# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

const _Exact = Rational{BigInt}

# A finite nonzero binary64 value is m * 2^e, with odd signed m. Reading the
# representation avoids the general Float64-to-rational normalization path.
@inline function _dyadic_parts(v::Float64)
    bits = reinterpret(UInt64, v)
    exponent = Int((bits >> 52) & 0x7ff)
    mantissa = bits & 0x000fffffffffffff
    exponent == 0 || (mantissa |= 0x0010000000000000)
    iszero(mantissa) && return (Int64(0), 0)
    shift = trailing_zeros(mantissa)
    m = Int64(mantissa >> shift)
    signbit(v) && (m = -m)
    e = (exponent == 0 ? -1074 : exponent - 1075) + shift
    return m, e
end

@inline function _to_exact(v::Float64)::_Exact
    if v == trunc(v) && -9007199254740992.0 <= v <= 9007199254740992.0
        return Base.unsafe_rational(BigInt, BigInt(Int64(v)), BigInt(1))
    end
    isfinite(v) || return _Exact(v)
    m, e = _dyadic_parts(v)
    # m is odd unless it is zero, so these numerator/denominator pairs are
    # already normalized. BigInt shifts preserve subnormals and large integers.
    num = e > 0 ? BigInt(m) << e : BigInt(m)
    den = e >= 0 ? BigInt(1) : BigInt(1) << -e
    return Base.unsafe_rational(BigInt, num, den)
end
@inline _to_exact(v::Integer)::_Exact = Base.unsafe_rational(BigInt, BigInt(v), BigInt(1))
@inline _to_exact(v::_Exact)::_Exact = v

# Exact normalized q / 2^shift for the bounded constructor accumulators. No
# gcd is needed because the only possible common factors are powers of two.
@inline function _from_dyadic_integer(q::Integer, shift::Int)::_Exact
    iszero(q) && return _to_exact(0)
    common = min(trailing_zeros(q), shift)
    return Base.unsafe_rational(BigInt, BigInt(q >> common), BigInt(1) << (shift - common))
end

const _DyadicDenominators = Vector{Union{Nothing,BigInt}}
_dyadic_denominators(shift::Int) =
    fill!(Vector{Union{Nothing,BigInt}}(undef, shift + 3), nothing)

# This cache is local to one construction/replay. Rational arithmetic treats
# its input BigInts as read-only; never pass a cached denominator as the mutable
# destination of a GMP operation. Public coefficient queries/export copy them.
@inline function _dyadic_denominator!(denominators::_DyadicDenominators, shift::Int)::BigInt
    den = denominators[shift + 1]
    if den === nothing
        den = shift == 0 ? BigInt(1) : BigInt(1) << shift
        denominators[shift + 1] = den
    end
    return den
end

@inline function _from_dyadic_integer(q::Int128, shift::Int, denominators::_DyadicDenominators)::_Exact
    common = iszero(q) ? shift : min(trailing_zeros(q), shift)
    den = _dyadic_denominator!(denominators, shift - common)
    return Base.unsafe_rational(BigInt, BigInt(q >> common), den)
end

@inline function _dyadic_integer(v::Float64, shift::Int)::Int128
    if shift == 0 && -9007199254740992.0 <= v <= 9007199254740992.0
        return Int128(Int64(v))
    end
    m, e = _dyadic_parts(v)
    return Int128(m) << (e + shift)
end

abstract type _ProofRecord end
const _NeighborRecord{I} = Tuple{Int,I,I,I}
const _DualDegreeRecord{I} = Tuple{Int,I,Int}
const _AdjacencyEdit{I} = Tuple{Symbol,Int,Int,Pair{Int,I}}

_reserve!(a::Vector, sz::Int) = @static VERSION >= v"1.11.0-DEV" ? sizehint!(a, sz; shrink=false) : sizehint!(a, nextpow(2, max(16, sz)))

struct _UndoFix{I<:Integer}
    serial::UInt64
    fix_depth::Int
    index::Int
    value::Int
    constant::I
    fields::Vector{_NeighborRecord{I}}
    queue_length::Int
    proof::Union{Nothing,_ProofRecord}
    dual_constant::I
    dual_fields::Vector{Pair{Int,I}}
    elim_queue_lengths::NTuple{4,Int}
    rel_queue_length::Int
end

struct _UndoReduction{I<:Integer}
    serial::UInt64
    fix_depth::Int
    index::Int
    status::Int8
    constant::I
    dual_constant::I
    fields::Vector{_NeighborRecord{I}}
    dual_fields::Vector{_DualDegreeRecord{I}}
    adj_edits::Vector{_AdjacencyEdit{I}}
    queue_length::Int
    proof::_ProofRecord
    spin_const_delta::I
    spin_field_deltas::Vector{Pair{Int,I}}
    spin_coupling_deltas::Vector{Tuple{Int,Int,I}}
    elim_queue_lengths::NTuple{4,Int}
    rel_queue_length::Int
end

struct _UndoQueue
    serial::UInt64
    fix_depth::Int
    index::Int
    head::Int
    queued::Bool
    bucket::Int8 # 0 for dominance queue, 1..4 for elim_queues pop, 5..8 for elim_queues requeue, -1 for rel_queue pop, -2 for rel_queue requeue
    blocked_fill::Int
    checked_weak::Bool
end
_UndoQueue(serial::UInt64, fix_depth::Int, index::Int, head::Int, queued::Bool, bucket::Int8=Int8(0)) =
    _UndoQueue(serial, fix_depth, index, head, queued, bucket, typemax(Int), false)
const _UndoEntry{I} = Union{_UndoFix{I},_UndoReduction{I},_UndoQueue}

mutable struct _IntegerState{I<:Integer}
    adjacency::Vector{Vector{Pair{Int,I}}}
    fields::Vector{I}
    constant::I
    lower::Union{Nothing,Vector{I}}
    upper::Union{Nothing,Vector{I}}
    dual_fields::Vector{I}
    dual_constant::I
    trail::Vector{_UndoEntry{I}}
    shift::Int
    promotions::Int
    extensions::Int
end

# Topology-changing reductions (relation contractions and bounded local
# eliminations) trail their exact field, degree and adjacency edits in
# `_UndoReduction`. In `fixed`, `2` denotes free, `-1/0/1` constant-fixed,
# `3` relation-contracted and `4` locally eliminated.
mutable struct _Incremental
    numeric::Union{_IntegerState{Int128},_IntegerState{BigInt}}
    labels::Dict{Any,Int}
    adj_pos::Vector{Dict{Int,Int}}
    fixed::Vector{Int8} # 2 denotes free in either source domain
    queue::Vector{Int}
    queued::BitVector
    serial::UInt64
    epoch::UUID
    rules::Symbol
    head::Int
    fixes::Vector{Int}
    callers::Vector{Int}
    entries::Vector{Int}
    proof_count::Int
    first_proof_pos::Int
    marginal_count::Int
    total_candidates::Int
    total_edges::Int
    total_exact::Int
    degrees::Vector{Int}
    initial_degrees::Vector{Int}
    elim_queues::NTuple{4,Vector{Int}}
    elim_queued::NTuple{4,BitVector}
    elim_heads::Vector{Int}
    elim_blocked_fill::NTuple{4,Vector{Int}}
    rel_queue::Vector{Int}
    rel_queued::BitVector
    rel_head::Int
    rel_blocked_fill::Vector{Int}
    rel_checked_weak::BitVector
    elim_deferred::NTuple{4,Vector{Int}}
    rel_deferred::Vector{Int}
    rel_weak_deferred::Vector{Int}
    unweak_rel_count::Int
    active_edges::Int
    initial_edges::Int
    star_hint::Int
    rel_hint::Int
    # Caller requests that matched a certified unary deduction, as
    # (index, value, trail length when requested, id). They stay outside the
    # caller scope; `assume!` replays them as caller fixes when its structural
    # rollback undoes the deduction, and `rollback!` drops those made after its
    # checkpoint. Ids come from the monotone `pin_serial`; both ids and trail
    # lengths are nondecreasing along `pins`.
    pins::Vector{NTuple{4,Int}}
    pin_serial::Int
end

# The stable topology owner exposes the actual typed integer arrays. There is no
# rational array wrapper or per-edge mixed numeric type. Replacing one numeric
# payload atomically preserves references held by scheduling/rollback callers.
const _numeric_properties = (:adjacency, :fields, :constant, :lower, :upper,
    :dual_fields, :dual_constant, :trail, :shift, :promotions, :extensions)
@inline function Base.getproperty(st::_Incremental, name::Symbol)
    name in _numeric_properties && return getproperty(getfield(st, :numeric), name)
    return getfield(st, name)
end
@inline function Base.setproperty!(st::_Incremental, name::Symbol, value)
    name in _numeric_properties && return setproperty!(getfield(st, :numeric), name, value)
    return setfield!(st, name, value)
end
Base.propertynames(::_Incremental, private::Bool=false) =
    (fieldnames(_Incremental)..., _numeric_properties...)

@inline _physical(st::_Incremental, q::Integer) = _from_dyadic_integer(q, st.shift)
@inline _physical(st::_Incremental, q::_Exact) = q
@inline _physical(q::Integer, shift::Int) = _from_dyadic_integer(q, shift)

function _grid_shift(q::_Exact)
    d = denominator(q)
    ispow2(d) || throw(ArgumentError("integer workspace requires dyadic reduction coefficients"))
    return ndigits(d; base=2) - 1
end
_grid_numerator(q::_Exact, shift::Int) = numerator(q) << (shift - _grid_shift(q))

# Rescale every live and historical numeric value together. Proof objects and
# gauge cursor caches remain in physical units and are deliberately not rescaled.
function _regrid_undo(e::_UndoFix, cv)
    return _UndoFix(e.serial, e.fix_depth, e.index, e.value, cv(e.constant),
        [(j, cv(f), cv(lo), cv(hi)) for (j,f,lo,hi) in e.fields], e.queue_length,
        e.proof, cv(e.dual_constant), [j=>cv(v) for (j,v) in e.dual_fields],
        e.elim_queue_lengths, e.rel_queue_length)
end
function _regrid_undo(e::_UndoReduction, cv)
    return _UndoReduction(e.serial, e.fix_depth, e.index, e.status, cv(e.constant),
        cv(e.dual_constant), [(j,cv(f),cv(lo),cv(hi)) for (j,f,lo,hi) in e.fields],
        [(j,cv(f),d) for (j,f,d) in e.dual_fields],
        [(op,a,p,j=>cv(v)) for (op,a,p,(j,v)) in e.adj_edits], e.queue_length,
        e.proof, cv(e.spin_const_delta), [j=>cv(v) for (j,v) in e.spin_field_deltas],
        [(a,b,cv(v)) for (a,b,v) in e.spin_coupling_deltas],
        e.elim_queue_lengths, e.rel_queue_length)
end
_regrid_undo(e::_UndoQueue, cv) = e

function _regrid(st::_Incremental, ::Type{I}, shift::Int) where {I<:Integer}
    old = st.numeric
    shift >= old.shift || throw(ArgumentError("integer grid cannot lose precision"))
    cv(v) = I(BigInt(v) << (shift - old.shift))
    adjacency = [[j=>cv(v) for (j,v) in a] for a in old.adjacency]
    trail = _UndoEntry{I}[_regrid_undo(e, cv) for e in old.trail]
    return _IntegerState{I}(adjacency, cv.(old.fields), cv(old.constant),
        old.lower === nothing ? nothing : cv.(old.lower),
        old.upper === nothing ? nothing : cv.(old.upper), cv.(old.dual_fields),
        cv(old.dual_constant), trail, shift,
        old.promotions + (I === BigInt && eltype(old.fields) === Int128),
        old.extensions + (shift > old.shift))
end

# Allow headroom for sign changes, multiplication by four and local bound sums.
# Productive updates preflight all scratch results before changing the payload.
const _SMALL_GRID_LIMIT = Int128(1) << 123
_grid_fits(v::Integer) = -_SMALL_GRID_LIMIT < v < _SMALL_GRID_LIMIT
function _ensure_grid!(st::_Incremental, shift::Int)
    shift == st.shift && return nothing
    if eltype(st.fields) === Int128
        try
            replacement = _regrid(st, Int128, shift)
            _payload_fits(replacement) ||
                (replacement = _regrid(st, BigInt, shift))
            st.numeric = replacement
        catch err
            err isa InexactError || rethrow()
            st.numeric = _regrid(st, BigInt, shift)
        end
    else
        st.numeric = _regrid(st, BigInt, shift)
    end
    return nothing
end

function _payload_fits(p::_IntegerState)
    all(_grid_fits, (p.constant, p.dual_constant)) || return false
    for values in (p.fields, p.dual_fields, p.lower, p.upper)
        values === nothing || all(_grid_fits, values) || return false
    end
    all(a -> all(e -> _grid_fits(e.second), a), p.adjacency) || return false
    for e in p.trail
        e isa _UndoQueue && continue
        all(_grid_fits, (e.constant, e.dual_constant)) || return false
        all(t -> all(_grid_fits, t[2:4]), e.fields) || return false
        if e isa _UndoFix
            all(t -> _grid_fits(t.second), e.dual_fields) || return false
        else
            all(t -> _grid_fits(t[2]), e.dual_fields) || return false
            all(t -> _grid_fits(t[4].second), e.adj_edits) || return false
            _grid_fits(e.spin_const_delta) || return false
            all(t -> _grid_fits(t.second), e.spin_field_deltas) || return false
            all(t -> _grid_fits(t[3]), e.spin_coupling_deltas) || return false
        end
    end
    return true
end

# Enclose numerator/2^shift without creating a Rational or depending on ambient
# BigFloat precision. Keep at most 53 leading bits; the discarded positive tail
# is below the next normal ulp. Outward neighbors also cover subnormal rounding.
function _enclose_grid(st::_Incremental, q::Integer)
    iszero(q) && return (0.0, 0.0)
    negative = q < 0
    n = if q isa Int128
        u = reinterpret(UInt128, q)
        negative ? zero(UInt128) - u : u
    else
        abs(q)
    end
    cut = max(0, ndigits(n; base=2) - 53)
    top = UInt64(n >> cut)
    value = ldexp(Float64(top), cut - st.shift)
    if isfinite(value) && (n >> cut) << cut == n && trailing_zeros(n) >= st.shift - 1074
        return negative ? (-value, -value) : (value, value)
    end
    lo = iszero(value) ? 0.0 : prevfloat(value)
    hi = nextfloat(value)
    return negative ? (-hi, -lo) : (lo, hi)
end
