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

# Each construction/replay or workspace owns its cache. Rational arithmetic
# treats these powers as read-only; never use one as a mutable GMP destination.
# Public coefficient queries/export copy them. Grid extension grows the cache
# lazily, geometrically, without replacing or modifying existing powers.
@inline function _dyadic_denominator!(denominators::_DyadicDenominators, shift::Int)::BigInt
    if shift >= length(denominators)
        previous = length(denominators)
        resize!(denominators, max(shift + 1, 2previous))
        for i in previous+1:length(denominators)
            denominators[i] = nothing
        end
    end
    den = denominators[shift + 1]
    if den === nothing
        den = shift == 0 ? BigInt(1) : BigInt(1) << shift
        denominators[shift + 1] = den
    end
    return den
end

# Inputs are already normalized: den_shift is nonnegative and num is odd
# when den_shift is positive (or num == 0 with den_shift == 0).
@inline function _from_normalized_dyadic(num::Int128, den_shift::Int, denominators::_DyadicDenominators)::_Exact
    return Base.unsafe_rational(BigInt, BigInt(num), _dyadic_denominator!(denominators, den_shift))
end

@inline function _from_dyadic_integer(q::Int128, shift::Int, denominators::_DyadicDenominators)::_Exact
    common = iszero(q) ? shift : min(trailing_zeros(q), shift)
    return _from_normalized_dyadic(q >> common, shift - common, denominators)
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
    denominators::_DyadicDenominators
    physical_constants::Vector{Union{Nothing,_Exact}}
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

# The 31 workspace-owned cells use canonical num/2^den_shift keys: integers
# -7:7, then odd numerators -7:2:7 at den_shift 1 and 2. Both BigInts remain
# read-only. Physical keys survive grid changes, numeric replacement and undo.
@inline function _physical_constant!(st::_Incremental, index::Int, num::Int128, den_shift::Int)::_Exact
    value = st.physical_constants[index]
    if value === nothing
        value = _from_normalized_dyadic(num, den_shift, st.denominators)
        st.physical_constants[index] = value
    end
    return value
end

# Exact coordinate views use an explicit nonnegative grid exponent without
# changing the live payload. Returned numerators and denominators are read-only.
@inline function _physical_at_shift(st::_Incremental, q::Int128, shift::Int)
    shift >= 0 || throw(ArgumentError("dyadic exponent must be nonnegative"))
    iszero(q) && return _physical_constant!(st, 8, Int128(0), 0)
    common = min(trailing_zeros(q), shift)
    num = q >> common
    den_shift = shift - common
    # Normalize without abs/negation or forming a sign-bit unit. Compare the
    # Int128 numerator before narrowing it, including at typemin(Int128).
    if den_shift <= 2 && -7 <= num <= 7
        n = Int(num)
        index = den_shift == 0 ? n + 8 : 15 + 8*(den_shift - 1) + (n + 9) ÷ 2
        return _physical_constant!(st, index, num, den_shift)
    end
    return _from_normalized_dyadic(num, den_shift, st.denominators)
end
@inline function _physical_at_shift(st::_Incremental, q::Integer, shift::Int)
    shift >= 0 || throw(ArgumentError("dyadic exponent must be nonnegative"))
    return _from_dyadic_integer(q, shift)
end
@inline _physical(st::_Incremental, q::Int128) = _physical_at_shift(st, q, st.shift)
@inline _physical(st::_Incremental, q::Integer) = _from_dyadic_integer(q, st.shift)
@inline _physical(st::_Incremental, q::_Exact) = q
@inline _physical(q::Integer, shift::Int) = _from_dyadic_integer(q, shift)

@inline function _physical_times_four(st::_Incremental, q::Int128)
    shift = st.shift
    shift >= 2 && return _physical_at_shift(st, q, shift - 2)
    # The live grid is nonnegative. At shifts zero and one, multiply only after
    # checking bounds; never negate/abs typemin or overflow an intermediate.
    factor = shift == 0 ? Int128(4) : shift == 1 ? Int128(2) :
        throw(ArgumentError("dyadic exponent must be nonnegative"))
    if typemin(Int128) ÷ factor <= q <= typemax(Int128) ÷ factor
        return _physical_at_shift(st, q * factor, 0)
    end
    return _from_dyadic_integer(BigInt(q) * factor, 0)
end
@inline function _physical_times_four(st::_Incremental, q::Integer)
    shift = st.shift
    shift >= 2 && return _physical_at_shift(st, q, shift - 2)
    shift >= 0 || throw(ArgumentError("dyadic exponent must be nonnegative"))
    return _from_dyadic_integer(BigInt(q) << (2 - shift), 0)
end

# Float-only consumers can avoid constructing a rational when the normalized
# dyadic is exactly representable as a normal binary64. Keep the old conversion
# for low BigFloat precision, where Rational{BigInt} conversion can round first,
# and for near/subnormal results, which can depend on the caller's FTZ setting.
@inline function _physical_float(st::_Incremental, q::Int128)
    iszero(q) && return 0.0
    shift = st.shift
    common = min(trailing_zeros(q), shift)
    num = q >> common
    den_shift = shift - common
    if 0 <= den_shift <= 1021 && -(Int128(1) << 53) <= num <= (Int128(1) << 53) &&
       precision(BigFloat) >= 53
        return ldexp(Float64(Int64(num)), -den_shift)
    end
    return Float64(_physical(st, q))
end
@inline _physical_float(st::_Incremental, q::Integer) = Float64(_physical(st, q))
@inline _physical_float(st::_Incremental, q::_Exact) = Float64(q)

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
# Count magnitude bits without converting the Int128 bounds to BigInt.
_grid_fits(v::BigInt) = ndigits(v; base=2) <= 123
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

# Enclose numerator/2^shift on the normal fast path without a Rational or
# ambient BigFloat precision. Keep at most 53 leading bits; the discarded
# positive tail is below the next normal ulp. Near/subnormal results use
# the checked rational enclosure to handle FTZ.
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
    value < floatmin(Float64) && return _enclose(_physical(st, q))
    if isfinite(value) && (n >> cut) << cut == n && trailing_zeros(n) >= st.shift - 1074
        return negative ? (-value, -value) : (value, value)
    end
    lo = iszero(value) ? 0.0 : prevfloat(value)
    hi = nextfloat(value)
    return negative ? (-hi, -lo) : (lo, hi)
end
