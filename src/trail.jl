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
    isfinite(v) || return _Exact(v)
    m, e = _dyadic_parts(v)
    # m is odd unless it is zero, so these numerator/denominator pairs are
    # already normalized. BigInt shifts preserve subnormals and large integers.
    num = e >= 0 ? BigInt(m) << e : BigInt(m)
    den = e >= 0 ? BigInt(1) : BigInt(1) << -e
    return Base.unsafe_rational(BigInt, num, den)
end
@inline _to_exact(v::Integer)::_Exact = Base.unsafe_rational(BigInt, BigInt(v), BigInt(1))
@inline _to_exact(v::_Exact)::_Exact = v

# Exact normalized q / 2^shift for the bounded constructor accumulators. No
# gcd is needed because the only possible common factors are powers of two.
@inline function _from_dyadic_integer(q::Int128, shift::Int)::_Exact
    iszero(q) && return _to_exact(0)
    common = min(trailing_zeros(q), shift)
    return Base.unsafe_rational(BigInt, BigInt(q >> common), BigInt(1) << (shift - common))
end

@inline function _dyadic_integer(v::Float64, shift::Int)::Int128
    m, e = _dyadic_parts(v)
    return Int128(m) << (e + shift)
end

abstract type _ProofRecord end
const _NeighborRecord = Tuple{Int,_Exact,_Exact,_Exact}
const _DualDegreeRecord = Tuple{Int,_Exact,Int}
const _AdjacencyEdit = Tuple{Symbol,Int,Int,Pair{Int,_Exact}}

_reserve!(a::Vector, sz::Int) = @static VERSION >= v"1.11.0-DEV" ? sizehint!(a, sz; shrink=false) : sizehint!(a, nextpow(2, max(16, sz)))

struct _UndoFix
    serial::UInt64
    fix_depth::Int
    index::Int
    value::Int
    constant::_Exact
    fields::Vector{_NeighborRecord}
    queue_length::Int
    proof::Union{Nothing,_ProofRecord}
    dual_constant::_Exact
    dual_fields::Vector{Pair{Int,_Exact}}
    elim_queue_lengths::NTuple{4,Int}
    rel_queue_length::Int
end

struct _UndoReduction
    serial::UInt64
    fix_depth::Int
    index::Int
    status::Int8
    constant::_Exact
    dual_constant::_Exact
    fields::Vector{_NeighborRecord}
    dual_fields::Vector{_DualDegreeRecord}
    adj_edits::Vector{_AdjacencyEdit}
    queue_length::Int
    proof::_ProofRecord
    spin_const_delta::_Exact
    spin_field_deltas::Vector{Pair{Int,_Exact}}
    spin_coupling_deltas::Vector{Tuple{Int,Int,_Exact}}
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
const _UndoEntry = Union{_UndoFix,_UndoReduction,_UndoQueue}

# Topology-changing reductions (relation contractions and bounded local
# eliminations) trail their exact field, degree and adjacency edits in
# `_UndoReduction`. In `fixed`, `2` denotes free, `-1/0/1` constant-fixed,
# `3` relation-contracted and `4` locally eliminated.
mutable struct _Incremental
    labels::Dict{Any,Int}
    adjacency::Vector{Vector{Pair{Int,_Exact}}}
    adj_pos::Vector{Dict{Int,Int}}
    fields::Vector{_Exact}
    constant::_Exact
    fixed::Vector{Int8} # 2 denotes free in either source domain
    queue::Vector{Int}
    queued::BitVector
    trail::Vector{_UndoEntry}
    serial::UInt64
    epoch::UUID
    rules::Symbol
    lower::Union{Nothing,Vector{_Exact}}
    upper::Union{Nothing,Vector{_Exact}}
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
    dual_fields::Vector{_Exact}
    dual_constant::_Exact
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
