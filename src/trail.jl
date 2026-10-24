# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

const _Exact = Rational{BigInt}
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
    bucket::Int8 # 0 for dominance queue, 1..4 for degree-(bucket-1) elim_queues, -1 for rel_queue
end
_UndoQueue(serial::UInt64, fix_depth::Int, index::Int, head::Int, queued::Bool) =
    _UndoQueue(serial, fix_depth, index, head, queued, Int8(0))
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
    rel_queue::Vector{Int}
    rel_queued::BitVector
    rel_head::Int
end
