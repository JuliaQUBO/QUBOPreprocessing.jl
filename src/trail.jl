# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

const _Exact = Rational{BigInt}
abstract type _ProofRecord end
const _NeighborRecord = Tuple{Int,_Exact,_Exact,_Exact}

_reserve!(a::Vector, sz::Int) = @static VERSION >= v"1.11.0-DEV" ? sizehint!(a, sz; shrink=false) : sizehint!(a, sz)

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
end

struct _UndoQueue
    serial::UInt64
    fix_depth::Int
    index::Int
    head::Int
    queued::Bool
end
const _UndoEntry = Union{_UndoFix,_UndoQueue}

# Adjacency is fixed for this conditioning-only slice. Future topology-changing
# reductions must introduce their own trailed edge/reconstruction records here;
# mutating adjacency without such records is unsupported.
mutable struct _Incremental
    labels::Dict{Any,Int}
    adjacency::Vector{Vector{Pair{Int,_Exact}}}
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
    total_candidates::Int
    total_edges::Int
    total_exact::Int
    dual_fields::Vector{_Exact}
    dual_constant::_Exact
    degrees::Vector{Int}
end
