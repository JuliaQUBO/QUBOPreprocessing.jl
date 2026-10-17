# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

const _Exact = Rational{BigInt}

struct _UndoFix
    serial::UInt64
    index::Int
    value::Int
    constant::_Exact
    fields::Vector{Pair{Int,_Exact}}
    queue_length::Int
end

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
    trail::Vector{_UndoFix}
    serial::UInt64
    epoch::UUID
end
