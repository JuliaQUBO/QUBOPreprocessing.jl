# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

function _label_index_dict(@nospecialize(labels::Tuple))
    n = length(labels)
    d = Dict{Any,Int}()
    sizehint!(d, n)
    for i in 1:n
        d[labels[i]] = i
    end
    return d
end

function _is_quadratic_deg3(
    is_bool::Bool,
    fields::Vector{I},
    dual_fields::Vector{I},
    adjacency::Vector{Vector{Pair{Int,I}}},
    fixed::Union{Nothing,Vector{Int8}},
    u::Int,
) where {I<:Integer}
    h_u = is_bool ? 4 * dual_fields[u] : fields[u]
    iszero(h_u) && return true
    abs_h = abs(h_u)
    sum_J = zero(I)
    max_J = zero(I)
    cnt = 0
    for (w, q) in adjacency[u]
        ((fixed === nothing || fixed[w] == 2) && !iszero(q)) || continue
        cnt += 1
        cnt > 3 && return false
        aJ = abs(q)
        sum_J += aJ
        aJ > max_J && (max_J = aJ)
    end
    cnt == 3 || return false
    return abs_h >= sum_J || 2 * max_J >= abs_h + sum_J
end

_is_quadratic_deg3(ws::Workspace, u::Int) = _is_quadratic_deg3(
    ws._snapshot.domain === QT.BoolDomain,
    ws._state.fields,
    ws._state.dual_fields,
    ws._state.adjacency,
    ws._state.fixed,
    u,
)

function _may_be_quadratic_deg3_fast(ws::Workspace, u::Int)
    st = ws._state
    st.degrees[u] == 3 || return false
    return iszero(ws._snapshot.domain === QT.BoolDomain ? st.dual_fields[u] : st.fields[u]) ||
        _is_quadratic_deg3(ws, u)
end

mutable struct _DyadicConstructionRange
    min_exponent::Int
    max_top::Int
    terms::UInt128
    timed_out::Bool
end

@inline function _observe_dyadic!(range::_DyadicConstructionRange, v::Float64)
    iszero(v) && return nothing
    m, e = _dyadic_parts(v)
    range.min_exponent = min(range.min_exponent, e)
    range.max_top = max(range.max_top, e + (64 - leading_zeros(UInt64(abs(m)))))
    range.terms += UInt128(1)
    return nothing
end

# Preflight before accumulating: with D=2^shift, every numerator is smaller in
# magnitude than 2^bits. The bound reserves a factor of two for dual-coordinate
# formulas and covers every global/per-vertex sum, including cancellation.
# The offset is added separately in arbitrary precision and needs no bound.
# Unsafe exponent spreads use the existing arbitrary-precision rational path.
function _dyadic_construction_plan(s::_Snapshot; deadline=nothing)
    _expired(deadline) && return nothing
    range = _DyadicConstructionRange(0, typemin(Int), UInt128(0), false)
    degrees = zeros(Int, length(s.labels))
    _foreach_linear_term(s.linear) do _, v
        if range.timed_out || _expired(deadline)
            range.timed_out = true
            return nothing
        end
        _observe_dyadic!(range, v)
    end
    range.timed_out && return nothing
    _foreach_quadratic_term(s.quadratic) do i, j, v
        if range.timed_out || _expired(deadline)
            range.timed_out = true
            return nothing
        end
        iszero(v) && return nothing
        degrees[i] += 1
        degrees[j] += 1
        _observe_dyadic!(range, v)
        return nothing
    end
    (range.timed_out || _expired(deadline)) && return nothing
    shift = -range.min_exponent
    if !iszero(range.terms)
        sum_bits = 128 - leading_zeros(range.terms - UInt128(1))
        range.max_top + shift + sum_bits <= 126 || (shift = -1)
    end
    return (; shift, degrees)
end

function _incremental(s::_Snapshot; rules=:identity)
    range = _DyadicConstructionRange(0, typemin(Int), UInt128(0), false)
    degrees = zeros(Int, length(s.labels))
    _observe_dyadic!(range, s.offset)
    _foreach_linear_term(s.linear) do _, v
        _observe_dyadic!(range, v)
    end
    _foreach_quadratic_term(s.quadratic) do i, j, v
        iszero(v) && return nothing
        degrees[i] += 1
        degrees[j] += 1
        _observe_dyadic!(range, v)
    end
    # Boolean dual spin fields/constants need quarters on the input grid.
    shift = -range.min_exponent + (s.domain === QT.BoolDomain ? 2 : 0)
    sum_bits = iszero(range.terms) ? 0 : 128 - leading_zeros(range.terms - UInt128(1))
    bounded = iszero(range.terms) || range.max_top + shift + sum_bits + 3 <= 123
    return _incremental_integer(s, rules, degrees, shift, bounded ? Int128 : BigInt)
end

function _incremental_integer(s::_Snapshot, rules::Symbol, degrees::Vector{Int},
                              shift::Int, ::Type{I}) where {I<:Integer}
    n = length(s.labels)
    cv(v) = if I === Int128
        _dyadic_integer(v, shift)
    else
        m, e = _dyadic_parts(v)
        BigInt(m) << (e + shift)
    end
    fields = zeros(I, n)
    _foreach_linear_term(s.linear) do i, v
        fields[i] = cv(v)
    end
    adjacency = [Vector{Pair{Int,I}}(undef, degrees[i]) for i in 1:n]
    adj_pos = [Dict{Int,Int}() for _ in 1:n]
    cursors = ones(Int, n)
    csum = zeros(I, n)
    neg = zeros(I, n)
    pos = zeros(I, n)
    quad_sum = Ref(zero(I))
    _foreach_quadratic_term(s.quadratic) do i, j, v
        iszero(v) && return nothing
        q = cv(v)
        for (a,b) in ((i,j),(j,i))
            k = cursors[a]
            adjacency[a][k] = b=>q
            adj_pos[a][b] = k
            cursors[a] = k + 1
            csum[a] += q
            if q < 0
                neg[a] += q
            else
                pos[a] += q
            end
        end
        quad_sum[] += q
    end
    is_bool = s.domain === QT.BoolDomain
    constant = cv(s.offset)
    dual_fields = [is_bool ? div(2*fields[i] + csum[i], 4) :
                              2*fields[i] - 2*csum[i] for i in 1:n]
    total_field = sum(fields; init=zero(I))
    dual_constant = is_bool ? constant + div(2*total_field + quad_sum[], 4) :
                              constant - total_field + quad_sum[]
    need_bounds = rules in (:dominance, :elimination, :relations, :mixed)
    lower = need_bounds ? [is_bool ? fields[i]+neg[i] : fields[i]-pos[i]+neg[i] for i in 1:n] : nothing
    upper = need_bounds ? [is_bool ? fields[i]+pos[i] : fields[i]+pos[i]-neg[i] for i in 1:n] : nothing
    queue = need_bounds ? collect(1:n) : Int[]
    queued = need_bounds ? trues(n) : falses(n)
    is_quad_deg3(i) = _is_quadratic_deg3(is_bool, fields, dual_fields, adjacency, nothing, i)
    elim_queues = ntuple(b -> Int[i for i in 1:n if degrees[i] == b-1 && (b<4 || is_quad_deg3(i))], 4)
    elim_queued = ntuple(_ -> falses(n), 4)
    for b in 1:4, i in elim_queues[b]
        elim_queued[b][i] = true
    end
    rel_queue = Int[i for i in 1:n if degrees[i] >= 1]
    rel_queued = BitVector(degrees[i] >= 1 for i in 1:n)
    m_init = sum(degrees; init=0) ÷ 2
    numeric = _IntegerState{I}(adjacency, fields, constant, lower, upper,
        dual_fields, dual_constant, _UndoEntry{I}[], shift, 0, 0)
    return _Incremental(numeric, _dyadic_denominators(shift),
        fill!(Vector{Union{Nothing,_Exact}}(undef,31),nothing), _label_index_dict(s.labels), adj_pos,
        fill(Int8(2), n), queue, queued, 0, uuid4(), rules, 1,
        Int[], Int[], zeros(Int,n), 0, 0, 0, 0, 0, 0,
        degrees, copy(degrees), elim_queues, elim_queued, [1,1,1,1],
        ntuple(_ -> fill(typemax(Int), n),4), rel_queue, rel_queued, 1,
        fill(typemax(Int),n), trues(n), (Int[],Int[],Int[],Int[]), Int[],Int[],0,
        m_init,m_init,1,1,NTuple{4,Int}[],0)
end

"""
    Checkpoint

Opaque workspace/source/branch-specific position in the conditioning trail.
An ancestor remains valid after rollback; discarded descendants cannot become
valid again after a new branch reaches the same depth. Reset and non-LIFO unfix
invalidate checkpoints. Private fields are not a construction/mutation API.
"""
struct Checkpoint
    _generation::Generation
    _epoch::UUID
    _depth::Int
    _serial::UInt64
    _fix_depth::Int
    _pin::Int
end

"""`checkpoint(ws)` captures a constant-size position without copying the model."""
function checkpoint(ws::Workspace)
    t = ws._state.trail
    return _checkpoint_at(ws,length(t))
end

function _checkpoint_at(ws::Workspace,depth::Int)
    st = ws._state
    t = st.trail
    # Record the latest active pin requested while the trail was at most `depth` long.
    pin = 0
    for p in st.pins
        p[3] <= depth || break
        pin = p[4]
    end
    return Checkpoint(generation(ws),st.epoch,depth,depth == 0 ? 0 : t[depth].serial,
                      depth == 0 ? 0 : t[depth].fix_depth,pin)
end

function _validate_checkpoint(ws::Workspace, cp::Checkpoint)
    st = ws._state
    t = st.trail
    cp._generation == generation(ws) && cp._epoch == st.epoch &&
        0 <= cp._depth <= length(t) &&
        (cp._depth == 0 ? cp._serial == 0 && cp._fix_depth == 0 :
            t[cp._depth].serial == cp._serial && t[cp._depth].fix_depth == cp._fix_depth) &&
        (cp._pin == 0 || any(p -> p[4] == cp._pin, st.pins)) ||
        throw(ArgumentError("checkpoint belongs to another workspace, generation or discarded branch"))
    return nothing
end

"""
    UpdateReport

An atomic caller update: `stop_reason` is `:applied`, `:unchanged`, `:work_limit`
or `:deadline`. `edge_visits` counts adjacency entries visited, and `changed`
counts caller assumptions added/removed. This is not an inference/proof report.
"""
struct UpdateReport
    stop_reason::Symbol
    edge_visits::Int
    changed::Int
end

function _limits(max_work, deadline_ns)
    max_work isa Integer && !(max_work isa Bool) && 0 <= max_work <= typemax(Int) ||
        throw(ArgumentError("max_work must be a nonnegative machine-sized integer"))
    deadline_ns === nothing || deadline_ns isa UInt64 ||
        throw(ArgumentError("deadline_ns must be nothing or an absolute time_ns() UInt64 deadline"))
end
_expired(deadline) = deadline !== nothing && time_ns() >= deadline

function _variable(ws::Workspace, label)
    i = get(ws._state.labels, label, 0)
    i != 0 || throw(ArgumentError("unknown original variable label"))
    return i
end

function _assignment(ws::Workspace, v)
    low = ws._snapshot.domain === QT.BoolDomain ? 0 : -1
    v isa Real && isfinite(v) && (v == low || v == 1) ||
        throw(ArgumentError("assumption is outside the original domain"))
    return Int(v)
end

"""
    assume!(ws, label, value; map=nothing, max_work=typemax(Int), deadline_ns=nothing)

Condition on one explicit original-label assignment, never a certified deduction.
When `map::DomainGaugeMap` is supplied, `value` is given in `map.target_domain`
and translated bijectively to the original domain. Repeat assignments are no-ops,
including a matching certified unary deduction; they do not promote deductions
into independent caller assumptions. Conflicts/invalid values throw before
mutation. If `label` was removed by a structural reduction (`RelationStep` or
`EliminationStep`) or a non-pointwise marginal weak step is active on the trail,
`assume!` never treats the removed variable as freely assignable on the reduced
residual; instead it rolls back the reduction suffix and replays retained caller
assumptions before imposing the new assumption. A request that previously
matched a deduction undone by that rollback is replayed too, as an explicit
caller assumption, so the conditioning the caller asked for is not dropped.
`rollback!` discards such requests made after its checkpoint, and `unfix!`
discards those whose deduction it removes.
"""
function assume!(ws::Workspace, label, value; map::Union{Nothing,DomainGaugeMap}=nothing,
                 max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws, label)
    v = if map === nothing
        _assignment(ws, value)
    else
        u_val = _check_domain_scalar(value, map.target_domain)
        _lift_index_value(map, i, u_val)
    end
    st = ws._state
    if st.fixed[i] in (-1, 0, 1)
        st.fixed[i] == v || throw(ArgumentError("conflicting caller assumption"))
        if st.trail[st.entries[i]].proof !== nothing && !any(p -> p[1] == i, st.pins)
            st.pin_serial += 1
            push!(st.pins, (i, v, length(st.trail), st.pin_serial))
        end
        return UpdateReport(:unchanged, 0, 0)
    end
    if st.fixed[i] != 2 || st.marginal_count > 0
        pos = st.first_proof_pos
        pos > 0 || throw(ArgumentError("inconsistent variable status"))
        c_idx = length(st.callers)
        while c_idx >= 1 && st.callers[c_idx] > pos
            c_idx -= 1
        end
        replay_start = c_idx + 1
        n_pins = length(st.pins)
        replay_count = length(st.callers) - c_idx + n_pins + 1
        replay_list = Vector{Pair{Int,Int}}(undef, replay_count)
        # Every pin matched a deduction at or after `pos`, so the rollback below
        # undoes it; merge retained callers after `pos` and pins by trail depth
        # so replayed assumptions stay in chronological application order.
        out_idx = 0
        p_idx = 1
        for k in replay_start:length(st.callers)
            c_pos = st.callers[k]
            while p_idx <= n_pins && st.pins[p_idx][3] < c_pos
                pin_i, pin_v, _, _ = st.pins[p_idx]
                replay_list[out_idx += 1] = pin_i => pin_v
                p_idx += 1
            end
            e = st.trail[c_pos]::_UndoFix
            replay_list[out_idx += 1] = e.index => e.value
        end
        while p_idx <= n_pins
            pin_i, pin_v, _, _ = st.pins[p_idx]
            replay_list[out_idx += 1] = pin_i => pin_v
            p_idx += 1
        end
        replay_list[replay_count] = i => v
        planned_visits = 0
        for (idx, _) in replay_list
            deg = st.initial_degrees[idx]
            deg <= max_work - planned_visits || return UpdateReport(:work_limit, 0, 0)
            for _ in 1:deg
                _expired(deadline_ns) && return UpdateReport(:deadline, planned_visits, 0)
                planned_visits += 1
            end
        end
        _expired(deadline_ns) && return UpdateReport(:deadline, planned_visits, 0)
        rollback!(ws, _checkpoint_at(ws, pos - 1))
        total_visits = 0
        for (idx, val) in replay_list
            rep = _fix!(ws, idx, val; max_work=typemax(Int), deadline_ns=nothing)
            total_visits += rep.edge_visits
        end
        return UpdateReport(:applied, total_visits, 1 + n_pins)
    end
    return _fix!(ws, i, v; max_work, deadline_ns)
end

function _fix!(ws::Workspace,i::Int,v::Int;proof=nothing,max_work=typemax(Int),deadline_ns=nothing)
    st = ws._state
    old_numeric = st.numeric
    result = try
        _fix_integer!(ws, st, st.numeric, i, v; proof, max_work, deadline_ns)
    catch err
        st.fixed[i] == 2 && (st.numeric = old_numeric)
        rethrow()
    end
    result.stop_reason === :applied || (st.numeric = old_numeric)
    return result
end

function _fix_integer!(ws::Workspace, st::_Incremental, numeric::_IntegerState{I}, i::Int, v::Int;
                       proof=nothing, max_work=typemax(Int), deadline_ns=nothing) where {I<:Integer}
    st.fixed[i] == 2 || throw(ArgumentError("fixing requires a free variable"))
    edges = numeric.adjacency[i]
    length(edges) <= max_work || return UpdateReport(:work_limit, 0, 0)
    _expired(deadline_ns) && return UpdateReport(:deadline, 0, 0)
    is_bool = ws._snapshot.domain === QT.BoolDomain
    dual_v = is_bool ? (2 * v - 1) : ((v + 1) ÷ 2)
    old = _NeighborRecord{I}[]
    updated = _NeighborRecord{BigInt}[]
    old_dual = Pair{Int,I}[]
    updated_dual = Pair{Int,BigInt}[]
    sizehint!(old, length(edges))
    sizehint!(updated, length(edges))
    sizehint!(old_dual, length(edges))
    sizehint!(updated_dual, length(edges))
    visits = 0
    for (j,q_raw) in edges
        q = BigInt(q_raw)
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits += 1
        st.fixed[j] == 2 || continue
        field = v == 0 ? numeric.fields[j] : (v == 1 ? (BigInt(numeric.fields[j]) + q) : (BigInt(numeric.fields[j]) - q))
        df_new = if dual_v == 0
            numeric.dual_fields[j]
        else
            dual_q = is_bool ? div(q, 4) : (4 * q)
            dual_v == 1 ? (BigInt(numeric.dual_fields[j]) + dual_q) : (BigInt(numeric.dual_fields[j]) - dual_q)
        end
        push!(old_dual, j => numeric.dual_fields[j])
        push!(updated_dual, j => df_new)
        if numeric.lower === nothing
            push!(old,(j,numeric.fields[j],numeric.fields[j],numeric.fields[j]))
            push!(updated,(j,field,field,field))
        else
            new_lo, new_hi = if is_bool
                if v == 0
                    q >= 0 ? (numeric.lower[j], BigInt(numeric.upper[j]) - q) : (BigInt(numeric.lower[j]) - q, numeric.upper[j])
                else
                    q >= 0 ? (BigInt(numeric.lower[j]) + q, numeric.upper[j]) : (numeric.lower[j], BigInt(numeric.upper[j]) + q)
                end
            else
                if (v == 1 && q >= 0) || (v == -1 && q <= 0)
                    (BigInt(numeric.lower[j]) + 2 * abs(q), numeric.upper[j])
                else
                    (numeric.lower[j], BigInt(numeric.upper[j]) - 2 * abs(q))
                end
            end
            push!(old,(j,numeric.fields[j],numeric.lower[j],numeric.upper[j]))
            push!(updated,(j,field,new_lo,new_hi))
        end
    end
    constant = v == 0 ? numeric.constant : (v == 1 ? (BigInt(numeric.constant) + BigInt(numeric.fields[i])) : (BigInt(numeric.constant) - BigInt(numeric.fields[i])))
    dual_constant = dual_v == 0 ? numeric.dual_constant : (dual_v == 1 ? (BigInt(numeric.dual_constant) + BigInt(numeric.dual_fields[i])) : (BigInt(numeric.dual_constant) - BigInt(numeric.dual_fields[i])))
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    if I === Int128 && (!all(_grid_fits, (constant, dual_constant)) ||
            !all(t -> all(_grid_fits, t[2:4]), updated) ||
            !all(p -> _grid_fits(p.second), updated_dual))
        st.numeric = _regrid(st, BigInt, numeric.shift)
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    end
    return _commit_integer_fix!(ws, st, st.numeric, i, v, proof, old, updated,
        old_dual, updated_dual, constant, dual_constant, visits)
end

# Promotion preserves the grid, so prepared scratch remains valid. Convert the
# saved undo values to the new payload type without repeating adjacency visits.
function _commit_integer_fix!(ws::Workspace, st::_Incremental, numeric::_IntegerState{I},
    i::Int, v::Int, proof, old, updated, old_dual, updated_dual,
    constant::Integer, dual_constant::Integer, visits::Int) where {I<:Integer}
    old = old isa Vector{_NeighborRecord{I}} ? old :
        _NeighborRecord{I}[(j,I(field),I(lo),I(hi)) for (j,field,lo,hi) in old]
    old_dual = old_dual isa Vector{Pair{Int,I}} ? old_dual :
        Pair{Int,I}[j=>I(value) for (j,value) in old_dual]
    constant_i, dual_constant_i = I(constant), I(dual_constant)
    updated_i = _NeighborRecord{I}[(j,I(field),I(lo),I(hi)) for (j,field,lo,hi) in updated]
    updated_dual_i = Pair{Int,I}[j=>I(value) for (j,value) in updated_dual]
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    # Complete allocation before committing field, queue and trail changes.
    _reserve!(st.queue, length(st.queue) + length(updated))
    for b in 1:4
        _reserve!(st.elim_queues[b], length(st.elim_queues[b]) + length(updated))
    end
    _reserve!(st.rel_queue, length(st.rel_queue) + length(updated))
    _reserve!(numeric.trail, length(numeric.trail) + 1)
    _reserve!(st.fixes, length(st.fixes) + 1)
    proof === nothing && _reserve!(st.callers, length(st.callers) + 1)
    elim_lens = ntuple(b -> length(st.elim_queues[b]), 4)
    entry = _UndoFix(st.serial + 1,length(st.fixes)+1,i,v,numeric.constant,old,length(st.queue),proof,numeric.dual_constant,old_dual,elim_lens,length(st.rel_queue))
    push!(numeric.trail, entry)
    push!(st.fixes,length(numeric.trail))
    if proof === nothing
        push!(st.callers,length(numeric.trail))
    else
        st.proof_count == 0 && (st.first_proof_pos = length(numeric.trail))
        st.proof_count += 1
        (proof isa ProbingStep || proof isa RoofDualityStep || proof isa SubmodularCutStep || proof isa MaxCutStep ||
         (hasproperty(proof, :method) && proof.method === :marginal)) &&
            (st.marginal_count += 1)
    end
    st.entries[i] = length(numeric.trail)
    st.serial += 1
    numeric.constant = constant_i
    numeric.dual_constant = dual_constant_i
    st.fixed[i] = v
    st.degrees[i] = 0
    st.active_edges -= length(updated_dual)
    for (j,field,lower,upper) in updated_i
        numeric.fields[j] = field
        if numeric.lower !== nothing
            numeric.lower[j],numeric.upper[j] = lower,upper
        end
        if !st.queued[j]
            push!(st.queue, j)
            st.queued[j] = true
        end
    end
    for (j, df) in updated_dual_i
        numeric.dual_fields[j] = df
        st.degrees[j] -= 1
        d_j = st.degrees[j]
        if d_j <= 3 && (d_j < 3 || _may_be_quadratic_deg3_fast(ws, j)) && !st.elim_queued[d_j + 1][j]
            push!(st.elim_queues[d_j + 1], j)
            st.elim_queued[d_j + 1][j] = true
        end
        d_j == 3 && _may_be_quadratic_deg3_fast(ws, j) && (st.star_hint = st.elim_heads[4])
        if d_j >= 1 && !st.rel_queued[j]
            push!(st.rel_queue, j)
            st.rel_queued[j] = true
        end
    end
    return UpdateReport(:applied, visits, 1)
end

function _adj_set!(adjacency, adj_pos, adj_edits::Vector{_AdjacencyEdit{I}}, a::Int, b::Int, q_new::I) where {I<:Integer}
    pos = get(adj_pos[a], b, 0)
    if pos == 0
        !iszero(q_new) || return nothing
        push!(adjacency[a], b => q_new)
        adj_pos[a][b] = length(adjacency[a])
        push!(adj_edits, (:pop, a, 0, b => zero(I)))
    else
        old_pair = adjacency[a][pos]
        if iszero(q_new)
            last_pos = length(adjacency[a])
            if pos != last_pos
                tail_pair = adjacency[a][last_pos]
                adjacency[a][pos] = tail_pair
                adj_pos[a][tail_pair.first] = pos
            end
            pop!(adjacency[a])
            delete!(adj_pos[a], b)
            push!(adj_edits, (:swap_remove, a, pos, old_pair))
        else
            adjacency[a][pos] = b => q_new
            push!(adj_edits, (:update, a, pos, old_pair))
        end
    end
    return nothing
end

function _touch!(touched::Vector{Int}, touched_seen::Set{Int}, w::Int)
    w in touched_seen && return nothing
    push!(touched_seen, w)
    push!(touched, w)
    return nothing
end

function _apply_reduction!(
    ws::Workspace,
    u::Int,
    status::Int8,
    proof::_ProofRecord,
    const_delta::_Exact,
    field_deltas::Vector{Pair{Int,_Exact}},
    quad_deltas::Vector{Tuple{Int,Int,_Exact}};
    max_work=typemax(Int),
    deadline_ns=nothing,
    precharged_visits::Int=0,
)
    st = ws._state
    st.fixed[u] == 2 || throw(ArgumentError("reduction requires a free variable"))
    shift = max(st.shift, _grid_shift(const_delta) + (ws._snapshot.domain === QT.BoolDomain ? 2 : 0))
    for (_, q) in field_deltas
        shift = max(shift, _grid_shift(q) + (ws._snapshot.domain === QT.BoolDomain ? 2 : 0))
    end
    for (_, _, q) in quad_deltas
        shift = max(shift, _grid_shift(q) + (ws._snapshot.domain === QT.BoolDomain ? 2 : 0))
    end
    old_numeric = st.numeric
    result = try
        _ensure_grid!(st, shift)
        _apply_integer_reduction!(ws, st, st.numeric, u, status, proof,
            _grid_numerator(const_delta, shift),
            [i=>_grid_numerator(q, shift) for (i,q) in field_deltas],
            [(i,j,_grid_numerator(q, shift)) for (i,j,q) in quad_deltas];
            max_work, deadline_ns, precharged_visits)
    catch err
        st.fixed[u] == 2 && (st.numeric = old_numeric)
        rethrow()
    end
    result.stop_reason === :applied || (st.numeric = old_numeric)
    return result
end

function _apply_integer_reduction!(ws::Workspace, st::_Incremental, numeric::_IntegerState{I},
    u::Int, status::Int8, proof::_ProofRecord, const_delta::BigInt,
    field_deltas::Vector{Pair{Int,BigInt}}, quad_deltas::Vector{Tuple{Int,Int,BigInt}};
    max_work=typemax(Int), deadline_ns=nothing, precharged_visits::Int=0) where {I<:Integer}
    st.fixed[u] == 2 || throw(ArgumentError("reduction requires a free variable"))
    is_bool = ws._snapshot.domain === QT.BoolDomain
    visits = precharged_visits
    u_free_edges = Pair{Int,BigInt}[]
    touched = Int[]
    touched_seen = Set{Int}()
    for (w, q) in numeric.adjacency[u]
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits < max_work || return UpdateReport(:work_limit, visits, 0)
        visits += 1
        if st.fixed[w] == 2
            push!(u_free_edges, w => q)
            _touch!(touched, touched_seen, w)
        end
    end
    for (w, df) in field_deltas
        iszero(df) && continue
        w != u && st.fixed[w] == 2 || throw(ArgumentError("field delta targets a non-free variable"))
        _touch!(touched, touched_seen, w)
    end
    merged_q = Dict{Tuple{Int,Int},BigInt}()
    merged_order = Tuple{Int,Int}[]
    for (a, b, dq) in quad_deltas
        iszero(dq) && continue
        a != b && a != u && b != u && st.fixed[a] == 2 && st.fixed[b] == 2 ||
            throw(ArgumentError("quadratic delta targets non-free or identical variables"))
        j, k = min(a, b), max(a, b)
        !haskey(merged_q, (j, k)) && push!(merged_order, (j, k))
        merged_q[(j, k)] = get(merged_q, (j, k), big(0)) + dq
        _touch!(touched, touched_seen, j)
        _touch!(touched, touched_seen, k)
    end
    merged_quad_deltas = Tuple{Int,Int,BigInt}[
        (j, k, merged_q[(j, k)]) for (j, k) in merged_order if !iszero(merged_q[(j, k)])
    ]
    for _ in merged_quad_deltas
        2 <= max_work - visits || return UpdateReport(:work_limit, visits, 0)
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits += 2
    end
    old_fields = Vector{_NeighborRecord{I}}(undef, length(touched))
    old_dual = Vector{_DualDegreeRecord{I}}(undef, length(touched) + 1)
    old_dual[1] = (u, numeric.dual_fields[u], st.degrees[u])
    for (idx, w) in enumerate(touched)
        lo_w = numeric.lower === nothing ? numeric.fields[w] : numeric.lower[w]
        hi_w = numeric.upper === nothing ? numeric.fields[w] : numeric.upper[w]
        old_fields[idx] = (w, numeric.fields[w], lo_w, hi_w)
        old_dual[idx + 1] = (w, numeric.dual_fields[w], st.degrees[w])
    end
    f_map = Dict{Int,BigInt}(w => big(0) for w in touched)
    lo_map = Dict{Int,BigInt}(w => big(0) for w in touched)
    hi_map = Dict{Int,BigInt}(w => big(0) for w in touched)
    qsum_map = Dict{Int,BigInt}(w => big(0) for w in touched)
    deg_map = Dict{Int,Int}(w => 0 for w in touched)
    grow_map = Dict{Int,Int}(w => 0 for w in touched)
    for (w, q_uw) in u_free_edges
        deg_map[w] -= 1
        qsum_map[w] -= q_uw
        lo_map[w] -= is_bool ? min(0, q_uw) : -abs(q_uw)
        hi_map[w] -= is_bool ? max(0, q_uw) : abs(q_uw)
    end
    for (w, df) in field_deltas
        iszero(df) && continue
        f_map[w] += df
        lo_map[w] += df
        hi_map[w] += df
    end
    for (j, k, dq) in merged_quad_deltas
        pos_j = get(st.adj_pos[j], k, 0)
        q_old = pos_j == 0 ? big(0) : numeric.adjacency[j][pos_j].second
        q_new = q_old + dq
        if pos_j == 0
            deg_map[j] += 1
            deg_map[k] += 1
            grow_map[j] += 1
            grow_map[k] += 1
        elseif iszero(q_new)
            deg_map[j] -= 1
            deg_map[k] -= 1
        end
        qsum_map[j] += dq
        qsum_map[k] += dq
        d_lo = (is_bool ? min(0, q_new) : -abs(q_new)) - (is_bool ? min(0, q_old) : -abs(q_old))
        d_hi = (is_bool ? max(0, q_new) : abs(q_new)) - (is_bool ? max(0, q_old) : abs(q_old))
        lo_map[j] += d_lo
        lo_map[k] += d_lo
        hi_map[j] += d_hi
        hi_map[k] += d_hi
    end
    old_f_u = BigInt(numeric.fields[u])
    old_h_u = BigInt(is_bool ? numeric.dual_fields[u] : numeric.fields[u])
    total_f_delta = -old_f_u + sum(values(f_map); init=big(0))
    total_q_delta = -sum((q for (_, q) in u_free_edges); init=big(0)) +
                    sum((dq for (_, _, dq) in merged_quad_deltas); init=big(0))
    new_constant = BigInt(numeric.constant) + const_delta
    new_dual_constant = is_bool ?
        (BigInt(numeric.dual_constant) + const_delta + div(total_f_delta, 2) + div(total_q_delta, 4)) :
        (BigInt(numeric.dual_constant) + const_delta - total_f_delta + total_q_delta)
    spin_const_delta = is_bool ? (new_dual_constant - numeric.dual_constant) : const_delta
    spin_field_deltas = Pair{Int,BigInt}[u => -old_h_u]
    for w in touched
        dh_w = is_bool ? (div(f_map[w], 2) + div(qsum_map[w], 4)) : f_map[w]
        !iszero(dh_w) && push!(spin_field_deltas, w => dh_w)
    end
    spin_coupling_deltas = Tuple{Int,Int,BigInt}[]
    for (w, q_uw) in u_free_edges
        push!(spin_coupling_deltas, (min(u, w), max(u, w), -(is_bool ? div(q_uw, 4) : q_uw)))
    end
    for (j, k, dq) in merged_quad_deltas
        push!(spin_coupling_deltas, (j, k, (is_bool ? div(dq, 4) : dq)))
    end
    fits = all(_grid_fits, (new_constant, new_dual_constant, spin_const_delta))
    for w in touched
        fits &= _grid_fits(BigInt(numeric.fields[w]) + f_map[w])
        dual_delta = is_bool ? div(f_map[w],2) + div(qsum_map[w],4) : 2*f_map[w] - 2*qsum_map[w]
        fits &= _grid_fits(BigInt(numeric.dual_fields[w]) + dual_delta)
        if numeric.lower !== nothing
            fits &= _grid_fits(BigInt(numeric.lower[w]) + lo_map[w])
            fits &= _grid_fits(BigInt(numeric.upper[w]) + hi_map[w])
        end
    end
    fits &= all(p -> _grid_fits(p.second), spin_field_deltas)
    fits &= all(t -> _grid_fits(t[3]), spin_coupling_deltas)
    for (j,k,dq) in merged_quad_deltas
        pos = get(st.adj_pos[j], k, 0)
        fits &= _grid_fits((pos == 0 ? big(0) : BigInt(numeric.adjacency[j][pos].second)) + dq)
    end
    prepared = (; u_free_edges, touched, merged_quad_deltas, old_fields, old_dual,
        f_map, lo_map, hi_map, qsum_map, deg_map, grow_map, new_constant,
        new_dual_constant, spin_const_delta, spin_field_deltas, spin_coupling_deltas)
    if I === Int128 && !fits
        st.numeric = _regrid(st, BigInt, numeric.shift)
    end
    return _commit_integer_reduction!(ws, st, st.numeric, u, status, proof,
        prepared, visits; deadline_ns)
end

function _commit_integer_reduction!(ws::Workspace, st::_Incremental, numeric::_IntegerState{I},
    u::Int, status::Int8, proof::_ProofRecord, prepared::NamedTuple, visits::Int;
    deadline_ns=nothing) where {I<:Integer}
    (; u_free_edges, touched, merged_quad_deltas, old_fields, old_dual,
        f_map, lo_map, hi_map, qsum_map, deg_map, grow_map, new_constant,
        new_dual_constant, spin_const_delta, spin_field_deltas, spin_coupling_deltas) = prepared
    is_bool = ws._snapshot.domain === QT.BoolDomain
    old_fields = old_fields isa Vector{_NeighborRecord{I}} ? old_fields :
        _NeighborRecord{I}[(j,I(field),I(lo),I(hi)) for (j,field,lo,hi) in old_fields]
    old_dual = old_dual isa Vector{_DualDegreeRecord{I}} ? old_dual :
        _DualDegreeRecord{I}[(j,I(field),degree) for (j,field,degree) in old_dual]
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    _reserve!(st.queue, length(st.queue) + length(touched))
    for b in 1:4
        _reserve!(st.elim_queues[b], length(st.elim_queues[b]) + length(touched))
    end
    _reserve!(st.rel_queue, length(st.rel_queue) + length(touched))
    _reserve!(numeric.trail, length(numeric.trail) + 1)
    _reserve!(st.fixes, length(st.fixes) + 1)
    for w in touched
        grow_map[w] > 0 && _reserve!(numeric.adjacency[w], length(numeric.adjacency[w]) + grow_map[w])
    end
    constant_i, dual_constant_i = I(new_constant), I(new_dual_constant)
    updated_fields = _NeighborRecord{I}[]
    updated_dual = I[]
    for w in touched
        field = I(BigInt(numeric.fields[w]) + f_map[w])
        lo = numeric.lower === nothing ? field : I(BigInt(numeric.lower[w]) + lo_map[w])
        hi = numeric.upper === nothing ? field : I(BigInt(numeric.upper[w]) + hi_map[w])
        dual_delta = is_bool ? div(f_map[w],2) + div(qsum_map[w],4) : 2*f_map[w] - 2*qsum_map[w]
        push!(updated_fields, (w,field,lo,hi))
        push!(updated_dual, I(BigInt(numeric.dual_fields[w]) + dual_delta))
    end
    planned_adjacency = Dict(w=>copy(numeric.adjacency[w]) for w in touched)
    planned_positions = Dict(w=>copy(st.adj_pos[w]) for w in touched)
    adj_edits = _AdjacencyEdit{I}[]
    _reserve!(adj_edits, length(u_free_edges) + 2 * length(merged_quad_deltas))
    for (w, _) in u_free_edges
        _adj_set!(planned_adjacency, planned_positions, adj_edits, w, u, zero(I))
    end
    for (j, k, dq) in merged_quad_deltas
        pos_j = get(st.adj_pos[j], k, 0)
        q_old = pos_j == 0 ? big(0) : numeric.adjacency[j][pos_j].second
        q_new = q_old + dq
        _adj_set!(planned_adjacency, planned_positions, adj_edits, j, k, I(q_new))
        _adj_set!(planned_adjacency, planned_positions, adj_edits, k, j, I(q_new))
    end
    elim_lens = ntuple(b -> length(st.elim_queues[b]), 4)
    entry = _UndoReduction(
        st.serial + 1,
        length(st.fixes) + 1,
        u,
        status,
        numeric.constant,
        numeric.dual_constant,
        old_fields,
        old_dual,
        adj_edits,
        length(st.queue),
        proof,
        I(spin_const_delta),
        Pair{Int,I}[j=>I(v) for (j,v) in spin_field_deltas],
        Tuple{Int,Int,I}[(j,k,I(v)) for (j,k,v) in spin_coupling_deltas],
        elim_lens,
        length(st.rel_queue),
    )
    for w in touched
        numeric.adjacency[w] = planned_adjacency[w]
        st.adj_pos[w] = planned_positions[w]
    end
    push!(numeric.trail, entry)
    push!(st.fixes, length(numeric.trail))
    st.proof_count == 0 && (st.first_proof_pos = length(numeric.trail))
    st.proof_count += 1
    (proof isa MaxCutStep || (proof isa RelationStep && proof.method in (:probing_pair, :roof_scc_pair))) && (st.marginal_count += 1)
    st.entries[u] = length(numeric.trail)
    st.serial += 1
    numeric.constant = constant_i
    numeric.dual_constant = dual_constant_i
    st.fixed[u] = status
    st.degrees[u] = 0
    st.active_edges += (-old_dual[1][3] + sum(values(deg_map); init=0)) ÷ 2
    for (idx,(w,field,lo,hi)) in enumerate(updated_fields)
        numeric.fields[w] = field
        numeric.dual_fields[w] = updated_dual[idx]
        st.degrees[w] += deg_map[w]
        if numeric.lower !== nothing
            numeric.lower[w] = lo
            numeric.upper[w] = hi
        end
        if !st.queued[w]
            push!(st.queue, w)
            st.queued[w] = true
        end
        d_w = st.degrees[w]
        if d_w <= 3 && (d_w < 3 || _may_be_quadratic_deg3_fast(ws, w)) && !st.elim_queued[d_w + 1][w]
            push!(st.elim_queues[d_w + 1], w)
            st.elim_queued[d_w + 1][w] = true
        end
        d_w == 3 && _may_be_quadratic_deg3_fast(ws, w) && (st.star_hint = st.elim_heads[4])
        if d_w >= 1 && !st.rel_queued[w]
            push!(st.rel_queue, w)
            st.rel_queued[w] = true
        end
    end
    return UpdateReport(:applied, visits, 1)
end

"""
    RollbackReport

Optional owned rollback result: source `generation`, restored `checkpoint`,
`caller_unfixed` and `deduction_unfixed` vectors of original-index => removed-value
pairs in reverse application order. These are indices, unlike the label-based
`assumptions`/`deductions` queries. They describe removals, not new proof claims.
"""
struct RollbackReport
    generation::Generation
    checkpoint::Checkpoint
    caller_unfixed::Vector{Pair{Int,Int}}
    deduction_unfixed::Vector{Pair{Int,Int}}
end
generation(r::RollbackReport) = r.generation

"""
    rollback!(ws, checkpoint; report=false)

Restore fields, constant, free/fixed values, queue flags and assumptions exactly
in reverse trail order. Cost is proportional to undone entries/touched fields
and appended queue entries. No source graph copy or floating subtraction occurs.
Invalid checkpoints fail before mutation. Rollback completes without a work or
deadline limit; callers bound its cost by bounding preceding updates.

By default return `ws`. With `report=true`, return a [`RollbackReport`](@ref)
whose removed-fixing vectors are prepared before mutation. Capture visits only
fixing records after `cp`, not queue-only history or unrelated source vertices.
Rollback itself still costs all undone journal/field/queue work. Empty reports
cost constant-size work and no full materialization is needed.
"""
function rollback!(ws::Workspace, cp::Checkpoint;report::Bool=false)
    _validate_checkpoint(ws, cp)
    st = ws._state
    return _rollback_integer!(ws, st, st.numeric, cp; report)
end

# Rollback restores journaled values without regridding or replacing the payload.
# Dispatch once so undo iteration and numeric array writes retain their type.
function _rollback_integer!(ws::Workspace, st::_Incremental, numeric::_IntegerState{I},
                            cp::Checkpoint; report::Bool=false) where {I<:Integer}
    captured = if report
        callers,deductions = Pair{Int,Int}[],Pair{Int,Int}[]
        for k in length(st.fixes):-1:cp._fix_depth+1
            e = numeric.trail[st.fixes[k]]
            if e isa _UndoFix
                push!(e.proof === nothing ? callers : deductions,e.index=>e.value)
            end
        end
        RollbackReport(generation(ws),cp,callers,deductions)
    else
        nothing
    end
    while length(numeric.trail) > cp._depth
        undo = pop!(numeric.trail)
        if undo isa _UndoQueue
            b = Int(undo.bucket)
            if b == 0
                st.head = undo.head
                st.queued[undo.index] = undo.queued
            elseif b == -1
                u = undo.index
                st.rel_blocked_fill[u] < typemax(Int) && pop!(st.rel_deferred)
                !st.rel_checked_weak[u] && pop!(st.rel_weak_deferred)
                if st.rel_checked_weak[u] != undo.checked_weak
                    st.unweak_rel_count += undo.checked_weak ? -1 : 1
                end
                st.rel_head = undo.head
                st.rel_queued[u] = undo.queued
                st.rel_blocked_fill[u] = undo.blocked_fill
                st.rel_checked_weak[u] = undo.checked_weak
            elseif b == -2
                pop!(st.rel_queue)
                st.rel_queued[undo.index] = undo.queued
                st.rel_blocked_fill[undo.index] = undo.blocked_fill
                st.rel_checked_weak[undo.index] = undo.checked_weak
            elseif 1 <= b <= 4
                u = undo.index
                st.elim_blocked_fill[b][u] < typemax(Int) && pop!(st.elim_deferred[b])
                st.elim_heads[b] = undo.head
                st.elim_queued[b][u] = undo.queued
                st.elim_blocked_fill[b][u] = undo.blocked_fill
            else
                eb = b - 4
                pop!(st.elim_queues[eb])
                st.elim_queued[eb][undo.index] = undo.queued
                st.elim_blocked_fill[eb][undo.index] = undo.blocked_fill
            end
        elseif undo isa _UndoReduction
            for r in length(undo.adj_edits):-1:1
                op, a, pos, old_pair = undo.adj_edits[r]
                if op === :pop
                    popped = pop!(numeric.adjacency[a])
                    delete!(st.adj_pos[a], popped.first)
                elseif op === :swap_remove
                    if pos <= length(numeric.adjacency[a])
                        moved_pair = numeric.adjacency[a][pos]
                        push!(numeric.adjacency[a], moved_pair)
                        st.adj_pos[a][moved_pair.first] = length(numeric.adjacency[a])
                        numeric.adjacency[a][pos] = old_pair
                    else
                        push!(numeric.adjacency[a], old_pair)
                    end
                    st.adj_pos[a][old_pair.first] = pos
                else
                    numeric.adjacency[a][pos] = old_pair
                end
            end
            for (j, field, lower, upper) in undo.fields
                numeric.fields[j] = field
                if numeric.lower !== nothing
                    numeric.lower[j], numeric.upper[j] = lower, upper
                end
            end
            deg_delta = 0
            for (j, df, deg) in undo.dual_fields
                deg_delta += deg - st.degrees[j]
                numeric.dual_fields[j] = df
                st.degrees[j] = deg
            end
            st.active_edges += deg_delta ÷ 2
            while length(st.queue) > undo.queue_length
                st.queued[pop!(st.queue)] = false
            end
            for b in 1:4
                while length(st.elim_queues[b]) > undo.elim_queue_lengths[b]
                    st.elim_queued[b][pop!(st.elim_queues[b])] = false
                end
            end
            while length(st.rel_queue) > undo.rel_queue_length
                st.rel_queued[pop!(st.rel_queue)] = false
            end
            st.fixed[undo.index] = 2
            st.entries[undo.index] = 0
            pop!(st.fixes)
            st.proof_count -= 1
            st.proof_count == 0 && (st.first_proof_pos = 0)
            (undo.proof isa MaxCutStep || (undo.proof isa RelationStep && undo.proof.method in (:probing_pair, :roof_scc_pair))) && (st.marginal_count -= 1)
            numeric.constant = undo.constant
            numeric.dual_constant = undo.dual_constant
        else
            for (j,field,lower,upper) in undo.fields
                numeric.fields[j] = field
                if numeric.lower !== nothing
                    numeric.lower[j],numeric.upper[j] = lower,upper
                end
            end
            for (j, df) in undo.dual_fields
                numeric.dual_fields[j] = df
                st.degrees[j] += 1
            end
            st.active_edges += length(undo.dual_fields)
            while length(st.queue) > undo.queue_length
                st.queued[pop!(st.queue)] = false
            end
            for b in 1:4
                while length(st.elim_queues[b]) > undo.elim_queue_lengths[b]
                    st.elim_queued[b][pop!(st.elim_queues[b])] = false
                end
            end
            while length(st.rel_queue) > undo.rel_queue_length
                st.rel_queued[pop!(st.rel_queue)] = false
            end
            st.fixed[undo.index] = 2
            st.degrees[undo.index] = length(undo.fields)
            st.entries[undo.index] = 0
            pop!(st.fixes)
            if undo.proof === nothing
                pop!(st.callers)
            else
                st.proof_count -= 1
                st.proof_count == 0 && (st.first_proof_pos = 0)
                (undo.proof isa ProbingStep || undo.proof isa RoofDualityStep || undo.proof isa SubmodularCutStep || undo.proof isa MaxCutStep ||
                 (hasproperty(undo.proof, :method) && undo.proof.method === :marginal)) &&
                    (st.marginal_count -= 1)
            end
            numeric.constant = undo.constant
            numeric.dual_constant = undo.dual_constant
        end
    end
    filter!(p -> p[4] <= cp._pin, st.pins)
    st.star_hint = st.elim_heads[4]
    st.rel_hint = st.rel_head
    return report ? captured : ws
end

"""
    assumptions(ws)

Return owned original-label/value pairs in application order, O(k) for k active
assumptions. No graph scan, residual construction or proof claim is involved.
"""
function assumptions(ws::Workspace)
    s = ws._snapshot
    st = ws._state
    return [_owned_labels([s.labels[st.trail[p].index]])[1]=>st.trail[p].value for p in st.callers]
end

"""
    changes(ws, checkpoint)

Return owned caller assumptions added since a still-valid ancestor checkpoint,
in application order; O(number of changes), with no full residual copy.
"""
function changes(ws::Workspace, cp::Checkpoint)
    _validate_checkpoint(ws, cp)
    s, st = ws._snapshot, ws._state
    entries = (st.trail[st.fixes[k]] for k in cp._fix_depth+1:length(st.fixes))
    return [_owned_labels([s.labels[e.index]])[1]=>e.value for e in entries if e.proof === nothing]
end

"""
    unfix!(ws, label; max_work=typemax(Int), deadline_ns=nothing)

Remove a caller assumption. The most recent one rolls back locally. Otherwise
build fresh algebra and replay all retained assumptions, then replace state only
on success; every prior checkpoint is invalidated. This conservative path costs
O(n+m + retained adjacency work), plus exact arithmetic, and allocates a new
workspace state. `max_work` bounds replay adjacency visits, not initialization;
the latter always costs O(n+m). Deadline/work stops preserve the old state.
Later deductions are undone by the local path. Non-LIFO replay discards all
deductions and replays only explicit caller assumptions, never inferred values.
Resume inference explicitly with `propagate!`. Removing a deduction directly
is rejected; use its ancestor checkpoint.
"""
function unfix!(ws::Workspace, label; max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    i = _variable(ws, label)
    st = ws._state
    st.fixed[i] == 2 && return UpdateReport(:unchanged, 0, 0)
    position = st.entries[i]
    st.trail[position].proof === nothing || throw(ArgumentError(
        "unfix! removes caller assumptions; rollback before undoing a certified deduction"))
    _expired(deadline_ns) && return UpdateReport(:deadline, 0, 0)
    if st.callers[end] == position
        cp = _checkpoint_at(ws,position-1)
        rollback!(ws, cp)
        return UpdateReport(:applied, 0, 1)
    end
    work = 0
    for p in st.callers
        e = st.trail[p]
        e.index == i && continue
        degree = st.initial_degrees[e.index]
        degree <= max_work - work || return UpdateReport(:work_limit, 0, 0)
        work += degree
    end
    staged = Workspace(ws._snapshot,generation(ws),_incremental(ws._snapshot;rules=st.rules))
    visits = 0
    for p in st.callers
        e = st.trail[p]
        e.index == i && continue
        r = assume!(staged, ws._snapshot.labels[e.index], e.value; max_work=max_work-visits, deadline_ns)
        visits += r.edge_visits
        r.stop_reason === :applied || return UpdateReport(r.stop_reason, visits, 0)
    end
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    staged._state.total_candidates = st.total_candidates
    staged._state.total_edges = st.total_edges
    staged._state.total_exact = st.total_exact
    ws._state = staged._state
    return UpdateReport(:applied, visits, 1)
end

function index_map(ws::Workspace)
    map = zeros(Int, length(ws._state.fixed))
    j = 0
    for i in eachindex(map)
        if ws._state.fixed[i] == 2
            map[i] = (j += 1)
        end
    end
    return map
end

const _ConditionedCertNT = NamedTuple{
    (:scope, :assumptions, :reduction_chain, :unchanged_representation, :proof),
    Tuple{Symbol, Tuple, Tuple, Bool, Any},
}

"""
    ConditionedExport

Owned historical residual under explicit caller assumptions and/or certified
deductions. `status=:certified` certifies exact algebra/transport within that
scope, not that caller assumptions retain a global optimum. The certificate
contains the ordered strong-deduction proof when present; no solver proof is produced.
An explicitly rounded Float64 transport has `status=:rounded` and records its
largest effective-coefficient change in `max_perturbation`; the reduction proof
continues to describe the exact residual, not the rounded solver model.
Original labels/maps, scope and exact residual data are immutable snapshots;
`export_model` returns a separately owned QUBOTools model.
"""
struct ConditionedExport{T}
    _snapshot::_Snapshot
    generation::Generation
    status::Symbol
    certificate::_ConditionedCertNT
    _fixed::Tuple
    _free::Tuple
    _linear::Tuple
    _quadratic::Tuple
    _constant::T
    _scale::T
    _map::Union{Nothing,DomainGaugeMap}
end
generation(r::ConditionedExport) = r.generation
original_variables(r::ConditionedExport) = _labels_vector(r._snapshot)

@inline function Base.getproperty(r::ConditionedExport, name::Symbol)
    name === :perturbed && return getfield(r, :_snapshot).perturbed
    name === :max_perturbation && return getfield(r, :_snapshot).max_perturbation
    return getfield(r, name)
end
Base.propertynames(::ConditionedExport, private::Bool=false) =
    private ? (:_snapshot, :generation, :status, :certificate, :_fixed, :_free, :_linear, :_quadratic, :_constant, :_scale, :_map, :perturbed, :max_perturbation) :
              (:generation, :status, :certificate, :perturbed, :max_perturbation)

function Base.deepcopy_internal(r::ConditionedExport{T}, dict::IdDict) where T
    haskey(dict, r) && return dict[r]::ConditionedExport{T}
    proof_copy = Base.deepcopy_internal(r.certificate.proof, dict)
    chain_copy = if proof_copy isa DominanceCertificate &&
            r.certificate.proof isa DominanceCertificate &&
            r.certificate.reduction_chain === r.certificate.proof.steps
        proof_copy.steps
    else
        _deepcopy_steps(r.certificate.reduction_chain, dict)
    end
    cert_copy = _ConditionedCertNT((
        r.certificate.scope,
        _deepcopy_tuple(r.certificate.assumptions, dict),
        chain_copy,
        r.certificate.unchanged_representation,
        proof_copy,
    ))
    return ConditionedExport{T}(
        Base.deepcopy_internal(r._snapshot, dict),
        r.generation,
        r.status,
        cert_copy,
        _deepcopy_tuple(r._fixed, dict),
        _deepcopy_tuple(r._free, dict),
        _deepcopy_tuple(r._linear, dict),
        _deepcopy_tuple(r._quadratic, dict),
        Base.deepcopy_internal(r._constant, dict),
        Base.deepcopy_internal(r._scale, dict),
        Base.deepcopy_internal(r._map, dict),
    )
end

function _fill_index_map!(map::Vector{Int}, @nospecialize(free::Tuple))
    for j in 1:length(free)
        map[_entry_at(free, j)::Int] = j
    end
    return map
end

function index_map(r::ConditionedExport)
    map = zeros(Int, length(r._fixed))
    return _fill_index_map!(map, r._free)
end

function _transport_error(ws::Workspace, q::_Exact, kind::Symbol, i::Int, j::Int)
    s, st = ws._snapshot, ws._state
    coefficient = kind === :linear ? "linear coefficient for variable $(repr(s.labels[i]))" :
        kind === :quadratic ? "coupling ($(repr(s.labels[i])), $(repr(s.labels[j])))" :
        kind === :constant ? "constant" : "scale"
    n = abs(numerator(q))
    bits = iszero(n) ? 0 : ndigits(n; base=2) - trailing_zeros(n)
    families = Symbol[]
    for p in st.fixes
        step = st.trail[p].proof
        family = step === nothing ? :CallerAssumption : nameof(typeof(step))
        family in families || push!(families, family)
    end
    chain = isempty(families) ? "none (coordinate conversion only)" : join(string.(families), ", ")
    throw(ArgumentError("conditioned $coefficient cannot be represented exactly as finite Float64 " *
        "($bits significant numerator bits; Float64 has 53 significant bits). " *
        "Reduction-chain families: $chain. Fixings, eliminations and contractions add exact sums " *
        "of input coefficients; the final state cannot attribute this coefficient to one family. " *
        "Use coefficient_type=Rational{BigInt} for exact transport, rounding=:nearest for recorded " *
        "finite Float64 rounding, normalization=:integer when its primitive integers and adjusted " *
        "scale fit exactly, or integerize_scale on input when an exact scaling is available."))
end

# Rational{BigInt}'s ordinary floating conversion can pass through the ambient
# BigFloat precision. Round directly with integer arithmetic instead, including
# halfway cases and subnormals, and assemble the binary64 representation exactly.
function _nearest_float64(q::_Exact)
    n = numerator(q)
    sign = n < 0 ? UInt64(1) << 63 : UInt64(0)
    iszero(n) && return reinterpret(Float64, sign)
    n = abs(n)
    d = denominator(q)
    exponent = ndigits(n; base=2) - ndigits(d; base=2)
    # The bit-length estimate is either floor(log2(abs(q))) or one greater.
    # Bound it before shifting: arbitrarily large/small rationals need no work
    # proportional to their distance from the representable exponent range.
    exponent > 1024 && return reinterpret(Float64, sign | UInt64(0x7ff0000000000000))
    exponent < -1075 && return reinterpret(Float64, sign)
    below = exponent >= 0 ? n < (d << exponent) : (n << -exponent) < d
    below && (exponent -= 1)
    exponent > 1023 && return reinterpret(Float64, sign | UInt64(0x7ff0000000000000))
    unit_exponent = max(exponent - 52, -1074)
    scaled_n, scaled_d = unit_exponent >= 0 ? (n, d << unit_exponent) :
        (n << -unit_exponent, d)
    significand, remainder = divrem(scaled_n, scaled_d)
    twice_remainder = remainder << 1
    if twice_remainder > scaled_d || (twice_remainder == scaled_d && isodd(significand))
        significand += 1
    end
    if significand < (UInt64(1) << 52)
        # A subnormal's integer significand is already its fraction bit field.
        return reinterpret(Float64, sign | UInt64(significand))
    end
    exponent = unit_exponent + 52
    if significand == (UInt64(1) << 53)
        significand >>= 1
        exponent += 1
    end
    exponent > 1023 && return reinterpret(Float64, sign | UInt64(0x7ff0000000000000))
    bits = sign | (UInt64(exponent + 1023) << 52) | (UInt64(significand) - (UInt64(1) << 52))
    return reinterpret(Float64, bits)
end

function _transport(::Type{Float64}, q::_Exact; rounding::Symbol=:none,
                    ws::Workspace, kind::Symbol=:constant, i::Int=0, j::Int=0)
    v = _nearest_float64(q)
    isfinite(v) && (rounding === :nearest || _Exact(v) == q) ||
        _transport_error(ws, q, kind, i, j)
    return v
end
_transport(::Type{_Exact}, q::_Exact; kwargs...) = deepcopy(q)

function _with_export_perturbation(s::_Snapshot, error::_Exact)
    max_perturbation = max(s.max_perturbation, error)
    return _Snapshot(s.labels, s.label_type, s.state_type, s.linear, s.quadratic,
        s.scale, s.offset, s.sense, s.domain, !iszero(max_perturbation), max_perturbation)
end

# Maintain the common denominator D and gcd G of the corresponding integer
# numerators as each mapped term is included. The constant shares this basis.
function _include_normalization_term(D::BigInt, G::BigInt, q::_Exact)
    d = denominator(q)
    next_D = lcm(D, d)
    next_G = gcd(G * div(next_D, D), abs(numerator(q)) * div(next_D, d))
    return next_D, next_G
end

function _integer_normalization_factor(ws::Workspace, free::Vector{Int}, map)
    D, G = big(1), big(0)
    for i in free
        D, G = _include_normalization_term(D, G, _mapped_field(ws, i, map))
        for (j, q) in ws._state.adjacency[i]
            if i < j && ws._state.fixed[j] == 2
                D, G = _include_normalization_term(D, G, _mapped_coupling(ws, i, j, q, map))
            end
        end
    end
    D, G = _include_normalization_term(D, G, _direct_mapped_constant(ws, map))
    # There is no primitive gcd for the zero polynomial. Use the neutral factor
    # so zero coefficients and the original finite scale remain unchanged.
    return iszero(G) ? one(_Exact) : G // D
end

function _conditioned_export(ws::Workspace, ::Type{T}; map::Union{Nothing,DomainGaugeMap}=nothing,
                             rounding::Symbol=:none, normalization::Symbol=:none) where T
    T in (Float64, _Exact) || throw(ArgumentError("supported transport: Float64 or Rational{BigInt}"))
    map === nothing || _validate_domain_map(ws, map; full=true)
    s, st = ws._snapshot, ws._state
    snapshot = deepcopy(s)
    _validate_label_copy(s.labels, snapshot.labels)
    owned_map = map === nothing ? nothing : deepcopy(map)
    free = findall(==(2), st.fixed)
    factor = normalization === :integer ? _integer_normalization_factor(ws, free, owned_map) : one(_Exact)
    idxmap = index_map(ws)
    rounding_error = zero(_Exact)
    lin_vec = Vector{T}(undef, length(free))
    for (idx_f, i) in enumerate(free)
        q = _mapped_field(ws, i, owned_map)
        normalization === :integer && (q /= factor)
        v = _transport(T, q; rounding, ws, kind=:linear, i)
        lin_vec[idx_f] = v
        rounding === :nearest && (rounding_error = max(rounding_error, abs(_to_exact(v) - q)))
    end
    linear = Tuple(lin_vec)
    quad_vec = Tuple{Int,Int,T}[]
    for i in free
        ii = idxmap[i]
        for (j, q) in st.adjacency[i]
            if i < j && st.fixed[j] == 2
                mapped_q = _mapped_coupling(ws, i, j, q, owned_map)
                normalization === :integer && (mapped_q /= factor)
                v = _transport(T, mapped_q; rounding, ws, kind=:quadratic, i, j)
                push!(quad_vec, (ii, idxmap[j], v))
                rounding === :nearest && (rounding_error = max(rounding_error, abs(_to_exact(v) - mapped_q)))
            end
        end
    end
    quadratic = Tuple(quad_vec)
    scope = _caller_scope(ws)
    proof = _export_certificate(ws,snapshot;map=owned_map)
    steps = proof === nothing ? () : proof.steps
    unchanged = isone(factor) && isempty(st.fixes) && !s.perturbed && (owned_map === nothing ||
        (owned_map.target_domain === owned_map.source_domain && owned_map._identity_gauge))
    c_export = _direct_mapped_constant(ws, owned_map)
    normalization === :integer && (c_export /= factor)
    c_transport = _transport(T, c_export; rounding, ws, kind=:constant)
    rounding === :nearest && (rounding_error = max(rounding_error, abs(_to_exact(c_transport) - c_export)))
    # The exact positive normalization factor preserves effective coefficients,
    # scale sign and objective sense. The adjusted scale is never rounded.
    adjusted_scale = normalization === :integer ? _Exact(s.scale) * factor : _Exact(s.scale)
    scale_transport = _transport(T, adjusted_scale; ws, kind=:scale)
    normalization === :integer && iszero(s.scale) && (scale_transport = s.scale)
    rounded = !iszero(rounding_error)
    if rounded
        # Keep the proof's source metadata unchanged: it certifies the exact
        # reductions, while the export additionally records solver rounding.
        snapshot = _with_export_perturbation(snapshot, abs(_Exact(s.scale)) * rounding_error)
    end
    cert = _ConditionedCertNT((
        isempty(scope) ? :original : :assumptions,
        scope,
        steps,
        unchanged && !rounded,
        proof,
    ))
    return ConditionedExport{T}(snapshot, generation(ws), rounded ? :rounded : :certified,
        cert,
        Tuple(st.fixed), Tuple(free), linear, quadratic,
        c_transport, scale_transport, owned_map)
end

function _build_export_linear(::Type{T}, @nospecialize(lin::Tuple)) where T
    n = length(lin)
    d = Dict{Int,T}()
    sizehint!(d, n)
    for i in 1:n
        d[i] = deepcopy(_entry_at(lin, i)::T)
    end
    return QT.DictLinearForm{T}(d)
end

function _build_export_quadratic(::Type{T}, @nospecialize(quad::Tuple)) where T
    m = length(quad)
    d = Dict{Tuple{Int,Int},T}()
    sizehint!(d, m)
    for k in 1:m
        item = _entry_at(quad, k)::Tuple{Int,Int,T}
        d[(item[1], item[2])] = deepcopy(item[3])
    end
    return QT.DictQuadraticForm{T}(d)
end

function export_model(r::ConditionedExport{T}) where T
    s = r._snapshot
    V, U = s.label_type, s.state_type
    labels = original_variables(r)[_ints(r._free)]
    vm = QT.VariableMap{V}(Dict{V,Int}(v=>i for (i,v) in enumerate(labels)), labels)
    lf = _build_export_linear(T, r._linear)
    qf = _build_export_quadratic(T, r._quadratic)
    dom = r._map === nothing ? s.domain : _qt_domain(r._map.target_domain)
    f = QT.Form{T}(length(labels), lf, qf, deepcopy(r._scale), deepcopy(r._constant);
                   sense=s.sense, domain=dom)
    return QT.Model{V,T,U}(vm, f)
end

function _lift_state_impl(
    r::ConditionedExport,
    y::AbstractVector,
    @nospecialize(free::Tuple),
    @nospecialize(steps::Tuple),
)
    Base.require_one_based_indexing(y)
    n_free = length(free)
    length(y) == n_free || throw(ArgumentError("state must cover every free variable"))
    is_bool = r._snapshot.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    target_dom = r._map === nothing ? _domain_symbol(r._snapshot.domain) : r._map.target_domain
    low = target_dom === :bool ? 0 : -1
    state = _ints(r._fixed)
    for j in 1:n_free
        i = _entry_at(free, j)::Int
        v = y[j]
        v isa Real && isfinite(v) && (v == low || v == 1) ||
            throw(ArgumentError("state value is outside the residual domain"))
        iv = Int(v)
        state[i] = r._map === nothing ? iv : _lift_index_value(r._map, i, iv)
    end
    for k in length(steps):-1:1
        step = _entry_at(steps, k)
        if step isa Union{DominanceStep,ProbingStep,RoofDualityStep,SubmodularCutStep}
            state[step.variable] = step.value
        elseif step isa MaxCutStep
            if step.representative == 0
                state[step.eliminated] = step.value
            else
                rep_val = state[step.representative]
                (rep_val == low_orig || rep_val == 1) ||
                    throw(ArgumentError("representative variable $(step.representative) not reconstructed before relation step"))
                s_rep = is_bool ? (2 * rep_val - 1) : rep_val
                s_elim = step.orig_sign * s_rep
                state[step.eliminated] = is_bool ? ((s_elim + 1) ÷ 2) : s_elim
            end
        elseif step isa RelationStep
            rep_val = state[step.representative]
            (rep_val == low_orig || rep_val == 1) ||
                throw(ArgumentError("representative variable $(step.representative) not reconstructed before relation step"))
            s_rep = is_bool ? (2 * rep_val - 1) : rep_val
            s_elim = step.orig_sign * s_rep
            state[step.eliminated] = is_bool ? ((s_elim + 1) ÷ 2) : s_elim
        elseif step isa EliminationStep
            idx = 1
            for (bit_pos, nbr) in enumerate(step.neighbors)
                nbr_val = state[nbr]
                (nbr_val == low_orig || nbr_val == 1) ||
                    throw(ArgumentError("boundary neighbor $nbr not reconstructed before elimination step"))
                if nbr_val == 1
                    idx += 1 << (bit_pos - 1)
                end
            end
            state[step.variable] = step.table[idx]
        end
    end
    all(v -> v == low_orig || v == 1, state) ||
        throw(ArgumentError("incomplete reconstruction chain for removed variables"))
    return state
end

_lift_state(r::ConditionedExport, y::AbstractVector) =
    _lift_state_impl(r, y, r._free, r.certificate.reduction_chain)
function reconstruct(r::ConditionedExport,y::AbstractVector)
    state = _lift_state(r,y)
    return _evaluate_state(r,state,_source_evaluator(r._snapshot))
end
reconstruct(::ConditionedExport, y) = throw(ArgumentError("state must be a complete ordered residual vector"))
