# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    PropagationReport

Bounded-call result with generation/checkpoint, `stop_reason`, examined
`candidates`, `edge_visits`, new `deductions`, reserved `exact_work`, raw
`pending` queue entries and cumulative propagation `totals`. Counters measure
executed/reserved work and are not undone by model rollback. Caller updates,
initial construction, proof export and verification remain separate boundaries.
"""
struct PropagationReport
    generation::Generation
    checkpoint::Checkpoint
    stop_reason::Symbol
    candidates::Int
    edge_visits::Int
    deductions::Int
    exact_work::Int
    pending::Int
    totals::NamedTuple{(:candidates,:edge_visits,:exact_work),Tuple{Int,Int,Int}}
end
generation(r::PropagationReport) = r.generation

function _propagation_report!(ws,reason,candidates,edges,deductions,exact;pending=nothing)
    st = ws._state
    st.total_candidates += candidates
    st.total_edges += edges
    st.total_exact += exact
    pend = pending === nothing ? (length(st.queue)-st.head+1) : pending
    return PropagationReport(generation(ws),checkpoint(ws),reason,candidates,edges,deductions,exact,
        pend,
        (candidates=st.total_candidates,edge_visits=st.total_edges,exact_work=st.total_exact))
end

function _pop_queue!(ws::Workspace)
    st = ws._state
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    i = st.queue[st.head]
    entry = _UndoQueue(st.serial+1,length(st.fixes),i,st.head,st.queued[i],Int8(0))
    _reserve!(st.trail,length(st.trail)+1)
    push!(st.trail,entry)
    st.serial += 1
    st.queued[i] = false
    st.head += 1
    return nothing
end

function _pop_elim_queue!(ws::Workspace, b::Int, blocked_fill::Int=typemax(Int))
    st = ws._state
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    q = st.elim_queues[b]
    qd = st.elim_queued[b]
    h = st.elim_heads[b]
    i = q[h]
    entry = _UndoQueue(
        st.serial + 1, length(st.fixes), i, h, qd[i],
        Int8(b), st.elim_blocked_fill[b][i], false,
    )
    _reserve!(st.trail, length(st.trail) + 1)
    push!(st.trail, entry)
    st.serial += 1
    qd[i] = false
    blocked_fill < typemax(Int) && push!(st.elim_deferred[b], i)
    st.elim_blocked_fill[b][i] = blocked_fill
    st.elim_heads[b] = h + 1
    return nothing
end

function _pop_rel_queue!(ws::Workspace, blocked_fill::Int=typemax(Int), checked_weak::Bool=true)
    st = ws._state
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    u = st.rel_queue[st.rel_head]
    entry = _UndoQueue(
        st.serial + 1, length(st.fixes), u, st.rel_head, st.rel_queued[u],
        Int8(-1), st.rel_blocked_fill[u], st.rel_checked_weak[u],
    )
    _reserve!(st.trail, length(st.trail) + 1)
    push!(st.trail, entry)
    st.serial += 1
    st.rel_queued[u] = false
    blocked_fill < typemax(Int) && push!(st.rel_deferred, u)
    !checked_weak && push!(st.rel_weak_deferred, u)
    if st.rel_checked_weak[u] != checked_weak
        st.unweak_rel_count += checked_weak ? -1 : 1
    end
    st.rel_blocked_fill[u] = blocked_fill
    st.rel_checked_weak[u] = checked_weak
    st.rel_head += 1
    return nothing
end

function _deferred_rel_eligible(st::_Incremental, u::Int, mf::Int, allow_weak::Bool)
    return st.fixed[u] == 2 && st.degrees[u] >= 1 && !st.rel_queued[u] &&
           ((st.rel_blocked_fill[u] < typemax(Int) && mf >= st.rel_blocked_fill[u]) ||
            (allow_weak && !st.rel_checked_weak[u]))
end

function _next_deferred_rel(st::_Incremental, mf::Int, allow_weak::Bool)
    list = (allow_weak && st.unweak_rel_count > 0) ? view(st.rel_queue, 1:(st.rel_head - 1)) : st.rel_deferred
    @inbounds for u in list
        _deferred_rel_eligible(st, u, mf, allow_weak) && return u
    end
    return 0
end

function _count_deferred_rel(st::_Incremental, mf::Int, allow_weak::Bool)
    list = (allow_weak && st.unweak_rel_count > 0) ? view(st.rel_queue, 1:(st.rel_head - 1)) : st.rel_deferred
    cnt = 0
    @inbounds for idx in eachindex(list)
        u = list[idx]
        if _deferred_rel_eligible(st, u, mf, allow_weak)
            !(u in view(list, 1:(idx - 1))) && (cnt += 1)
        end
    end
    return cnt
end

function _requeue_deferred_rel!(ws::Workspace, mf::Int, allow_weak::Bool)
    st = ws._state
    use_full = allow_weak && st.unweak_rel_count > 0
    limit = use_full ? (st.rel_head - 1) : length(st.rel_deferred)
    @inbounds for idx in 1:limit
        u = use_full ? st.rel_queue[idx] : st.rel_deferred[idx]
        if _deferred_rel_eligible(st, u, mf, allow_weak)
            st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
            entry = _UndoQueue(
                st.serial + 1, length(st.fixes), u, st.rel_head, false,
                Int8(-2), st.rel_blocked_fill[u], st.rel_checked_weak[u],
            )
            _reserve!(st.trail, length(st.trail) + 1)
            _reserve!(st.rel_queue, length(st.rel_queue) + 1)
            push!(st.trail, entry)
            st.serial += 1
            push!(st.rel_queue, u)
            st.rel_queued[u] = true
        end
    end
    return nothing
end

function _contraction_fill(st::_Incremental, elim::Int, rep::Int)
    fill = 0
    for (w, q) in st.adjacency[elim]
        (w != rep && st.fixed[w] == 2 && !iszero(q)) || continue
        haskey(st.adj_pos[rep], w) || (fill += 1)
    end
    return fill
end

function _next_elim_bucket(st::_Incremental, max_degree::Int; min_bucket::Int=1)
    @inbounds for b in min_bucket:(max_degree + 1)
        st.elim_heads[b] <= length(st.elim_queues[b]) && return b
    end
    return 0
end

function _elimination_fill(st::_Incremental, quad_deltas)
    fill = 0
    for (a, b, dq) in quad_deltas
        iszero(dq) && continue
        pos = get(st.adj_pos[a], b, 0)
        (pos == 0 || iszero(st.adjacency[a][pos].second)) && (fill += 1)
    end
    return fill
end

function _deferred_elim_eligible(st::_Incremental, b::Int, u::Int, mf::Int)
    return st.fixed[u] == 2 && st.degrees[u] == b - 1 && !st.elim_queued[b][u] &&
           st.elim_blocked_fill[b][u] < typemax(Int) && mf >= st.elim_blocked_fill[b][u]
end

function _next_deferred_elim(st::_Incremental, md::Int, mf::Int; min_bucket::Int=1)
    @inbounds for b in min_bucket:(md + 1)
        for u in st.elim_deferred[b]
            _deferred_elim_eligible(st, b, u, mf) && return b
        end
    end
    return 0
end

function _count_deferred_elim(st::_Incremental, md::Int, mf::Int; min_bucket::Int=1)
    cnt = 0
    @inbounds for b in min_bucket:(md + 1)
        q = st.elim_deferred[b]
        for idx in eachindex(q)
            u = q[idx]
            if _deferred_elim_eligible(st, b, u, mf)
                !(u in view(q, 1:(idx - 1))) && (cnt += 1)
            end
        end
    end
    return cnt
end

function _requeue_deferred_elim!(ws::Workspace, md::Int, mf::Int; min_bucket::Int=1)
    st = ws._state
    @inbounds for b in min_bucket:(md + 1)
        q = st.elim_queues[b]
        for u in st.elim_deferred[b]
            if _deferred_elim_eligible(st, b, u, mf)
                st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
                entry = _UndoQueue(
                    st.serial + 1, length(st.fixes), u, st.elim_heads[b], false,
                    Int8(b + 4), st.elim_blocked_fill[b][u], false,
                )
                _reserve!(st.trail, length(st.trail) + 1)
                _reserve!(q, length(q) + 1)
                push!(st.trail, entry)
                st.serial += 1
                push!(q, u)
                st.elim_queued[b][u] = true
            end
        end
    end
    return nothing
end

function _cached_step(ws::Workspace,i::Int,direction::Int;allow_weak::Bool=false)
    st = ws._state
    direction == 0 && return nothing
    lower,upper = direction > 0 ? (st.lower[i],st.upper[i]) : (-st.upper[i],-st.lower[i])
    value = _strict_value(lower,upper,ws._snapshot.domain)
    if value !== nothing
        return DominanceStep(i,value,deepcopy(lower),deepcopy(upper),deepcopy(st.constant),
                             st.proof_count,:exact,length(st.callers),:strong)
    end
    if allow_weak
        wval = _weak_value(lower,upper,ws._snapshot.domain)
        wval === nothing && return nothing
        return DominanceStep(i,wval,deepcopy(lower),deepcopy(upper),deepcopy(st.constant),
                             st.proof_count,:exact,length(st.callers),:weak)
    end
    return nothing
end

function _dominance_interval_strict(ws::Workspace, i::Int, direction::Int)
    st, s = ws._state, ws._snapshot
    lo, hi = _enclose(direction * st.fields[i])
    for (j, q) in st.adjacency[i]
        st.fixed[j] == 2 || continue
        c_lo, c_hi = _enclose(direction * q)
        if s.domain === QT.BoolDomain
            a, b = min(0.0, c_lo), max(0.0, c_hi)
        else
            m = max(abs(c_lo), abs(c_hi))
            a, b = -m, m
        end
        lo = prevfloat(lo + a)
        hi = nextfloat(hi + b)
    end
    return isfinite(lo) && isfinite(hi) && _strict_value(lo, hi, s.domain) !== nothing
end

function _step_dominance_queue!(
    ws::Workspace,
    direction::Int,
    allow_weak::Bool,
    rem_work::Int,
    rem_exact::Int,
    deadline_ns;
    allow_exact_fallback::Bool=true,
)
    st = ws._state
    _expired(deadline_ns) && return (:deadline, 0, 0, 0, 0, 0)
    rem_work > 0 || return (:work_limit, 0, 0, 0, 0, 0)
    i = st.queue[st.head]
    if st.fixed[i] == 2 && direction != 0
        rem_exact > 0 || return (:verification_limit, 0, 0, 0, 0, 0)
    end
    if st.fixed[i] != 2 || direction == 0
        _pop_queue!(ws)
        return (:continue, 1, 0, 0, 0, 0)
    end
    dc, de, dx = 1, 0, 1
    step = _cached_step(ws, i, direction; allow_weak)
    if step === nothing && allow_weak
        allow_exact_fallback || return (:unsupported_arithmetic, dc, de, 0, dx, 1)
        m_step, m_reason, _, m_visits, _, m_exact = _marginal_dominance_witness(
            ws, i, nothing, nothing, direction, 0, 0,
            rem_work - dc, rem_exact - dx,
            deadline_ns, st.proof_count, length(st.callers),
        )
        de += m_visits
        dx += m_exact
        m_reason in (:work_limit, :verification_limit, :deadline) && return (m_reason, dc, de, 0, dx, 1)
        step = m_step
    end
    if step === nothing
        _pop_queue!(ws)
        return (:continue, dc, de, 0, dx, 0)
    end
    dfb = (step.persistency === :weak || step.method === :marginal || !_dominance_interval_strict(ws, i, direction)) ? 1 : 0
    (!allow_exact_fallback && dfb > 0) && return (:unsupported_arithmetic, dc, de, 0, dx, 1)
    degree = length(st.adjacency[i])
    degree <= rem_work - dc - de || return (:work_limit, dc, de, 0, dx, dfb)
    remaining = rem_exact - dx
    remaining >= 1 && degree <= (remaining - 1) ÷ 3 || return (:verification_limit, dc, de, 0, dx, dfb)
    reserved = 1 + 3 * degree
    st.serial <= typemax(UInt64) - 2 || throw(ArgumentError("trail serial exhausted; reset workspace"))
    _reserve!(st.trail, length(st.trail) + 2)
    result = _fix!(ws, i, step.value; proof=step, max_work=rem_work - dc - de, deadline_ns)
    de += result.edge_visits
    dx += reserved
    result.stop_reason === :applied || return (result.stop_reason, dc, de, 0, dx, dfb)
    _pop_queue!(ws)
    return (:applied, dc, de, 1, dx, dfb)
end

"""
    propagate!(ws; map=nothing, allow_weak=false, max_work=typemax(Int),
               max_deductions=typemax(Int), max_exact_work=typemax(Int),
               deadline_ns=nothing)

Run deterministic dominance propagation on a workspace selected with
`rules=:dominance`, optionally validating and operating through a
[`DomainGaugeMap`](@ref). By default (`allow_weak=false`), only strong strict
dominance is applied (`:strong` persistency). When `allow_weak=true`, weak
optimum-preserving restrictions are also applied sequentially on the evolving
residual so later candidates are always re-evaluated against already-applied
steps.
"""
function propagate!(ws::Workspace;map::Union{Nothing,DomainGaugeMap}=nothing,
                     allow_weak::Bool=false,
                     max_work=typemax(Int),max_deductions=typemax(Int),
                     max_exact_work=typemax(Int),deadline_ns=nothing)
    _limits(max_work,deadline_ns)
    _limits(max_deductions,deadline_ns)
    _limits(max_exact_work,deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    st.rules === :dominance || throw(ArgumentError("select Workspace(model; rules=:dominance)"))
    candidates,edges,deductions,exact = 0,0,0,0
    finish(reason) = _propagation_report!(ws,reason,candidates,edges,deductions,exact)
    direction = _direction(ws._snapshot)
    while st.head <= length(st.queue)
        _expired(deadline_ns) && return finish(:deadline)
        deductions < max_deductions || return finish(:deduction_limit)
        status, dc, de, dd, dx = _step_dominance_queue!(
            ws, direction, allow_weak,
            Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns,
        )
        candidates += dc
        edges += de
        deductions += dd
        exact += dx
        status in (:applied, :continue) || return finish(status)
    end
    return finish(:quiescent)
end

"""
    apply_dominance!(ws, label; value=nothing, map=nothing, allow_weak=false,
                     max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Certify and transactionally commit one unary dominance fixing on `ws`, recording
a [`DominanceStep`](@ref) on the reversible trail. Returns an [`UpdateReport`](@ref).
"""
function apply_dominance!(ws::Workspace, label;
                          value=nothing,
                          map::Union{Nothing,DomainGaugeMap}=nothing,
                          allow_weak::Bool=false,
                          max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws, label)
    st = ws._state
    raw_step, reason, _, visits, _, _ = _dominance_witness(
        ws, i; map, allow_weak, value, max_work, max_exact_work, deadline_ns,
        predecessors=st.proof_count, scope_length=length(st.callers),
    )
    raw_step === nothing && return UpdateReport(reason, visits, 0)
    step = if map === nothing
        raw_step
    elseif raw_step.method === :marginal
        dm = map.gauge[i] * raw_step.lower
        DominanceStep(i, raw_step.value, deepcopy(dm), deepcopy(dm), deepcopy(st.constant),
                      raw_step.predecessors, :marginal, raw_step.scope_length, raw_step.persistency)
    else
        new_lo, new_hi = _convert_step_bounds(ws._snapshot, raw_step, map, nothing)
        DominanceStep(i, raw_step.value, new_lo, new_hi, deepcopy(st.constant),
                      raw_step.predecessors, raw_step.method, raw_step.scope_length, raw_step.persistency)
    end
    rep = _fix!(ws, i, step.value; proof=step, max_work=max_work - visits, deadline_ns)
    return UpdateReport(rep.stop_reason, visits + rep.edge_visits, rep.changed)
end

"""
    contract_relation!(ws, eliminated, representative; sign=nothing, map=nothing,
                       allow_weak=false, max_work=typemax(Int),
                       max_exact_work=typemax(Int), deadline_ns=nothing)

Certify and transactionally contract `eliminated` into `representative` under
``t_{\\text{eliminated}} = \\sigma t_{\\text{representative}}``, recording a
[`RelationStep`](@ref) on the reversible trail and updating surviving fields,
degrees and adjacency in ``O(\\text{touched})`` work. Returns an [`UpdateReport`](@ref).
"""
function contract_relation!(ws::Workspace, eliminated, representative;
                            sign::Union{Nothing,Int}=nothing,
                            map::Union{Nothing,DomainGaugeMap}=nothing,
                            allow_weak::Bool=false,
                            max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    u = _variable(ws, eliminated)
    v = _variable(ws, representative)
    st = ws._state
    raw_step, reason, _, visits, _, _ = _relation_witness(
        ws, u, v; sign, map, allow_weak, max_work, max_exact_work, deadline_ns,
        predecessors=st.proof_count, scope_length=length(st.callers),
    )
    raw_step === nothing && return UpdateReport(reason, visits, 0)
    step = map === nothing ? raw_step :
        RelationStep(u, v, raw_step.orig_sign, raw_step.orig_sign,
                     deepcopy(raw_step.lower), deepcopy(raw_step.upper), deepcopy(st.constant),
                     raw_step.predecessors, raw_step.method, raw_step.scope_length, raw_step.persistency)
    const_delta, field_deltas, quad_deltas = _relation_deltas(ws, u, v, step.orig_sign)
    return _apply_reduction!(
        ws, u, Int8(3), step, const_delta, field_deltas, quad_deltas;
        max_work, deadline_ns, precharged_visits=visits,
    )
end

"""
    eliminate_variable!(ws, label; map=nothing, tie_break=:low, max_degree=2,
                        max_work=typemax(Int), max_exact_work=typemax(Int),
                        deadline_ns=nothing)

Certify and transactionally eliminate a free variable of active degree
`0..max_degree` (default `max_degree=2`) from `ws`, recording an
[`EliminationStep`](@ref) with its exact argmin reconstruction table and
updating surviving neighbor fields, fill edges and degrees on the reversible
trail. Higher-degree variables are refused with `:degree_too_high`. Returns an
[`UpdateReport`](@ref).
"""
function eliminate_variable!(ws::Workspace, label;
                             map::Union{Nothing,DomainGaugeMap}=nothing,
                             tie_break::Symbol=:low,
                             max_degree=2,
                             max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    u = _variable(ws, label)
    st = ws._state
    raw_step, reason, _, visits, _ = _elimination_witness(
        ws, u; map, tie_break, max_degree, max_work, max_exact_work, deadline_ns,
        predecessors=st.proof_count, scope_length=length(st.callers),
    )
    raw_step === nothing && return UpdateReport(reason, visits, 0)
    step = map === nothing ? raw_step :
        EliminationStep(u, raw_step.neighbors, raw_step.table,
                        deepcopy(raw_step.constant_delta), deepcopy(raw_step.linear_deltas),
                        deepcopy(raw_step.quadratic_deltas), deepcopy(st.constant),
                        raw_step.predecessors, raw_step.scope_length, raw_step.unique_argmin)
    field_deltas = Pair{Int,_Exact}[p for p in step.linear_deltas]
    quad_deltas = Tuple{Int,Int,_Exact}[t for t in step.quadratic_deltas]
    return _apply_reduction!(
        ws, u, Int8(4), step, step.constant_delta, field_deltas, quad_deltas;
        max_work, deadline_ns, precharged_visits=visits,
    )
end

_is_exact_float64(q::_Exact) = (v = Float64(q); isfinite(v) && _Exact(v) == q)
function _is_float64_exact_elimination(step::EliminationStep)
    return step.unique_argmin && _is_exact_float64(step.constant_delta) &&
           all(p -> _is_exact_float64(p.second), step.linear_deltas) &&
           all(t -> _is_exact_float64(t[3]), step.quadratic_deltas)
end

function _step_elimination_queue!(
    ws::Workspace,
    md::Int,
    mf::Int,
    map::Union{Nothing,DomainGaugeMap},
    tie_break::Symbol,
    direction::Int,
    rem_work::Int,
    rem_exact::Int,
    deadline_ns;
    min_bucket::Int=1,
    allow_exact_fallback::Bool=true,
)
    st = ws._state
    _expired(deadline_ns) && return (:deadline, 0, 0, 0, 0, 0, 0)
    rem_work > 0 || return (:work_limit, 0, 0, 0, 0, 0, 0)
    if _next_elim_bucket(st, md; min_bucket) == 0
        _requeue_deferred_elim!(ws, md, mf; min_bucket)
    end
    b = _next_elim_bucket(st, md; min_bucket)
    u = st.elim_queues[b][st.elim_heads[b]]
    if st.fixed[u] != 2 || direction == 0 || st.degrees[u] != b - 1 || (b == 4 && !iszero(_spin_field(ws, u)))
        _pop_elim_queue!(ws, b)
        return (:continue, 1, 0, 0, 0, 0, 0)
    end
    d_u = st.degrees[u]
    adj_len = length(st.adjacency[u])
    num_states = 1 << d_u
    max_quad_deltas = (d_u * (d_u - 1)) >> 1
    total_edge_need = 2 * adj_len + 2 * max_quad_deltas
    total_exact_need = num_states + 1 + 3 * d_u
    total_edge_need <= rem_work - 1 || return (:work_limit, 0, 0, 0, 0, 0, 0)
    total_exact_need <= rem_exact || return (:verification_limit, 0, 0, 0, 0, 0, 0)
    raw_step, w_reason, _, w_visits, w_exact = _elimination_witness(
        ws, u; map, tie_break, max_degree=md,
        max_work=rem_work - 1,
        max_exact_work=rem_exact,
        deadline_ns,
        predecessors=st.proof_count,
        scope_length=length(st.callers),
    )
    raw_step === nothing && return (w_reason, 1, w_visits, 0, w_exact, 0, 0)
    dfb = _is_float64_exact_elimination(raw_step) ? 0 : 1
    (!allow_exact_fallback && dfb > 0) && return (:unsupported_arithmetic, 1, w_visits, 0, w_exact, 1, 0)
    actual_fill = _elimination_fill(st, raw_step.quadratic_deltas)
    if actual_fill > mf
        _pop_elim_queue!(ws, b, actual_fill)
        return (:continue, 1, w_visits, 0, w_exact, dfb, 0)
    end
    step = map === nothing ? raw_step :
        EliminationStep(u, raw_step.neighbors, raw_step.table,
                        deepcopy(raw_step.constant_delta), deepcopy(raw_step.linear_deltas),
                        deepcopy(raw_step.quadratic_deltas), deepcopy(st.constant),
                        raw_step.predecessors, raw_step.scope_length, raw_step.unique_argmin)
    field_deltas = Pair{Int,_Exact}[p for p in step.linear_deltas]
    quad_deltas = Tuple{Int,Int,_Exact}[t for t in step.quadratic_deltas]
    st.serial <= typemax(UInt64) - 2 || throw(ArgumentError("trail serial exhausted; reset workspace"))
    _reserve!(st.trail, length(st.trail) + 2)
    rep = _apply_reduction!(
        ws, u, Int8(4), step, step.constant_delta, field_deltas, quad_deltas;
        max_work=rem_work - 1 - w_visits, deadline_ns, precharged_visits=0,
    )
    de = w_visits + rep.edge_visits
    dx = w_exact + 1 + 3 * length(step.neighbors)
    rep.stop_reason === :applied || return (rep.stop_reason, 1, de, 0, dx, dfb, 0)
    _pop_elim_queue!(ws, b)
    return (:applied, 1, de, 1, dx, dfb, actual_fill)
end

"""
    eliminate_low_degree!(ws; map=nothing, max_degree=2, max_fill=typemax(Int),
                          tie_break=:low, cascade_dominance=false,
                          allow_weak_dominance=false, max_work=typemax(Int),
                          max_deductions=typemax(Int), max_exact_work=typemax(Int),
                          deadline_ns=nothing)

Run queue-driven exact local elimination for free vertices of active degree
`0 <= degree(ws, label) <= max_degree` (default `max_degree=2`; `max_degree=3`
enables guarded zero-field degree-three Ising star–triangle reduction) without
scanning the whole graph per elimination. Eliminations that would introduce more
than `max_fill` new fill edges are skipped and deferred. When
`cascade_dominance=true` (requiring `Workspace(model; rules=:dominance)`,
`rules=:elimination`, `rules=:relations` or `rules=:mixed`), dirty dominance candidates are
interleaved with low-degree eliminations so dominance fixings that drop neighbor
degrees to `<= max_degree` and local eliminations that strengthen neighbor
derivative bounds cascade automatically. Returns a [`PropagationReport`](@ref).
"""
function eliminate_low_degree!(
    ws::Workspace;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    max_degree=2,
    max_fill=typemax(Int),
    tie_break::Symbol=:low,
    cascade_dominance::Bool=false,
    allow_weak_dominance::Bool=false,
    max_work=typemax(Int),
    max_deductions=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_deductions, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    max_degree isa Integer && !(max_degree isa Bool) && 0 <= max_degree <= 3 ||
        throw(ArgumentError("eliminate_low_degree! supports max_degree in 0..3"))
    max_fill isa Integer && !(max_fill isa Bool) && 0 <= max_fill <= typemax(Int) ||
        throw(ArgumentError("max_fill must be a nonnegative machine-sized integer"))
    tie_break in (:low, :high) || throw(ArgumentError("tie_break must be :low or :high"))
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    if cascade_dominance
        st.rules in (:dominance, :elimination, :relations, :mixed) ||
            throw(ArgumentError("cascade_dominance requires Workspace(model; rules=:dominance), rules=:elimination, rules=:relations or rules=:mixed"))
    end
    md = Int(max_degree)
    mf = Int(max_fill)
    candidates, edges, deductions, exact = 0, 0, 0, 0
    function pending_count()
        p = cascade_dominance ? (length(st.queue) - st.head + 1) : 0
        @inbounds for b in 1:(md + 1)
            p += length(st.elim_queues[b]) - st.elim_heads[b] + 1
        end
        p += _count_deferred_elim(st, md, mf)
        return p
    end
    finish(reason) = _propagation_report!(ws, reason, candidates, edges, deductions, exact;
                                          pending=pending_count())
    direction = _direction(ws._snapshot)
    while _next_elim_bucket(st, md) != 0 || _next_deferred_elim(st, md, mf) != 0 || (cascade_dominance && st.head <= length(st.queue))
        if cascade_dominance && st.head <= length(st.queue)
            _expired(deadline_ns) && return finish(:deadline)
            deductions < max_deductions || return finish(:deduction_limit)
            status, dc, de, dd, dx = _step_dominance_queue!(
                ws, direction, allow_weak_dominance,
                Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns,
            )
            candidates += dc
            edges += de
            deductions += dd
            exact += dx
            status in (:applied, :continue) || return finish(status)
            continue
        end
        _expired(deadline_ns) && return finish(:deadline)
        deductions < max_deductions || return finish(:deduction_limit)
        status, dc, de, dd, dx, _, _ = _step_elimination_queue!(
            ws, md, mf, map, tie_break, direction,
            Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns,
        )
        candidates += dc
        edges += de
        deductions += dd
        exact += dx
        status in (:applied, :continue) || return finish(status)
    end
    return finish(:quiescent)
end

function _try_contract_pair!(
    ws::Workspace,
    elim::Int,
    rep::Int,
    map::Union{Nothing,DomainGaugeMap},
    allow_weak::Bool,
    rem_work::Int,
    rem_exact::Int,
    deadline_ns;
    reserve_pop::Bool=false,
    allow_exact_fallback::Bool=true,
)
    st = ws._state
    raw_step, w_reason, _, w_visits, w_fb, w_exact = _relation_witness(
        ws, elim, rep;
        map, allow_weak,
        max_work=rem_work,
        max_exact_work=rem_exact,
        deadline_ns,
        predecessors=st.proof_count,
        scope_length=length(st.callers),
    )
    (!allow_exact_fallback && w_fb > 0 && raw_step !== nothing) &&
        return (:unsupported_arithmetic, w_visits, w_exact, w_fb)
    raw_step === nothing && return (w_reason, w_visits, w_exact, w_fb)
    d_elim = st.degrees[elim]
    adj_elim_len = length(st.adjacency[elim])
    apply_edge_need = adj_elim_len + 2 * max(0, d_elim - 1)
    apply_exact_need = 1 + 3 * d_elim
    apply_edge_need <= rem_work - w_visits || return (:work_limit, w_visits, w_exact, w_fb)
    apply_exact_need <= rem_exact - w_exact || return (:verification_limit, w_visits, w_exact, w_fb)
    step = map === nothing ? raw_step :
        RelationStep(elim, rep, raw_step.orig_sign, raw_step.orig_sign,
                     deepcopy(raw_step.lower), deepcopy(raw_step.upper), deepcopy(st.constant),
                     raw_step.predecessors, raw_step.method, raw_step.scope_length, raw_step.persistency)
    const_delta, field_deltas, quad_deltas = _relation_deltas(ws, elim, rep, step.orig_sign)
    trail_extra = reserve_pop ? 2 : 1
    st.serial <= typemax(UInt64) - UInt64(trail_extra) ||
        throw(ArgumentError("trail serial exhausted; reset workspace"))
    _reserve!(st.trail, length(st.trail) + trail_extra)
    rep_apply = _apply_reduction!(
        ws, elim, Int8(3), step, const_delta, field_deltas, quad_deltas;
        max_work=rem_work - w_visits, deadline_ns, precharged_visits=0,
    )
    return (rep_apply.stop_reason, w_visits + rep_apply.edge_visits, w_exact + apply_exact_need, w_fb)
end

function _step_relation_queue!(
    ws::Workspace,
    mf::Int,
    map::Union{Nothing,DomainGaugeMap},
    allow_weak::Bool,
    direction::Int,
    rem_work::Int,
    rem_exact::Int,
    deadline_ns;
    allow_exact_fallback::Bool=true,
)
    st = ws._state
    _expired(deadline_ns) && return (:deadline, 0, 0, 0, 0, 0, 0)
    rem_work > 0 || return (:work_limit, 0, 0, 0, 0, 0, 0)
    if st.rel_head > length(st.rel_queue)
        _requeue_deferred_rel!(ws, mf, allow_weak)
    end
    u = st.rel_queue[st.rel_head]
    if st.fixed[u] != 2 || direction == 0 || st.degrees[u] == 0
        _pop_rel_queue!(ws)
        return (:continue, 1, 0, 0, 0, 0, 0)
    end
    adj_u_len = length(st.adjacency[u])
    adj_u_len <= rem_work - 1 || return (:work_limit, 0, 0, 0, 0, 0, 0)
    nbrs = Int[]
    for (w, q) in st.adjacency[u]
        _expired(deadline_ns) && return (:deadline, 0, 0, 0, 0, 0, 0)
        if st.fixed[w] == 2 && !iszero(q)
            push!(nbrs, w)
        end
    end
    sort!(nbrs)
    u_visits = 0
    u_exact = 0
    u_fb = 0
    called_witness = false
    min_blocked = typemax(Int)
    for v in nbrs
        f_uv = _contraction_fill(st, u, v)
        if f_uv <= mf
            called_witness = true
            status, dv, dx, dfb = _try_contract_pair!(
                ws, u, v, map, allow_weak,
                rem_work - 1 - u_visits,
                rem_exact - u_exact,
                deadline_ns;
                reserve_pop=true,
                allow_exact_fallback,
            )
            u_visits += dv
            u_exact += dx
            u_fb += dfb
            if status === :applied
                _pop_rel_queue!(ws)
                return (:applied, 1, u_visits, 1, u_exact, u_fb, f_uv)
            elseif status !== :not_strict
                return (status, 1, u_visits, 0, u_exact, u_fb, 0)
            end
        else
            min_blocked = min(min_blocked, f_uv)
        end
    end
    for v in nbrs
        f_uv = _contraction_fill(st, u, v)
        f_vu = _contraction_fill(st, v, u)
        if f_vu <= mf && (f_uv > mf || !st.rel_queued[v])
            called_witness = true
            status, dv, dx, dfb = _try_contract_pair!(
                ws, v, u, map, allow_weak,
                rem_work - 1 - u_visits,
                rem_exact - u_exact,
                deadline_ns;
                reserve_pop=false,
                allow_exact_fallback,
            )
            u_visits += dv
            u_exact += dx
            u_fb += dfb
            if status === :applied
                return (:applied, 1, u_visits, 1, u_exact, u_fb, f_vu)
            elseif status !== :not_strict
                return (status, 1, u_visits, 0, u_exact, u_fb, 0)
            end
        elseif f_vu > mf
            min_blocked = min(min_blocked, f_vu)
        end
    end
    _pop_rel_queue!(ws, min_blocked, allow_weak)
    return (:continue, 1, called_witness ? u_visits : adj_u_len, 0, u_exact, u_fb, 0)
end

"""
    contract_relations!(ws; map=nothing, allow_weak=false,
                        cascade_dominance=false, allow_weak_dominance=false,
                        max_fill=typemax(Int), max_work=typemax(Int),
                        max_deductions=typemax(Int), max_exact_work=typemax(Int),
                        deadline_ns=nothing)

Run queue-driven certified pair relation detection and signed contraction on `ws`
without scanning all vertex pairs globally. Candidate active vertices are popped
from an incremental relation queue and their active incident edges are tested for
certified pair equivalences or implications (`:interval`, `:exact` or `:glk_pair`).
Contractions that would introduce more than `max_fill` new fill edges on the
representative are skipped. When `cascade_dominance=true` (requiring
`Workspace(model; rules=:dominance)`, `rules=:elimination`, `rules=:relations` or
`rules=:mixed`), dirty unary dominance candidates are interleaved with relation
contractions. Returns a [`PropagationReport`](@ref).
"""
function contract_relations!(
    ws::Workspace;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    cascade_dominance::Bool=false,
    allow_weak_dominance::Bool=false,
    max_fill=typemax(Int),
    max_work=typemax(Int),
    max_deductions=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_deductions, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    max_fill isa Integer && !(max_fill isa Bool) && 0 <= max_fill <= typemax(Int) ||
        throw(ArgumentError("max_fill must be a nonnegative machine-sized integer"))
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    if cascade_dominance
        st.rules in (:dominance, :elimination, :relations, :mixed) ||
            throw(ArgumentError("cascade_dominance requires Workspace(model; rules=:dominance), rules=:elimination, rules=:relations or rules=:mixed"))
    end
    mf = Int(max_fill)
    candidates, edges, deductions, exact = 0, 0, 0, 0
    function pending_count()
        p = cascade_dominance ? (length(st.queue) - st.head + 1) : 0
        p += (length(st.rel_queue) - st.rel_head + 1) + _count_deferred_rel(st, mf, allow_weak)
        return p
    end
    finish(reason) = _propagation_report!(ws, reason, candidates, edges, deductions, exact;
                                          pending=pending_count())
    direction = _direction(ws._snapshot)
    while st.rel_head <= length(st.rel_queue) || _next_deferred_rel(st, mf, allow_weak) != 0 ||
          (cascade_dominance && st.head <= length(st.queue))
        if cascade_dominance && st.head <= length(st.queue)
            _expired(deadline_ns) && return finish(:deadline)
            deductions < max_deductions || return finish(:deduction_limit)
            status, dc, de, dd, dx = _step_dominance_queue!(
                ws, direction, allow_weak_dominance,
                Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns,
            )
            candidates += dc
            edges += de
            deductions += dd
            exact += dx
            status in (:applied, :continue) || return finish(status)
            continue
        end
        _expired(deadline_ns) && return finish(:deadline)
        deductions < max_deductions || return finish(:deduction_limit)
        status, dc, de, dd, dx, _, _ = _step_relation_queue!(
            ws, mf, map, allow_weak, direction,
            Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns,
        )
        candidates += dc
        edges += de
        deductions += dd
        exact += dx
        status in (:applied, :continue) || return finish(status)
    end
    return finish(:quiescent)
end

"""
    SchedulePassSummary

Per-pass execution summary recorded by [`schedule_reductions!`](@ref): `pass`
(`:dominance`, `:elimination`, `:star_triangle` or `:relations`), `stop_reason`,
examined `candidates`, `edge_visits`, committed `deductions`, reserved/executed
`exact_work`, `exact_fallbacks`, and new `fill_edges` added during the pass.
"""
struct SchedulePassSummary
    pass::Symbol
    stop_reason::Symbol
    candidates::Int
    edge_visits::Int
    deductions::Int
    exact_work::Int
    exact_fallbacks::Int
    fill_edges::Int
end

"""
    ScheduleReport

Bounded mixed-pass scheduling report returned by [`schedule_reductions!`](@ref).
Retains `generation`, `checkpoint`, `stop_reason` (`:quiescent`, `:work_limit`,
`:verification_limit`, `:deduction_limit`, `:deadline`, `:unsupported_arithmetic`,
`:fill_limit` or `:optional_pass_disabled`), total `candidates`, `edge_visits`,
`deductions`, `exact_work`, `exact_fallbacks`, `pending`, cumulative `totals`,
per-family deduction counts (`dominance_deductions`, `elimination_deductions`,
`star_triangle_deductions`, `relation_deductions`), total introduced `fill_edges`,
initial/residual graph sizes (`initial_variables`, `residual_variables`,
`initial_edges`, `residual_edges`), ordered `passes::Vector{SchedulePassSummary}`,
and `optional_passes_disabled`.
"""
struct ScheduleReport
    generation::Generation
    checkpoint::Checkpoint
    stop_reason::Symbol
    candidates::Int
    edge_visits::Int
    deductions::Int
    exact_work::Int
    exact_fallbacks::Int
    pending::Int
    totals::NamedTuple{(:candidates,:edge_visits,:exact_work),Tuple{Int,Int,Int}}
    dominance_deductions::Int
    elimination_deductions::Int
    star_triangle_deductions::Int
    relation_deductions::Int
    fill_edges::Int
    initial_variables::Int
    residual_variables::Int
    initial_edges::Int
    residual_edges::Int
    passes::Vector{SchedulePassSummary}
    optional_passes_disabled::Tuple{Vararg{Symbol}}
end
generation(r::ScheduleReport) = r.generation

function _has_fill_blocked_elim(ws::Workspace, b::Int, mf::Int)
    st = ws._state
    @inbounds for u in st.elim_deferred[b]
        if st.fixed[u] == 2 && st.degrees[u] == b - 1 && !st.elim_queued[b][u] &&
           (b < 4 || iszero(_spin_field(ws, u))) &&
           mf < st.elim_blocked_fill[b][u] < typemax(Int)
            return true
        end
    end
    return false
end

function _has_active_fill_blocked(
    ws::Workspace,
    enable_elimination::Bool,
    enable_star_triangle::Bool,
    enable_relations::Bool,
    mf::Int,
)
    st = ws._state
    if enable_elimination
        for b in 1:3
            _has_fill_blocked_elim(ws, b, mf) && return true
        end
    end
    enable_star_triangle && _has_fill_blocked_elim(ws, 4, mf) && return true
    if enable_relations
        @inbounds for u in st.rel_deferred
            if st.fixed[u] == 2 && st.degrees[u] >= 1 && !st.rel_queued[u] &&
               mf < st.rel_blocked_fill[u] < typemax(Int)
                return true
            end
        end
    end
    return false
end

function _has_star_candidate(ws::Workspace, mf::Int)
    st = ws._state
    q = st.elim_queues[4]
    idx = max(st.elim_heads[4], st.star_hint)
    @inbounds while idx <= length(q)
        u = q[idx]
        if st.fixed[u] == 2 && st.degrees[u] == 3 && iszero(_spin_field(ws, u))
            st.star_hint = idx
            return true
        end
        idx += 1
    end
    st.star_hint = idx
    return _next_deferred_elim(st, 3, mf; min_bucket=4) != 0
end

function _has_rel_candidate(st::_Incremental, mf::Int, allow_weak::Bool)
    st.active_edges > 0 || return false
    idx = max(st.rel_head, st.rel_hint)
    @inbounds while idx <= length(st.rel_queue)
        u = st.rel_queue[idx]
        if st.fixed[u] == 2 && st.degrees[u] >= 1
            st.rel_hint = idx
            return true
        end
        idx += 1
    end
    st.rel_hint = idx
    return _next_deferred_rel(st, mf, allow_weak) != 0
end

function _disabled_optional_passes_with_work(
    ws::Workspace,
    enable_dominance::Bool,
    enable_elimination::Bool,
    enable_star_triangle::Bool,
    enable_relations::Bool,
    mf::Int,
    allow_weak_relations::Bool,
)
    st = ws._state
    out = Symbol[]
    if !enable_dominance && length(st.fixes) < length(st.fixed) && st.head <= length(st.queue)
        push!(out, :dominance)
    end
    if !enable_elimination && (_next_elim_bucket(st, 2) != 0 || _next_deferred_elim(st, 2, mf) != 0)
        push!(out, :elimination)
    end
    if !enable_star_triangle && _has_star_candidate(ws, mf)
        push!(out, :star_triangle)
    end
    if !enable_relations && _has_rel_candidate(st, mf, allow_weak_relations)
        push!(out, :relations)
    end
    return Tuple(out)
end

"""
    schedule_reductions!(ws; map=nothing, enable_dominance=true,
                         enable_elimination=true, enable_relations=true,
                         enable_star_triangle=false, allow_weak_dominance=false,
                         allow_weak_relations=false, allow_exact_fallback=true,
                         stop_on_disabled_optional=false, tie_break=:low,
                         max_fill=typemax(Int), max_total_fill=typemax(Int),
                         relation_work_budget=typemax(Int), max_work=typemax(Int),
                         max_deductions=typemax(Int), max_exact_work=typemax(Int),
                         deadline_ns=nothing)

Run a deterministic mixed exact reduction schedule on one shared [`Workspace`](@ref)
and [`Generation`](@ref) without alternating full QUBO↔Ising materializations.
Cheap dirty-neighborhood unary propagation (`:dominance`) and degree-`<= 2` local
elimination (`:elimination`) run first; heavier passes (`:star_triangle` at degree 3,
disabled by default, and `:relations` bounded by `relation_work_budget` and
`max_fill` / `max_total_fill`) run only when cheap passes are quiescent, and
immediately cascade back to cheap passes whenever a reduction dirties a local
neighborhood. Returns a [`ScheduleReport`](@ref).
"""
function schedule_reductions!(
    ws::Workspace;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    enable_dominance::Bool=true,
    enable_elimination::Bool=true,
    enable_relations::Bool=true,
    enable_star_triangle::Bool=false,
    allow_weak_dominance::Bool=false,
    allow_weak_relations::Bool=false,
    allow_exact_fallback::Bool=true,
    stop_on_disabled_optional::Bool=false,
    tie_break::Symbol=:low,
    max_fill=typemax(Int),
    max_total_fill=typemax(Int),
    relation_work_budget=typemax(Int),
    max_work=typemax(Int),
    max_deductions=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_deductions, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    _limits(max_fill, deadline_ns)
    _limits(max_total_fill, deadline_ns)
    _limits(relation_work_budget, deadline_ns)
    tie_break in (:low, :high) || throw(ArgumentError("tie_break must be :low or :high"))
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    st.rules in (:dominance, :elimination, :relations, :mixed) ||
        throw(ArgumentError("schedule_reductions! requires Workspace(model; rules=:mixed), :dominance, :elimination or :relations"))
    mf_cap = Int(max_fill)
    mtf_cap = Int(max_total_fill)
    rel_budget = Int(relation_work_budget)
    candidates = edges = deductions = exact = exact_fallbacks = 0
    dom_ded = elim_ded = star_ded = rel_ded = 0
    total_fill = 0
    rel_work_used = 0
    passes = SchedulePassSummary[]
    eff_fill() = max(0, min(mf_cap, mtf_cap - total_fill))
    function pending_count()
        ef = eff_fill()
        p = enable_dominance ? (length(st.queue) - st.head + 1) : 0
        if enable_elimination
            for b in 1:3
                p += length(st.elim_queues[b]) - st.elim_heads[b] + 1
            end
            p += _count_deferred_elim(st, 2, ef)
        end
        if enable_star_triangle
            p += length(st.elim_queues[4]) - st.elim_heads[4] + 1
            p += _count_deferred_elim(st, 3, ef; min_bucket=4)
        end
        if enable_relations
            p += (length(st.rel_queue) - st.rel_head + 1) + _count_deferred_rel(st, ef, allow_weak_relations)
        end
        return p
    end
    function finish(reason, disabled=nothing)
        st.total_candidates += candidates
        st.total_edges += edges
        st.total_exact += exact
        n_init = length(ws._snapshot.labels)
        n_res = n_init - length(st.fixes)
        dis = disabled === nothing ?
            _disabled_optional_passes_with_work(
                ws, enable_dominance, enable_elimination, enable_star_triangle,
                enable_relations, eff_fill(), allow_weak_relations,
            ) : disabled
        return ScheduleReport(
            generation(ws),
            checkpoint(ws),
            reason,
            candidates,
            edges,
            deductions,
            exact,
            exact_fallbacks,
            pending_count(),
            (candidates=st.total_candidates, edge_visits=st.total_edges, exact_work=st.total_exact),
            dom_ded,
            elim_ded,
            star_ded,
            rel_ded,
            total_fill,
            n_init,
            n_res,
            st.initial_edges,
            st.active_edges,
            passes,
            dis,
        )
    end
    !enable_dominance && !enable_elimination && !enable_relations && !enable_star_triangle &&
        return finish(:optional_pass_disabled)
    direction = _direction(ws._snapshot)
    (direction == 0 && length(st.fixes) < length(st.fixed)) &&
        return finish(:unsupported_arithmetic)
    while true
        ef = eff_fill()
        if enable_dominance && st.head <= length(st.queue)
            p_cand = p_edges = p_ded = p_exact = p_fb = 0
            p_reason = :quiescent
            while st.head <= length(st.queue)
                if deductions >= max_deductions
                    p_reason = :deduction_limit
                    break
                end
                status, dc, de, dd, dx, dfb = _step_dominance_queue!(
                    ws, direction, allow_weak_dominance,
                    Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns;
                    allow_exact_fallback,
                )
                candidates += dc; edges += de; deductions += dd; exact += dx; exact_fallbacks += dfb
                dom_ded += dd
                p_cand += dc; p_edges += de; p_ded += dd; p_exact += dx; p_fb += dfb
                if !(status in (:applied, :continue))
                    p_reason = status
                    break
                end
            end
            push!(passes, SchedulePassSummary(:dominance, p_reason, p_cand, p_edges, p_ded, p_exact, p_fb, 0))
            p_reason === :quiescent || return finish(p_reason)
            continue
        elseif enable_elimination && (_next_elim_bucket(st, 2) != 0 || _next_deferred_elim(st, 2, ef) != 0)
            p_cand = p_edges = p_ded = p_exact = p_fb = p_fill = 0
            p_reason = :quiescent
            while _next_elim_bucket(st, 2) != 0 || _next_deferred_elim(st, 2, eff_fill()) != 0
                (enable_dominance && st.head <= length(st.queue) && p_ded > 0) && break
                if deductions >= max_deductions
                    p_reason = :deduction_limit
                    break
                end
                status, dc, de, dd, dx, dfb, dfill = _step_elimination_queue!(
                    ws, 2, eff_fill(), map, tie_break, direction,
                    Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns;
                    min_bucket=1, allow_exact_fallback,
                )
                candidates += dc; edges += de; deductions += dd; exact += dx; exact_fallbacks += dfb; total_fill += dfill
                elim_ded += dd
                p_cand += dc; p_edges += de; p_ded += dd; p_exact += dx; p_fb += dfb; p_fill += dfill
                if !(status in (:applied, :continue))
                    p_reason = status
                    break
                end
            end
            push!(passes, SchedulePassSummary(:elimination, p_reason, p_cand, p_edges, p_ded, p_exact, p_fb, p_fill))
            p_reason === :quiescent || return finish(p_reason)
            continue
        elseif enable_star_triangle && (_next_elim_bucket(st, 3; min_bucket=4) != 0 || _next_deferred_elim(st, 3, ef; min_bucket=4) != 0)
            p_cand = p_edges = p_ded = p_exact = p_fb = p_fill = 0
            p_reason = :quiescent
            while p_ded == 0 && (_next_elim_bucket(st, 3; min_bucket=4) != 0 || _next_deferred_elim(st, 3, eff_fill(); min_bucket=4) != 0)
                if deductions >= max_deductions
                    p_reason = :deduction_limit
                    break
                end
                status, dc, de, dd, dx, dfb, dfill = _step_elimination_queue!(
                    ws, 3, eff_fill(), map, tie_break, direction,
                    Int(max_work - candidates - edges), Int(max_exact_work - exact), deadline_ns;
                    min_bucket=4, allow_exact_fallback,
                )
                candidates += dc; edges += de; deductions += dd; exact += dx; exact_fallbacks += dfb; total_fill += dfill
                star_ded += dd
                p_cand += dc; p_edges += de; p_ded += dd; p_exact += dx; p_fb += dfb; p_fill += dfill
                if !(status in (:applied, :continue))
                    p_reason = status
                    break
                end
            end
            push!(passes, SchedulePassSummary(:star_triangle, p_reason, p_cand, p_edges, p_ded, p_exact, p_fb, p_fill))
            p_reason === :quiescent || return finish(p_reason)
            continue
        elseif enable_relations && (st.rel_head <= length(st.rel_queue) || _next_deferred_rel(st, ef, allow_weak_relations) != 0)
            p_cand = p_edges = p_ded = p_exact = p_fb = p_fill = 0
            p_reason = :quiescent
            while p_ded == 0 && (st.rel_head <= length(st.rel_queue) || _next_deferred_rel(st, eff_fill(), allow_weak_relations) != 0)
                if deductions >= max_deductions
                    p_reason = :deduction_limit
                    break
                end
                rem_rel_work = min(Int(max_work - candidates - edges), rel_budget - rel_work_used)
                status, dc, de, dd, dx, dfb, dfill = _step_relation_queue!(
                    ws, eff_fill(), map, allow_weak_relations, direction,
                    rem_rel_work, Int(max_exact_work - exact), deadline_ns;
                    allow_exact_fallback,
                )
                candidates += dc; edges += de; deductions += dd; exact += dx; exact_fallbacks += dfb; total_fill += dfill
                rel_work_used += dc + de
                rel_ded += dd
                p_cand += dc; p_edges += de; p_ded += dd; p_exact += dx; p_fb += dfb; p_fill += dfill
                if !(status in (:applied, :continue))
                    p_reason = status
                    break
                end
            end
            push!(passes, SchedulePassSummary(:relations, p_reason, p_cand, p_edges, p_ded, p_exact, p_fb, p_fill))
            p_reason === :quiescent || return finish(p_reason)
            continue
        else
            break
        end
    end
    _has_active_fill_blocked(ws, enable_elimination, enable_star_triangle, enable_relations, eff_fill()) &&
        return finish(:fill_limit)
    disabled = _disabled_optional_passes_with_work(
        ws, enable_dominance, enable_elimination, enable_star_triangle,
        enable_relations, eff_fill(), allow_weak_relations,
    )
    (stop_on_disabled_optional && !isempty(disabled)) &&
        return finish(:optional_pass_disabled, disabled)
    return finish(:quiescent, disabled)
end

"""
    PhaseAccounting

Per-phase work, exact-arithmetic, fallback, allocation and wall-time accounting
for one preprocessing lifecycle boundary (`:conversion_import`, `:discovery`,
`:arithmetic_fallback`, `:verification`, `:export`, `:reconstruction`,
`:rollback_replay`).
"""
struct PhaseAccounting
    phase::Symbol
    stop_reason::Symbol
    work_units::Int
    exact_work::Int
    exact_fallbacks::Int
    bytes_allocated::Int
    elapsed_ns::UInt64
end

"""
    PipelineAccounting

Complete end-to-end accounting across all seven preprocessing lifecycle phases
(`conversion_import`, `discovery`, `arithmetic_fallback`, `verification`,
`export_phase`, `reconstruction`, `rollback_replay`), together with initial and
residual graph dimensions (`initial_variables`, `residual_variables`,
`initial_edges`, `residual_edges`), introduced `fill_edges`, `verified`
certificate status, and the underlying `report` ([`ScheduleReport`](@ref),
[`PropagationReport`](@ref) or [`IdentityReport`](@ref)).
"""
struct PipelineAccounting
    generation::Generation
    rules::Symbol
    stop_reason::Symbol
    initial_variables::Int
    residual_variables::Int
    initial_edges::Int
    residual_edges::Int
    fill_edges::Int
    conversion_import::PhaseAccounting
    discovery::PhaseAccounting
    arithmetic_fallback::PhaseAccounting
    verification::PhaseAccounting
    export_phase::PhaseAccounting
    reconstruction::PhaseAccounting
    rollback_replay::PhaseAccounting
    report::Union{Nothing,ScheduleReport,PropagationReport,IdentityReport}
    verified::Bool
end
generation(a::PipelineAccounting) = a.generation

"""
    audit_pipeline!(model_or_ws; rules=:mixed, domain=nothing, gauge=nothing,
                    residual_state=nothing, exercise_rollback_replay=true,
                    max_work=typemax(Int), max_exact_work=typemax(Int),
                    deadline_ns=nothing, kwargs...)

Execute and account for all seven preprocessing lifecycle phases
(`conversion_import`, `discovery`, `arithmetic_fallback`, `verification`,
`export_phase`, `reconstruction`, `rollback_replay`) under shared `max_work`,
`max_exact_work` and `deadline_ns` budgets. Returns `(ws, PipelineAccounting)`.
"""
function audit_pipeline!(
    model_or_ws;
    rules::Symbol=:mixed,
    domain::Union{Nothing,Symbol}=nothing,
    gauge=nothing,
    residual_state=nothing,
    exercise_rollback_replay::Bool=true,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
    kwargs...,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    rem_work = Int(max_work)
    rem_exact = Int(max_exact_work)
    zero_phase(p, r=:not_run) = PhaseAccounting(p, r, 0, 0, 0, 0, UInt64(0))

    # 1. Conversion / import phase
    t0 = time_ns()
    ws = nothing
    map = nothing
    import_units = 0
    import_reason = :applied
    import_bytes = @allocated begin
        if _expired(deadline_ns)
            import_reason = :deadline
        else
            import_units = model_or_ws isa Workspace ?
                (length(model_or_ws._snapshot.labels) + model_or_ws._state.initial_edges + 1) :
                (QT.dimension(model_or_ws) + length(QT.quadratic_terms(model_or_ws)) + 1)
            if import_units > rem_work
                import_reason = :work_limit
            else
                ws = model_or_ws isa Workspace ? model_or_ws : Workspace(model_or_ws; rules)
                if domain !== nothing || gauge !== nothing
                    dom = something(domain, _domain_symbol(ws._snapshot.domain))
                    map = domain_map(ws; domain=dom, gauge)
                    import_units += length(ws._snapshot.labels)
                end
            end
        end
    end
    import_ns = time_ns() - t0
    if import_reason !== :applied
        gen = ws === nothing ? Generation(uuid4(), uuid4()) : generation(ws)
        conv_ph = PhaseAccounting(:conversion_import, import_reason, 0, 0, 0, import_bytes, import_ns)
        return ws, PipelineAccounting(
            gen, rules, import_reason, 0, 0, 0, 0, 0,
            conv_ph, zero_phase(:discovery), zero_phase(:arithmetic_fallback),
            zero_phase(:verification), zero_phase(:export), zero_phase(:reconstruction),
            zero_phase(:rollback_replay), nothing, false,
        )
    end
    rem_work = max(0, rem_work - import_units)
    conv_ph = PhaseAccounting(:conversion_import, :applied, import_units, 0, 0, import_bytes, import_ns)

    # 2. Rollback / replay phase (at clean root before discovery if requested)
    t_rr0 = time_ns()
    rr_units = 0
    rr_reason = :applied
    rr_bytes = @allocated begin
        if exercise_rollback_replay && isempty(ws._state.fixes) && length(ws._snapshot.labels) >= 2
            l1, l2 = ws._snapshot.labels[1], ws._snapshot.labels[2]
            low = ws._snapshot.domain === QT.BoolDomain ? 0 : -1
            for (op, lbl) in ((:assume, l1), (:assume, l2), (:unfix, l1), (:unfix, l2))
                r_op = op === :assume ?
                    assume!(ws, lbl, low; max_work=max(0, rem_work - rr_units), deadline_ns) :
                    unfix!(ws, lbl; max_work=max(0, rem_work - rr_units), deadline_ns)
                rr_units += r_op.edge_visits + 1
                if r_op.stop_reason !== :applied
                    rr_reason = r_op.stop_reason
                    rollback!(ws, _checkpoint_at(ws, 0))
                    break
                end
            end
        end
    end
    rr_ns = time_ns() - t_rr0
    rem_work = max(0, rem_work - rr_units)
    if rr_reason !== :applied
        n_init = length(ws._snapshot.labels)
        n_res = n_init - length(ws._state.fixes)
        rr_ph = PhaseAccounting(:rollback_replay, rr_reason, rr_units, 0, 0, rr_bytes, rr_ns)
        return ws, PipelineAccounting(
            generation(ws), ws._state.rules, rr_reason,
            n_init, n_res, ws._state.initial_edges, ws._state.active_edges, 0,
            conv_ph, zero_phase(:discovery), zero_phase(:arithmetic_fallback),
            zero_phase(:verification), zero_phase(:export), zero_phase(:reconstruction),
            rr_ph, nothing, false,
        )
    end

    # 3. Discovery & arithmetic fallback phases
    t_d0 = time_ns()
    rep = nothing
    d_bytes = @allocated begin
        rep = if ws._state.rules === :mixed
            schedule_reductions!(ws; map, max_work=rem_work, max_exact_work=rem_exact, deadline_ns, kwargs...)
        elseif ws._state.rules === :dominance
            propagate!(ws; map, max_work=rem_work, max_exact_work=rem_exact, deadline_ns, kwargs...)
        elseif ws._state.rules === :elimination
            eliminate_low_degree!(ws; map, max_work=rem_work, max_exact_work=rem_exact, deadline_ns, kwargs...)
        elseif ws._state.rules === :relations
            contract_relations!(ws; map, max_work=rem_work, max_exact_work=rem_exact, deadline_ns, kwargs...)
        else
            IdentityReport(generation(ws), :identity, :quiescent, 0, 0)
        end
    end
    d_ns = time_ns() - t_d0
    d_units = rep isa IdentityReport ? 0 : (rep.candidates + rep.edge_visits)
    d_exact = rep isa IdentityReport ? 0 : rep.exact_work
    d_fb = rep isa ScheduleReport ? rep.exact_fallbacks : 0
    d_fill = rep isa ScheduleReport ? rep.fill_edges : 0
    rem_work = max(0, rem_work - d_units)
    rem_exact = max(0, rem_exact - d_exact)
    disc_ph = PhaseAccounting(:discovery, rep.stop_reason, d_units, d_exact, d_fb, d_bytes, d_ns)
    fb_ph = PhaseAccounting(:arithmetic_fallback, rep.stop_reason, d_exact, d_exact, d_fb, 0, UInt64(0))

    # Exercise post-discovery LIFO checkpoint + rollback if any free variable remains
    if exercise_rollback_replay && rr_reason === :applied
        free_idx = findfirst(==(2), ws._state.fixed)
        if free_idx !== nothing && rem_work > ws._state.degrees[free_idx]
            t_rr1 = time_ns()
            rr_b2 = @allocated begin
                cp_post = checkpoint(ws)
                low = ws._snapshot.domain === QT.BoolDomain ? 0 : -1
                r_post = assume!(ws, ws._snapshot.labels[free_idx], low; max_work=rem_work, deadline_ns)
                rr_units += r_post.edge_visits + 1
                rem_work = max(0, rem_work - (r_post.edge_visits + 1))
                rollback!(ws, cp_post; report=true)
                rr_units += ws._state.degrees[free_idx] + 1
                rem_work = max(0, rem_work - (ws._state.degrees[free_idx] + 1))
            end
            rr_bytes += rr_b2
            rr_ns += (time_ns() - t_rr1)
        end
    end
    rr_ph = PhaseAccounting(:rollback_replay, rr_reason, rr_units, 0, 0, rr_bytes, rr_ns)

    # 4. Verification phase
    t_v0 = time_ns()
    ver_valid = true
    ver_units = 0
    ver_reason = :verified
    ver_bytes = @allocated begin
        cert = export_certificate(ws; map)
        if cert !== nothing
            vres = verify_certificate(ws, cert; map, max_work=rem_work, deadline_ns)
            ver_units = vres.term_visits
            ver_valid = vres.valid
            ver_reason = vres.stop_reason
        end
    end
    ver_ns = time_ns() - t_v0
    rem_work = max(0, rem_work - ver_units)
    ver_ph = PhaseAccounting(:verification, ver_reason, ver_units, ver_units, 0, ver_bytes, ver_ns)

    # 5. Export phase
    t_e0 = time_ns()
    exported = nothing
    exp_units = length(ws._snapshot.labels) + ws._state.active_edges + 1
    exp_reason = :certified
    exp_bytes = @allocated begin
        if _expired(deadline_ns) || exp_units > rem_work
            exp_reason = _expired(deadline_ns) ? :deadline : :work_limit
        else
            ctype = (isempty(ws._state.fixes) && map === nothing) ? Float64 : _Exact
            exported = materialize(ws; coefficient_type=ctype, map)
            export_model(exported)
        end
    end
    exp_ns = time_ns() - t_e0
    exp_ph = PhaseAccounting(:export, exp_reason, exp_reason === :certified ? exp_units : 0, 0, 0, exp_bytes, exp_ns)
    exp_reason === :certified && (rem_work = max(0, rem_work - exp_units))

    # 6. Reconstruction phase
    t_r0 = time_ns()
    rec_units = length(ws._snapshot.labels) + ws._state.initial_edges + 1
    rec_reason = :reconstructed
    rec_bytes = @allocated begin
        if exported === nothing || _expired(deadline_ns) || rec_units > rem_work
            rec_reason = exported === nothing ? :not_run : (_expired(deadline_ns) ? :deadline : :work_limit)
            rec_units = 0
        else
            n_free = length(ws._snapshot.labels) - length(ws._state.fixes)
            target_dom = map === nothing ? _domain_symbol(ws._snapshot.domain) : map.target_domain
            low_t = target_dom === :bool ? 0 : -1
            y_state = residual_state === nothing ? fill(low_t, n_free) : residual_state
            rec = reconstruct(exported, y_state)
            rec_reason = rec.energy.finite ? :reconstructed : :nonfinite_energy
        end
    end
    rec_ns = time_ns() - t_r0
    rec_ph = PhaseAccounting(:reconstruction, rec_reason, rec_units, 0, 0, rec_bytes, rec_ns)

    n_init = length(ws._snapshot.labels)
    n_res = n_init - length(ws._state.fixes)
    overall_reason = !ver_valid ? ver_reason :
                     exp_reason !== :certified ? exp_reason :
                     !(rec_reason in (:reconstructed, :not_run)) ? rec_reason :
                     rep.stop_reason
    return ws, PipelineAccounting(
        generation(ws),
        ws._state.rules,
        overall_reason,
        n_init,
        n_res,
        ws._state.initial_edges,
        ws._state.active_edges,
        d_fill,
        conv_ph,
        disc_ph,
        fb_ph,
        ver_ph,
        exp_ph,
        rec_ph,
        rr_ph,
        rep,
        ver_valid,
    )
end

function _resolve_relation_index(st::_Incremental, i::Int)
    curr = i
    orig_σ = 1
    while st.fixed[curr] == 3
        pos = st.entries[curr]
        pos > 0 || throw(ArgumentError("missing trail entry for relation-contracted variable"))
        entry = st.trail[pos]::_UndoReduction
        step = entry.proof::RelationStep
        orig_σ *= step.orig_sign
        curr = step.representative
    end
    return curr, orig_σ
end

"""
    relation_map(ws; map=nothing)
    relation_map(ws, label; map=nothing)

Read-only query returning the current representative label and relative parity
sign (`rep_label => sign` with `sign in (-1, 1)`) induced by active
[`RelationStep`](@ref) contractions on `ws`, without mutating or path-compressing
trail state during exploratory branches. With one argument `ws`, returns an
owned `Vector{Pair{V,Int}}` in original variable order; with `(ws, label)`,
resolves a single original variable in ``O(\\text{chain depth})`` work. When
`map::DomainGaugeMap` is supplied, the parity sign is expressed in `map`'s
gauged coordinate system.
"""
function relation_map(ws::Workspace; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map; full=true)
    s, st = ws._snapshot, ws._state
    labels = original_variables(ws)
    V = s.label_type
    out = Vector{Pair{V,Int}}(undef, length(labels))
    for i in eachindex(labels)
        rep, orig_σ = _resolve_relation_index(st, i)
        σ = map === nothing ? orig_σ : (map.gauge[i] * map.gauge[rep] * orig_σ)
        out[i] = labels[rep] => σ
    end
    return out
end

function relation_map(ws::Workspace, label; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws, label)
    s, st = ws._snapshot, ws._state
    rep, orig_σ = _resolve_relation_index(st, i)
    σ = map === nothing ? orig_σ : (map.gauge[i] * map.gauge[rep] * orig_σ)
    rep_label = _owned_labels(s.label_type[s.labels[rep]])[1]
    return rep_label => σ
end

"""
    apply_weak_batch!(ws, candidates; map=nothing, atomic=false,
                      max_work=typemax(Int), max_exact_work=typemax(Int),
                      deadline_ns=nothing)

Sequentially validate and apply a collection of candidate weak restrictions
(`label => value` pairs or `label` entries) against the evolving conditioned
residual of `ws`. Because weak persistency is not closed under simultaneous
application, each candidate is re-certified after earlier candidates update the
residual. When `atomic=true`, any rejected candidate rolls back the entire batch
to its entry checkpoint.
"""
function apply_weak_batch!(ws::Workspace, candidates;
                           map::Union{Nothing,DomainGaugeMap}=nothing,
                           atomic::Bool=false,
                           max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    entry_cp = checkpoint(ws)
    applied = 0
    rejected = 0
    total_visits = 0
    last_reason = :applied
    for item in candidates
        label, val = item isa Pair ? (item.first, item.second) : (item, nothing)
        rep = apply_dominance!(
            ws, label; value=val, map, allow_weak=true,
            max_work=max_work - total_visits, max_exact_work, deadline_ns,
        )
        total_visits += rep.edge_visits
        if rep.stop_reason === :applied
            applied += 1
        else
            rejected += 1
            last_reason = rep.stop_reason
            if atomic || rep.stop_reason in (:work_limit, :verification_limit, :deadline)
                atomic && rollback!(ws, entry_cp)
                return (
                    applied=atomic ? 0 : applied,
                    rejected=rejected,
                    stop_reason=last_reason,
                    edge_visits=total_visits,
                )
            end
        end
    end
    return (
        applied=applied,
        rejected=rejected,
        stop_reason=rejected == 0 ? :applied : last_reason,
        edge_visits=total_visits,
    )
end

"""
    deductions(ws; since=nothing)

Return owned original-label/value pairs for certified constant-fixing deductions,
optionally added after a valid ancestor checkpoint. Scan only fixing records in
that range; queue-only history and the source graph are not scanned. Caller
assumptions remain available separately through `assumptions`/`changes`, and
structural reductions (`RelationStep`, `EliminationStep`) are included in
[`reductions`](@ref).
"""
function deductions(ws::Workspace;since=nothing)
    since === nothing || _validate_checkpoint(ws,since)
    start = since === nothing ? 1 : since._fix_depth+1
    st,s = ws._state,ws._snapshot
    entries = (st.trail[st.fixes[k]] for k in start:length(st.fixes))
    return [_owned_labels([s.labels[e.index]])[1]=>e.value for e in entries if e isa _UndoFix && e.proof !== nothing]
end

"""
    reductions(ws; since=nothing)

Return owned proof records ([`DominanceStep`](@ref), [`RelationStep`](@ref),
[`EliminationStep`](@ref)) in application order for all certified reductions
committed on `ws`, optionally added after a valid ancestor checkpoint `since`.
"""
function reductions(ws::Workspace; since=nothing)
    since === nothing || _validate_checkpoint(ws, since)
    start = since === nothing ? 1 : since._fix_depth + 1
    st = ws._state
    return _ProofRecord[
        deepcopy(st.trail[st.fixes[k]].proof)
        for k in start:length(st.fixes)
        if st.trail[st.fixes[k]].proof !== nothing
    ]
end

function _proof_steps(ws::Workspace; map::Union{Nothing,DomainGaugeMap}=nothing)
    raw = Tuple(deepcopy(ws._state.trail[p].proof) for p in ws._state.fixes
                if ws._state.trail[p].proof !== nothing)
    map === nothing && return raw
    return _transport_steps(ws, _caller_scope(ws), raw, nothing, map)
end

function _export_certificate(ws::Workspace,source::_Snapshot;map::Union{Nothing,DomainGaugeMap}=nothing)
    ws._state.proof_count == 0 && return nothing
    owned_map = map === nothing ? nothing : deepcopy(map)
    return DominanceCertificate(generation(ws),checkpoint(ws),_caller_scope(ws),
                                _proof_steps(ws;map=owned_map),source,owned_map)
end

"""
    export_certificate(ws; map=nothing)

Explicitly capture the complete owned reduction chain and caller scope
(optionally transported into `map::DomainGaugeMap`), or return `nothing` in
constant-size work if no certified reduction exists. Verify with
`verify_certificate`; applicability requires the captured current trail tip.
No inference, solver dispatch or residual materialization occurs here.
"""
function export_certificate(ws::Workspace; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map; full=true)
    ws._state.proof_count == 0 && return nothing
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels,source.labels)
    return _export_certificate(ws,source;map)
end
