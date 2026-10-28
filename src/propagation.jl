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
    ProbingReport

Bounded-call probing result with `generation`, `checkpoint`, `stop_reason`,
probed `candidates`, `edge_visits`, committed `deductions`, `exact_fallbacks`,
`exact_work`, remaining `pending` candidate count, and cumulative workspace
`totals`. Counters measure executed work and are not undone by model rollback.
"""
struct ProbingReport
    generation::Generation
    checkpoint::Checkpoint
    stop_reason::Symbol
    candidates::Int
    edge_visits::Int
    deductions::Int
    exact_fallbacks::Int
    exact_work::Int
    pending::Int
    totals::NamedTuple{(:candidates,:edge_visits,:exact_work),Tuple{Int,Int,Int}}
end
generation(r::ProbingReport) = r.generation

function _probing_report!(ws::Workspace, reason::Symbol, candidates::Int, edges::Int,
                          deductions::Int, fallbacks::Int, exact::Int; pending::Int=0)
    st = ws._state
    st.total_candidates += candidates
    st.total_edges += edges
    st.total_exact += exact
    return ProbingReport(
        generation(ws), checkpoint(ws), reason,
        candidates, edges, deductions, fallbacks, exact, pending,
        (candidates=st.total_candidates, edge_visits=st.total_edges, exact_work=st.total_exact),
    )
end

"""
    apply_probing!(ws, label, witness; value=nothing, map=nothing,
                   max_rounds=1, max_trial_fixes=typemax(Int),
                   max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Certify and transactionally commit one probing fixing on `ws` by strictly
refuting the opposite branch (`branch_lower > witness_upper`) against the
verified parent-scope feasible `witness` (an original-order vector, label
dictionary, or [`Reconstruction`](@ref)), recording a [`ProbingStep`](@ref) on
the reversible trail. Interrupted or inconclusive probes leave `ws` at its exact
pre-probe checkpoint. Returns an [`UpdateReport`](@ref).
"""
function apply_probing!(
    ws::Workspace,
    label,
    witness;
    value=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    max_rounds=1,
    max_trial_fixes=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    _limits(max_rounds, nothing)
    _limits(max_trial_fixes, nothing)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws, label)
    w_vec = _extract_witness_state(ws, witness, map)
    req_orig = if value === nothing
        nothing
    elseif map === nothing
        _assignment(ws, value)
    else
        _lift_index_value(map, i, _check_domain_scalar(value, map.target_domain))
    end
    st = ws._state
    st.fixed[i] == 2 || return UpdateReport(:already_fixed, 0, 0)
    _direction(ws._snapshot) != 0 || return UpdateReport(:zero_scale, 0, 0)
    deg_i = length(st.adjacency[i])
    deg_i <= max_work || return UpdateReport(:work_limit, 0, 0)
    raw_step, reason, _, visits, _, _ = _probing_witness(
        ws, i, w_vec;
        map=nothing, value=req_orig, max_rounds, max_trial_fixes,
        max_work=max_work - deg_i, max_exact_work, deadline_ns,
        predecessors=st.proof_count, scope_length=length(st.callers),
        _prevalidated_witness=w_vec,
    )
    raw_step === nothing && return UpdateReport(reason, visits, 0)
    rep = _fix!(ws, i, raw_step.value; proof=raw_step, max_work=max_work - visits, deadline_ns)
    return UpdateReport(rep.stop_reason, visits + rep.edge_visits, rep.changed)
end

"""
    probe_variables!(ws, witness; candidates=nothing, map=nothing,
                     max_candidates=typemax(Int), max_rounds=1,
                     max_trial_fixes=typemax(Int), max_work=typemax(Int),
                     max_exact_work=typemax(Int), deadline_ns=nothing)

Run an optional bounded certified probing pass across `candidates` (defaulting to
all currently free variables in original order) using a verified parent-scope
feasible `witness`. Each candidate temporarily conditions on the opposite
assignment, propagates bounded trial dominance, and commits a [`ProbingStep`](@ref)
when the trial branch lower bound strictly refutes the branch against `witness`.
Cancelled or inconclusive trial probes roll back cleanly to the pre-probe
checkpoint while charging executed work in the returned [`ProbingReport`](@ref).
"""
function probe_variables!(
    ws::Workspace,
    witness;
    candidates=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    max_candidates=typemax(Int),
    max_rounds=1,
    max_trial_fixes=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_candidates, nothing)
    _limits(max_rounds, nothing)
    _limits(max_trial_fixes, nothing)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    w_vec = _extract_witness_state(ws, witness, map)
    s, st = ws._snapshot, ws._state
    cand_indices = if candidates === nothing
        Int[i for i in 1:length(s.labels) if st.fixed[i] == 2]
    else
        seen = Set{Int}()
        out = Int[]
        for lbl in candidates
            idx = _variable(ws, lbl)
            if st.fixed[idx] == 2 && !(idx in seen)
                push!(out, idx)
                push!(seen, idx)
            end
        end
        out
    end
    _direction(s) != 0 || return _probing_report!(ws, :zero_scale, 0, 0, 0, 0, 0; pending=length(cand_indices))
    probed = 0
    visits = 0
    deduced = 0
    fallbacks = 0
    exact = 0
    n_cand = length(cand_indices)
    w_energy_ref = Ref{Union{Nothing,_Exact}}(nothing)
    for pos in 1:n_cand
        i = cand_indices[pos]
        st.fixed[i] == 2 || continue
        remaining = count(k -> st.fixed[cand_indices[k]] == 2, pos:n_cand)
        probed < max_candidates ||
            return _probing_report!(ws, :candidate_limit, probed, visits, deduced, fallbacks, exact; pending=remaining)
        _expired(deadline_ns) &&
            return _probing_report!(ws, :deadline, probed, visits, deduced, fallbacks, exact; pending=remaining)
        deg_i = length(st.adjacency[i])
        deg_i <= max_work - visits ||
            return _probing_report!(ws, :work_limit, probed, visits, deduced, fallbacks, exact; pending=remaining)
        probed += 1
        p_step, p_reason, _, p_visits, p_fb, p_exact = _probing_witness(
            ws, i, w_vec;
            map=nothing, max_rounds, max_trial_fixes,
            max_work=max_work - visits - deg_i, max_exact_work=max_exact_work - exact,
            deadline_ns, predecessors=st.proof_count, scope_length=length(st.callers),
            _prevalidated_witness=w_vec,
            _w_energy_ref=w_energy_ref,
        )
        visits += p_visits
        fallbacks += p_fb
        exact += p_exact
        if p_reason in (:deadline, :work_limit, :verification_limit)
            return _probing_report!(ws, p_reason, probed, visits, deduced, fallbacks, exact; pending=remaining)
        end
        if p_step !== nothing
            rep = _fix!(ws, i, p_step.value; proof=p_step, max_work=max_work - visits, deadline_ns)
            visits += rep.edge_visits
            rep.stop_reason === :applied ||
                return _probing_report!(ws, rep.stop_reason, probed, visits, deduced, fallbacks, exact; pending=remaining)
            deduced += 1
        end
    end
    return _probing_report!(ws, :quiescent, probed, visits, deduced, fallbacks, exact; pending=0)
end

"""
    RoofDualityReport{V,S}

Summary of an optional certified [`apply_roof_duality!`](@ref) pass, recording
`stop_reason`, exact normalized `lower_bound`, scaled model `objective_bound`,
implication-network `max_flow`, `fixed_count`, committed `fixings`, and
phase-separated work counters (`graph_work`, `flow_work`, `verification_work`,
`materialization_work`, `edge_visits`, `exact_work`).
"""
struct RoofDualityReport{V,S}
    stop_reason::Symbol
    lower_bound::Union{Nothing,_Exact}
    objective_bound::Union{Nothing,_Exact}
    max_flow::Union{Nothing,_Exact}
    fixed_count::Int
    fixings::Vector{Pair{V,S}}
    graph_work::Int
    flow_work::Int
    verification_work::Int
    materialization_work::Int
    edge_visits::Int
    exact_work::Int
end

"""
    apply_roof_duality!(ws; candidates=nothing, map=nothing,
                        max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Run an optional certified roof-duality (posiform / implication-network) pass on
`ws`, extracting and transactionally committing strongly persistent variable
assignments in `candidates` (defaulting to all free variables in original order)
as [`RoofDualityStep`](@ref) records on the reversible trail. If committing the
batch is interrupted by `max_work` or `deadline_ns`, the pass rolls back cleanly
to the pre-pass checkpoint.
"""
function apply_roof_duality!(
    ws::Workspace;
    candidates=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    S = s.state_type
    cand_indices = _resolve_roof_candidates(ws, candidates)
    batch_pairs, flow_edges, L_roof, obj_bound, total_flow,
        stop, _, graph_work, flow_work, ver_work, total_visits, exact_work = _roof_duality_pass(
        ws, cand_indices;
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    if isempty(batch_pairs)
        return RoofDualityReport{V,S}(
            stop, L_roof, obj_bound, total_flow, 0, Pair{V,S}[],
            graph_work, flow_work, ver_work, 0, total_visits, exact_work,
        )
    end
    scope_len = length(st.callers)
    base_preds = st.proof_count
    batch_tuple = Tuple(batch_pairs)
    cp = checkpoint(ws)
    saved_star_hint = st.star_hint
    saved_rel_hint = st.rel_hint
    mat_visits = 0
    for (r, (u, orig_val)) in enumerate(batch_pairs)
        if _expired(deadline_ns)
            rollback!(ws, cp)
            st.star_hint = saved_star_hint
            st.rel_hint = saved_rel_hint
            return RoofDualityReport{V,S}(
                :deadline, L_roof, obj_bound, total_flow, 0, Pair{V,S}[],
                graph_work, flow_work, ver_work, mat_visits, total_visits + mat_visits, exact_work,
            )
        end
        c_before = deepcopy(st.constant)
        step_r = RoofDualityStep(
            u, orig_val,
            deepcopy(L_roof), deepcopy(total_flow),
            flow_edges, batch_tuple, r,
            c_before, base_preds + r - 1,
            :exact, scope_len, :strong,
        )
        rep = _fix!(ws, u, orig_val; proof=step_r, max_work=max_work - total_visits - mat_visits, deadline_ns=deadline_ns)
        mat_visits += rep.edge_visits
        if rep.stop_reason !== :applied
            rollback!(ws, cp)
            st.star_hint = saved_star_hint
            st.rel_hint = saved_rel_hint
            return RoofDualityReport{V,S}(
                rep.stop_reason, L_roof, obj_bound, total_flow, 0, Pair{V,S}[],
                graph_work, flow_work, ver_work, mat_visits, total_visits + mat_visits, exact_work,
            )
        end
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in batch_pairs
    ]
    return RoofDualityReport{V,S}(
        :applied, L_roof, obj_bound, total_flow, length(fixings), fixings,
        graph_work, flow_work, ver_work, mat_visits, total_visits + mat_visits, exact_work,
    )
end

"""
    SubmodularCutReport{V,S}

Summary of an optional certified gauge-submodular component cut pass run by
[`apply_submodular_cut!`](@ref). Retains `stop_reason` (`:applied`,
`:no_persistency`, `:frustrated_cycle`, `:boundary_coupled`, `:already_fixed`,
`:zero_scale`, `:work_limit`, `:verification_limit`, or `:deadline`),
`recognized_components`, `solved_components`, exact normalized `component_opt`,
`max_flow`, `fixed_count`, committed `fixings::Vector{Pair{V,S}}`, and
phase-separated work counters (`recognition_work`, `graph_work`, `flow_work`,
`verification_work`, `materialization_work`, `edge_visits`, `exact_work`).
"""
struct SubmodularCutReport{V,S}
    stop_reason::Symbol
    recognized_components::Int
    solved_components::Int
    component_opt::Union{Nothing,_Exact}
    max_flow::Union{Nothing,_Exact}
    fixed_count::Int
    fixings::Vector{Pair{V,S}}
    recognition_work::Int
    graph_work::Int
    flow_work::Int
    verification_work::Int
    materialization_work::Int
    edge_visits::Int
    exact_work::Int
end

"""
    apply_submodular_cut!(ws; component=nothing, map=nothing, allow_weak=false,
                          tie_break=:low, max_work=typemax(Int),
                          max_exact_work=typemax(Int), deadline_ns=nothing)
    apply_submodular_cut!(ws, component; map=nothing, allow_weak=false,
                          tie_break=:low, max_work=typemax(Int),
                          max_exact_work=typemax(Int), deadline_ns=nothing)

Recognize one or all gauge-submodular residual components in `ws`, solve each via
a direct ``(|C| + 2)``-vertex exact ``s``-``t`` min-cut, and transactionally
commit the resulting strong (`allow_weak=false`, default) or full minimum-cut
(`allow_weak=true`, selected via `tie_break`) variable assignments as
[`SubmodularCutStep`](@ref) records on the reversible trail. If committing the
batch is interrupted by `max_work` or `deadline_ns`, the pass rolls back cleanly
to the pre-pass checkpoint. Returns a [`SubmodularCutReport`](@ref).
"""
function apply_submodular_cut!(
    ws::Workspace;
    component=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    tie_break::Symbol=:low,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    component !== nothing && return apply_submodular_cut!(
        ws, component;
        map=map, allow_weak=allow_weak, tie_break=tie_break,
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    tie_break in (:low, :high, :source, :sink) ||
        throw(ArgumentError("tie_break must be :low, :high, :source, or :sink"))
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    S = s.state_type
    direction = _direction(s)
    if direction == 0
        return SubmodularCutReport{V,S}(
            :zero_scale, 0, 0, nothing, nothing, 0, Pair{V,S}[],
            0, 0, 0, 0, 0, 0, 0,
        )
    end
    comps, rec_stop, rec_work = recognize_submodular_components(
        ws; max_work=max_work, deadline_ns=deadline_ns,
    )
    if rec_stop in (:deadline, :work_limit)
        return SubmodularCutReport{V,S}(
            rec_stop, 0, 0, nothing, nothing, 0, Pair{V,S}[],
            rec_work, 0, 0, 0, 0, rec_work, 0,
        )
    end
    submod_comps = SubmodularComponent{V}[c for c in comps if c.is_submodular]
    n_rec = length(submod_comps)
    if isempty(submod_comps)
        stop = isempty(comps) ? :no_persistency : :frustrated_cycle
        return SubmodularCutReport{V,S}(
            stop, 0, 0, nothing, nothing, 0, Pair{V,S}[],
            rec_work, 0, 0, 0, 0, rec_work, 0,
        )
    end
    total_graph_work = 0
    total_flow_work = 0
    total_ver_work = 0
    total_visits = rec_work
    total_exact_work = 0
    total_comp_opt = _Exact(0)
    total_max_flow = _Exact(0)
    n_solved = 0
    all_batch_pairs = Pair{Int,Int}[]
    component_batches = Tuple{
        Vector{Int},Vector{Int},_Exact,_Exact,
        Tuple{Vararg{Tuple{Int,Int,_Exact}}},Vector{Pair{Int,Int}},Vector{Symbol},
    }[]
    for c in submod_comps
        batch_pairs, batch_pers, _, gauge_vec,
            flow_edges, comp_opt, c_flow,
            stop, _, _, g_work, f_work, v_work, c_visits, c_exact = _submodular_cut_component_pass(
            ws, c.indices;
            map=map, allow_weak=allow_weak, tie_break=tie_break,
            pre_rec=c,
            max_work=max_work - total_visits,
            max_exact_work=max_exact_work - total_exact_work,
            deadline_ns=deadline_ns,
        )
        total_graph_work += g_work
        total_flow_work += f_work
        total_ver_work += v_work
        total_visits += c_visits
        total_exact_work += c_exact
        if stop in (:deadline, :work_limit, :verification_limit)
            return SubmodularCutReport{V,S}(
                stop, n_rec, n_solved, nothing, nothing, 0, Pair{V,S}[],
                rec_work, total_graph_work, total_flow_work, total_ver_work, 0, total_visits, total_exact_work,
            )
        end
        n_solved += 1
        total_comp_opt += comp_opt
        total_max_flow += c_flow
        if !isempty(batch_pairs)
            append!(all_batch_pairs, batch_pairs)
            push!(
                component_batches,
                (c.indices, gauge_vec, comp_opt, c_flow, flow_edges, batch_pairs, batch_pers),
            )
        end
    end
    if isempty(all_batch_pairs)
        return SubmodularCutReport{V,S}(
            :no_persistency, n_rec, n_solved, total_comp_opt, total_max_flow, 0, Pair{V,S}[],
            rec_work, total_graph_work, total_flow_work, total_ver_work, 0, total_visits, total_exact_work,
        )
    end
    scope_len = length(st.callers)
    base_preds = st.proof_count
    cp = checkpoint(ws)
    saved_star_hint = st.star_hint
    saved_rel_hint = st.rel_hint
    mat_visits = 0
    step_offset = 0
    for (comp_indices, gauge_vec, comp_opt, c_flow, flow_edges, batch_pairs, batch_pers) in component_batches
        comp_tuple = Tuple(comp_indices)
        gauge_tuple = Tuple(gauge_vec)
        batch_tuple = Tuple(batch_pairs)
        for (r, (u, orig_val)) in enumerate(batch_pairs)
            if _expired(deadline_ns)
                rollback!(ws, cp)
                st.star_hint = saved_star_hint
                st.rel_hint = saved_rel_hint
                return SubmodularCutReport{V,S}(
                    :deadline, n_rec, n_solved, total_comp_opt, total_max_flow, 0, Pair{V,S}[],
                    rec_work, total_graph_work, total_flow_work, total_ver_work,
                    mat_visits, total_visits + mat_visits, total_exact_work,
                )
            end
            c_before = deepcopy(st.constant)
            step_r = SubmodularCutStep(
                u, orig_val,
                comp_tuple, gauge_tuple,
                deepcopy(comp_opt), deepcopy(c_flow),
                flow_edges, batch_tuple, r,
                c_before, base_preds + step_offset,
                :exact, scope_len, batch_pers[r],
            )
            step_offset += 1
            rep = _fix!(
                ws, u, orig_val;
                proof=step_r, max_work=max_work - total_visits - mat_visits, deadline_ns=deadline_ns,
            )
            mat_visits += rep.edge_visits
            if rep.stop_reason !== :applied
                rollback!(ws, cp)
                st.star_hint = saved_star_hint
                st.rel_hint = saved_rel_hint
                return SubmodularCutReport{V,S}(
                    rep.stop_reason, n_rec, n_solved, total_comp_opt, total_max_flow, 0, Pair{V,S}[],
                    rec_work, total_graph_work, total_flow_work, total_ver_work,
                    mat_visits, total_visits + mat_visits, total_exact_work,
                )
            end
        end
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in all_batch_pairs
    ]
    return SubmodularCutReport{V,S}(
        :applied, n_rec, n_solved, total_comp_opt, total_max_flow, length(fixings), fixings,
        rec_work, total_graph_work, total_flow_work, total_ver_work,
        mat_visits, total_visits + mat_visits, total_exact_work,
    )
end

function apply_submodular_cut!(
    ws::Workspace,
    component;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    tie_break::Symbol=:low,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    tie_break in (:low, :high, :source, :sink) ||
        throw(ArgumentError("tie_break must be :low, :high, :source, or :sink"))
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    S = s.state_type
    comp_indices = Int[]
    candidate_index = nothing
    init_rec_work = 0
    if component isa SubmodularComponent
        seen = Set{Int}()
        for lbl in component.variables
            u = _variable(ws, lbl)
            if !(u in seen)
                push!(comp_indices, u)
                push!(seen, u)
            end
        end
        isempty(comp_indices) && throw(ArgumentError("component must contain at least one variable"))
        sort!(comp_indices)
    elseif !(component isa Union{AbstractVector,AbstractSet}) && haskey(st.labels, component)
        i = _variable(ws, component)
        candidate_index = i
        if st.fixed[i] != 2
            return SubmodularCutReport{V,S}(
                :already_fixed, 0, 0, nothing, nothing, 0, Pair{V,S}[],
                0, 0, 0, 0, 0, 0, 0,
            )
        end
        if _direction(s) == 0
            return SubmodularCutReport{V,S}(
                :zero_scale, 0, 0, nothing, nothing, 0, Pair{V,S}[],
                0, 0, 0, 0, 0, 0, 0,
            )
        end
        comp_indices, conn_reason, conn_work = _connected_active_component(
            ws, i; max_work=max_work, deadline_ns=deadline_ns,
        )
        init_rec_work = conn_work
        if conn_reason !== :ok
            return SubmodularCutReport{V,S}(
                conn_reason, 0, 0, nothing, nothing, 0, Pair{V,S}[],
                init_rec_work, 0, 0, 0, 0, init_rec_work, 0,
            )
        end
    else
        seen = Set{Int}()
        for lbl in component
            u = _variable(ws, lbl)
            if !(u in seen)
                push!(comp_indices, u)
                push!(seen, u)
            end
        end
        isempty(comp_indices) && throw(ArgumentError("component must contain at least one variable"))
        sort!(comp_indices)
    end
    batch_pairs, batch_pers, _, gauge_vec,
        flow_edges, comp_opt, total_flow,
        stop, _, rec_work, graph_work, flow_work, ver_work, total_visits, exact_work = _submodular_cut_component_pass(
        ws, comp_indices;
        map=map, allow_weak=allow_weak, tie_break=tie_break,
        candidate_index=candidate_index,
        max_work=max_work - init_rec_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    rec_work += init_rec_work
    total_visits += init_rec_work
    n_rec = isempty(gauge_vec) ? 0 : 1
    n_solved = comp_opt === nothing ? 0 : 1
    if isempty(batch_pairs)
        return SubmodularCutReport{V,S}(
            stop, n_rec, n_solved, comp_opt, total_flow, 0, Pair{V,S}[],
            rec_work, graph_work, flow_work, ver_work, 0, total_visits, exact_work,
        )
    end
    scope_len = length(st.callers)
    base_preds = st.proof_count
    comp_tuple = Tuple(comp_indices)
    gauge_tuple = Tuple(gauge_vec)
    batch_tuple = Tuple(batch_pairs)
    cp = checkpoint(ws)
    saved_star_hint = st.star_hint
    saved_rel_hint = st.rel_hint
    mat_visits = 0
    for (r, (u, orig_val)) in enumerate(batch_pairs)
        if _expired(deadline_ns)
            rollback!(ws, cp)
            st.star_hint = saved_star_hint
            st.rel_hint = saved_rel_hint
            return SubmodularCutReport{V,S}(
                :deadline, n_rec, n_solved, comp_opt, total_flow, 0, Pair{V,S}[],
                rec_work, graph_work, flow_work, ver_work, mat_visits, total_visits + mat_visits, exact_work,
            )
        end
        c_before = deepcopy(st.constant)
        step_r = SubmodularCutStep(
            u, orig_val,
            comp_tuple, gauge_tuple,
            deepcopy(comp_opt), deepcopy(total_flow),
            flow_edges, batch_tuple, r,
            c_before, base_preds + r - 1,
            :exact, scope_len, batch_pers[r],
        )
        rep = _fix!(ws, u, orig_val; proof=step_r, max_work=max_work - total_visits - mat_visits, deadline_ns=deadline_ns)
        mat_visits += rep.edge_visits
        if rep.stop_reason !== :applied
            rollback!(ws, cp)
            st.star_hint = saved_star_hint
            st.rel_hint = saved_rel_hint
            return SubmodularCutReport{V,S}(
                rep.stop_reason, n_rec, n_solved, comp_opt, total_flow, 0, Pair{V,S}[],
                rec_work, graph_work, flow_work, ver_work, mat_visits, total_visits + mat_visits, exact_work,
            )
        end
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in batch_pairs
    ]
    return SubmodularCutReport{V,S}(
        :applied, n_rec, n_solved, comp_opt, total_flow, length(fixings), fixings,
        rec_work, graph_work, flow_work, ver_work, mat_visits, total_visits + mat_visits, exact_work,
    )
end

"""
    MaxCutReport{V,S}

Report returned by [`apply_maxcut!`](@ref), recording `generation`, `checkpoint`,
`stop_reason` (`:applied`, `:quiescent`, `:not_strict`, `:no_persistency`,
`:already_fixed`, `:zero_scale`, `:fill_limit`, `:deduction_limit`,
`:work_limit`, `:verification_limit`, `:deadline`, or `:optional_pass_disabled`),
examined `candidates`, total committed `deductions`, `unary_fixings`,
`pair_contractions`, `edge_deductions` (`:maxcut_edge`), `triangle_deductions`
(`:maxcut_triangle`), total `triangles_used`, introduced `fill_edges`,
`initial_reference_degree`, `residual_reference_degree`, committed `fixings`,
committed `contractions` `(eliminated, representative, sign)`, and phase-separated
work counters (`graph_work`, `triangle_work`, `materialization_work`,
`edge_visits`, `exact_work`).
"""
struct MaxCutReport{V,S}
    generation::Generation
    checkpoint::Checkpoint
    stop_reason::Symbol
    candidates::Int
    deductions::Int
    unary_fixings::Int
    pair_contractions::Int
    edge_deductions::Int
    triangle_deductions::Int
    triangles_used::Int
    fill_edges::Int
    initial_reference_degree::Int
    residual_reference_degree::Int
    fixings::Vector{Pair{V,S}}
    contractions::Vector{Tuple{V,V,Int}}
    graph_work::Int
    triangle_work::Int
    materialization_work::Int
    edge_visits::Int
    exact_work::Int
end
generation(r::MaxCutReport) = r.generation

"""
    apply_maxcut!(ws, label; value=nothing, map=nothing, allow_weak=false,
                  max_triangles=typemax(Int), max_work=typemax(Int),
                  max_exact_work=typemax(Int), deadline_ns=nothing)
    apply_maxcut!(ws, eliminated, representative; sign=nothing, map=nothing,
                  allow_weak=false, max_triangles=typemax(Int),
                  max_fill=typemax(Int), max_work=typemax(Int),
                  max_exact_work=typemax(Int), deadline_ns=nothing)
    apply_maxcut!(ws; candidates=nothing, map=nothing, allow_weak=false,
                  enable_unary=true, enable_pairs=true,
                  max_triangles=typemax(Int), max_fill=typemax(Int),
                  max_deductions=typemax(Int), max_work=typemax(Int),
                  max_exact_work=typemax(Int), deadline_ns=nothing)

Certify and transactionally commit weighted Max-Cut edge and triangle reductions
on the active residual Max-Cut graph ``G_{\\text{MC}} = (\\{0\\} \\cup F, E_{\\text{cut}}, w)``,
recording [`MaxCutStep`](@ref) proof records on the reversible trail and returning
a [`MaxCutReport`](@ref).
"""
function apply_maxcut!(
    ws::Workspace,
    label;
    value=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    max_triangles=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    u = _variable(ws, label)
    s, st = ws._snapshot, ws._state
    V, S = s.label_type, s.state_type
    init_ref_deg = _reference_degree(ws)
    raw_step, reason, method, _, tris_used, g_work, t_work, ex_work = _maxcut_witness(
        ws, u, 0;
        value=value, map=map, allow_weak=allow_weak, max_triangles=max_triangles,
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
        predecessors=st.proof_count, scope_length=length(st.callers),
    )
    visits = g_work + t_work
    if raw_step === nothing
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), reason, 1, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, init_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            g_work, t_work, 0, visits, ex_work,
        )
    end
    step = map === nothing ? raw_step :
        MaxCutStep(
            u, 0, raw_step.anchor, raw_step.orig_sign, raw_step.orig_sign, raw_step.value,
            deepcopy(raw_step.margin), deepcopy(raw_step.direct_weight),
            deepcopy(raw_step.non_triangle_slack), deepcopy(raw_step.triangles),
            deepcopy(st.constant), raw_step.predecessors, raw_step.method,
            raw_step.scope_length, raw_step.persistency,
        )
    rep = _fix!(ws, u, step.value; proof=step, max_work=max_work - visits, deadline_ns=deadline_ns)
    mat_work = rep.edge_visits
    tot_visits = visits + mat_work
    res_ref_deg = _reference_degree(ws)
    if rep.stop_reason !== :applied
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), rep.stop_reason, 1, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, res_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            g_work, t_work, mat_work, tot_visits, ex_work,
        )
    end
    mapped_val = S(map === nothing ? step.value : _map_index_value(map, u, step.value))
    fixings = Pair{V,S}[deepcopy(s.labels[u]) => mapped_val]
    is_edge = method === :maxcut_edge ? 1 : 0
    return MaxCutReport{V,S}(
        generation(ws), checkpoint(ws), :applied, 1, 1, 1, 0, is_edge, 1 - is_edge,
        tris_used, 0, init_ref_deg, res_ref_deg, fixings, Tuple{V,V,Int}[],
        g_work, t_work, mat_work, tot_visits, ex_work,
    )
end

function apply_maxcut!(
    ws::Workspace,
    eliminated,
    representative;
    sign::Union{Nothing,Int}=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    max_triangles=typemax(Int),
    max_fill=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    max_fill isa Integer && !(max_fill isa Bool) && 0 <= max_fill <= typemax(Int) ||
        throw(ArgumentError("max_fill must be a nonnegative machine-sized integer"))
    map === nothing || _validate_domain_map(ws, map)
    u = _variable(ws, eliminated)
    v = _variable(ws, representative)
    u != v || throw(ArgumentError("Max-Cut pair relation requires two distinct variables"))
    s, st = ws._snapshot, ws._state
    V, S = s.label_type, s.state_type
    init_ref_deg = _reference_degree(ws)
    if !(st.fixed[u] == 2 && st.fixed[v] == 2)
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), :already_fixed, 1, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, init_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            0, 0, 0, 0, 0,
        )
    end
    f_uv = _contraction_fill(st, u, v)
    if f_uv > Int(max_fill)
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), :fill_limit, 1, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, init_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            0, 0, 0, 0, 0,
        )
    end
    raw_step, reason, method, _, tris_used, g_work, t_work, ex_work = _maxcut_witness(
        ws, u, v;
        sign=sign, map=map, allow_weak=allow_weak, max_triangles=max_triangles,
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
        predecessors=st.proof_count, scope_length=length(st.callers),
    )
    visits = g_work + t_work
    if raw_step === nothing
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), reason, 1, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, init_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            g_work, t_work, 0, visits, ex_work,
        )
    end
    step = map === nothing ? raw_step :
        MaxCutStep(
            u, v, raw_step.anchor, raw_step.orig_sign, raw_step.orig_sign, 0,
            deepcopy(raw_step.margin), deepcopy(raw_step.direct_weight),
            deepcopy(raw_step.non_triangle_slack), deepcopy(raw_step.triangles),
            deepcopy(st.constant), raw_step.predecessors, raw_step.method,
            raw_step.scope_length, raw_step.persistency,
        )
    const_delta, field_deltas, quad_deltas = _relation_deltas(ws, u, v, step.orig_sign)
    rep = _apply_reduction!(
        ws, u, Int8(3), step, const_delta, field_deltas, quad_deltas;
        max_work=max_work - visits, deadline_ns=deadline_ns, precharged_visits=0,
    )
    mat_work = rep.edge_visits
    tot_visits = visits + mat_work
    res_ref_deg = _reference_degree(ws)
    if rep.stop_reason !== :applied
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), rep.stop_reason, 1, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, res_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            g_work, t_work, mat_work, tot_visits, ex_work,
        )
    end
    contractions = Tuple{V,V,Int}[(deepcopy(s.labels[u]), deepcopy(s.labels[v]), raw_step.sign)]
    is_edge = method === :maxcut_edge ? 1 : 0
    return MaxCutReport{V,S}(
        generation(ws), checkpoint(ws), :applied, 1, 1, 0, 1, is_edge, 1 - is_edge,
        tris_used, f_uv, init_ref_deg, res_ref_deg, Pair{V,S}[], contractions,
        g_work, t_work, mat_work, tot_visits, ex_work,
    )
end

function _mc_compute_sweep_bounds!(
    W_lo::Vector{Float64},
    M_hi::Vector{Float64},
    G_hi::Vector{Float64},
    H_hi::Vector{Float64},
    ws::Workspace,
    mt::Int,
)
    s, st = ws._snapshot, ws._state
    (st.lower !== nothing && st.upper !== nothing) || return false
    n = length(s.labels)
    is_spin_dom = s.domain === QT.SpinDomain
    scale_inv = is_spin_dom ? 1.0 : 0.25
    tot_scale = is_spin_dom ? 0.5 : 0.25
    W0_lo = 0.0
    M0_hi = 0.0
    @inbounds for x in 1:n
        if st.fixed[x] != 2
            W_lo[x] = Inf
            M_hi[x] = 0.0
            G_hi[x] = 0.0
            H_hi[x] = 0.0
            continue
        end
        hx_raw = _spin_field(ws, x)
        hx_lo, hx_hi = _enclose(hx_raw)
        hx_abs_lo = (hx_lo <= 0.0 && hx_hi >= 0.0) ? 0.0 : min(abs(hx_lo), abs(hx_hi))
        hx_abs_hi = max(abs(hx_lo), abs(hx_hi))
        H_hi[x] = hx_abs_hi
        W0_lo = prevfloat(W0_lo + hx_abs_lo)
        hx_abs_hi > M0_hi && (M0_hi = hx_abs_hi)
        up_lo, _ = _enclose(st.upper[x])
        _, lo_hi = _enclose(st.lower[x])
        edge_lo = prevfloat(tot_scale * prevfloat(up_lo - lo_hi))
        W_lo[x] = prevfloat(edge_lo + hx_abs_lo)
        mx = hx_abs_hi
        for (w, q) in st.adjacency[x]
            (st.fixed[w] == 2 && !iszero(q)) || continue
            q_lo, q_hi = _enclose(q)
            j_hi = nextfloat(scale_inv * max(abs(q_lo), abs(q_hi)))
            j_hi > mx && (mx = j_hi)
        end
        M_hi[x] = mx
    end
    @inbounds for x in 1:n
        st.fixed[x] == 2 || continue
        if mt == 0
            G_hi[x] = 0.0
            continue
        end
        g_sum = 0.0
        if H_hi[x] > 0.0
            two_jac = nextfloat(2.0 * H_hi[x])
            cand_g = nextfloat(nextfloat(two_jac + nextfloat(2.0 * M0_hi)) - W0_lo)
            if !(cand_g <= 0.0)
                g_sum = nextfloat(g_sum + min(two_jac, cand_g))
            end
        end
        for (c, q) in st.adjacency[x]
            (st.fixed[c] == 2 && !iszero(q)) || continue
            q_lo, q_hi = _enclose(q)
            j_ac_hi = nextfloat(scale_inv * max(abs(q_lo), abs(q_hi)))
            two_jac = nextfloat(2.0 * j_ac_hi)
            cand_g = nextfloat(nextfloat(two_jac + nextfloat(2.0 * M_hi[c])) - W_lo[c])
            if !(cand_g <= 0.0)
                g_sum = nextfloat(g_sum + min(two_jac, cand_g))
            end
        end
        G_hi[x] = g_sum
    end
    return true
end

function apply_maxcut!(
    ws::Workspace;
    candidates=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    enable_unary::Bool=true,
    enable_pairs::Bool=true,
    max_triangles=typemax(Int),
    max_fill=typemax(Int),
    max_deductions=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    _limits(max_deductions, deadline_ns)
    max_triangles isa Integer && !(max_triangles isa Bool) && 0 <= max_triangles <= typemax(Int) ||
        throw(ArgumentError("max_triangles must be a nonnegative machine-sized integer"))
    max_fill isa Integer && !(max_fill isa Bool) && 0 <= max_fill <= typemax(Int) ||
        throw(ArgumentError("max_fill must be a nonnegative machine-sized integer"))
    map === nothing || _validate_domain_map(ws, map)
    s, st = ws._snapshot, ws._state
    V, S = s.label_type, s.state_type
    cand_indices = _resolve_roof_candidates(ws, candidates)
    init_ref_deg = _reference_degree(ws)
    if !enable_unary && !enable_pairs
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), :optional_pass_disabled, 0, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, init_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            0, 0, 0, 0, 0,
        )
    end
    if _direction(s) == 0
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), :zero_scale, 0, 0, 0, 0, 0, 0, 0, 0,
            init_ref_deg, init_ref_deg, Pair{V,S}[], Tuple{V,V,Int}[],
            0, 0, 0, 0, 0,
        )
    end
    mf = Int(max_fill)
    mt = Int(max_triangles)
    cand_count = 0
    ded_count = 0
    unary_count = 0
    pair_count = 0
    edge_count = 0
    tri_count = 0
    tris_total = 0
    fill_total = 0
    g_work_tot = 0
    t_work_tot = 0
    mat_work_tot = 0
    ex_work_tot = 0
    fixings = Pair{V,S}[]
    contractions = Tuple{V,V,Int}[]
    fill_skipped = false

    function finish(reason)
        tot_visits = g_work_tot + t_work_tot + mat_work_tot
        st.total_candidates += cand_count
        st.total_edges += tot_visits
        st.total_exact += ex_work_tot
        return MaxCutReport{V,S}(
            generation(ws), checkpoint(ws), reason,
            cand_count, ded_count, unary_count, pair_count, edge_count, tri_count,
            tris_total, fill_total, init_ref_deg, _reference_degree(ws),
            fixings, contractions,
            g_work_tot, t_work_tot, mat_work_tot, tot_visits, ex_work_tot,
        )
    end

    w0_cache = Ref{Union{Nothing,_Exact}}(nothing)
    tested_pairs = Set{Tuple{Int,Int}}()
    n_vars = length(s.labels)
    W_lo = Vector{Float64}(undef, n_vars)
    M_hi = Vector{Float64}(undef, n_vars)
    G_hi = Vector{Float64}(undef, n_vars)
    H_hi = Vector{Float64}(undef, n_vars)
    scale_inv = s.domain === QT.SpinDomain ? 1.0 : 0.25
    while true
        changed_in_sweep = false
        empty!(tested_pairs)
        bounds_valid = _mc_compute_sweep_bounds!(W_lo, M_hi, G_hi, H_hi, ws, mt)
        if enable_unary
            for u in cand_indices
                st.fixed[u] == 2 || continue
                _expired(deadline_ns) && return finish(:deadline)
                ded_count < max_deductions || return finish(:deduction_limit)
                rem_w = Int(max_work) - (g_work_tot + t_work_tot + mat_work_tot)
                rem_ex = Int(max_exact_work) - ex_work_tot
                rem_w > 0 || return finish(:work_limit)
                rem_ex > 0 || return finish(:verification_limit)
                if bounds_valid && rem_w >= length(st.adjacency[u]) + st.degrees[u] && rem_ex > st.degrees[u] &&
                   isfinite(W_lo[u]) && isfinite(G_hi[u]) && isfinite(H_hi[u]) &&
                   nextfloat(nextfloat(2.0 * H_hi[u]) + G_hi[u]) < W_lo[u]
                    cand_count += 1
                    g_work_tot += length(st.adjacency[u])
                    ex_work_tot += 1 + st.degrees[u]
                    continue
                end
                cand_count += 1
                raw_step, reason, method, _, tris_used, gw, tw, exw = _maxcut_witness(
                    ws, u, 0;
                    map=map, allow_weak=allow_weak, max_triangles=mt,
                    max_work=rem_w, max_exact_work=rem_ex, deadline_ns=deadline_ns,
                    predecessors=st.proof_count, scope_length=length(st.callers),
                    w0_cache=w0_cache,
                )
                g_work_tot += gw
                t_work_tot += tw
                ex_work_tot += exw
                reason in (:deadline, :work_limit, :verification_limit) && return finish(reason)
                raw_step === nothing && continue
                step = map === nothing ? raw_step :
                    MaxCutStep(
                        u, 0, raw_step.anchor, raw_step.orig_sign, raw_step.orig_sign, raw_step.value,
                        deepcopy(raw_step.margin), deepcopy(raw_step.direct_weight),
                        deepcopy(raw_step.non_triangle_slack), _deepcopy_tuple(raw_step.triangles, IdDict()),
                        deepcopy(st.constant), raw_step.predecessors, raw_step.method,
                        raw_step.scope_length, raw_step.persistency,
                    )
                rem_w2 = Int(max_work) - (g_work_tot + t_work_tot + mat_work_tot)
                rep = _fix!(ws, u, step.value; proof=step, max_work=rem_w2, deadline_ns=deadline_ns)
                mat_work_tot += rep.edge_visits
                rep.stop_reason === :applied || return finish(rep.stop_reason)
                w0_cache[] = nothing
                bounds_valid = _mc_compute_sweep_bounds!(W_lo, M_hi, G_hi, H_hi, ws, mt)
                ded_count += 1
                unary_count += 1
                method === :maxcut_edge ? (edge_count += 1) : (tri_count += 1)
                tris_total += tris_used
                mapped_val = S(map === nothing ? step.value : _map_index_value(map, u, step.value))
                push!(fixings, deepcopy(s.labels[u]) => mapped_val)
                changed_in_sweep = true
            end
        end
        if enable_pairs
            for u in cand_indices
                st.fixed[u] == 2 && st.degrees[u] >= 1 || continue
                _expired(deadline_ns) && return finish(:deadline)
                ded_count < max_deductions || return finish(:deduction_limit)
                nbrs = Pair{Int,_Exact}[w => q for (w, q) in st.adjacency[u] if st.fixed[w] == 2 && !iszero(q)]
                sort!(nbrs; by=first)
                for (v, q) in nbrs
                    (st.fixed[u] == 2 && st.fixed[v] == 2) || continue
                    pair_key = u < v ? (u, v) : (v, u)
                    pair_key in tested_pairs && continue
                    _expired(deadline_ns) && return finish(:deadline)
                    ded_count < max_deductions || return finish(:deduction_limit)
                    rem_w = Int(max_work) - (g_work_tot + t_work_tot + mat_work_tot)
                    rem_ex = Int(max_exact_work) - ex_work_tot
                    rem_w > 0 || return finish(:work_limit)
                    rem_ex > 0 || return finish(:verification_limit)
                    if bounds_valid
                        q_lo, q_hi = _enclose(q)
                        j_uv_hi = nextfloat(scale_inv * max(abs(q_lo), abs(q_hi)))
                        two_j = nextfloat(2.0 * j_uv_hi)
                        need_w = length(st.adjacency[u]) + length(st.adjacency[v]) + 2 * (st.degrees[u] + st.degrees[v])
                        need_ex = 2 + st.degrees[u] + st.degrees[v]
                        if rem_w >= need_w && rem_ex >= need_ex &&
                           isfinite(W_lo[u]) && isfinite(G_hi[u]) && isfinite(W_lo[v]) && isfinite(G_hi[v]) &&
                           isfinite(two_j) &&
                           nextfloat(two_j + G_hi[u]) < W_lo[u] && nextfloat(two_j + G_hi[v]) < W_lo[v]
                            push!(tested_pairs, pair_key)
                            cand_count += 1
                            g_work_tot += length(st.adjacency[u]) + length(st.adjacency[v])
                            ex_work_tot += 2 + st.degrees[u] + st.degrees[v]
                            continue
                        end
                    end
                    f_uv = _contraction_fill(st, u, v)
                    f_vu = _contraction_fill(st, v, u)
                    elim, rep_v, f_chosen = f_uv <= f_vu ? (u, v, f_uv) : (v, u, f_vu)
                    if f_chosen > mf
                        fill_skipped = true
                        push!(tested_pairs, pair_key)
                        continue
                    end
                    push!(tested_pairs, pair_key)
                    cand_count += 1
                    raw_step, reason, method, _, tris_used, gw, tw, exw = _maxcut_witness(
                        ws, elim, rep_v;
                        map=map, allow_weak=allow_weak, max_triangles=mt,
                        max_work=rem_w, max_exact_work=rem_ex, deadline_ns=deadline_ns,
                        predecessors=st.proof_count, scope_length=length(st.callers),
                        w0_cache=w0_cache,
                    )
                    g_work_tot += gw
                    t_work_tot += tw
                    ex_work_tot += exw
                    reason in (:deadline, :work_limit, :verification_limit) && return finish(reason)
                    raw_step === nothing && continue
                    step = map === nothing ? raw_step :
                        MaxCutStep(
                            elim, rep_v, raw_step.anchor, raw_step.orig_sign, raw_step.orig_sign, 0,
                            deepcopy(raw_step.margin), deepcopy(raw_step.direct_weight),
                            deepcopy(raw_step.non_triangle_slack), _deepcopy_tuple(raw_step.triangles, IdDict()),
                            deepcopy(st.constant), raw_step.predecessors, raw_step.method,
                            raw_step.scope_length, raw_step.persistency,
                        )
                    const_delta, field_deltas, quad_deltas = _relation_deltas(ws, elim, rep_v, step.orig_sign)
                    rem_w2 = Int(max_work) - (g_work_tot + t_work_tot + mat_work_tot)
                    rep_apply = _apply_reduction!(
                        ws, elim, Int8(3), step, const_delta, field_deltas, quad_deltas;
                        max_work=rem_w2, deadline_ns=deadline_ns, precharged_visits=0,
                    )
                    mat_work_tot += rep_apply.edge_visits
                    rep_apply.stop_reason === :applied || return finish(rep_apply.stop_reason)
                    w0_cache[] = nothing
                    empty!(tested_pairs)
                    bounds_valid = _mc_compute_sweep_bounds!(W_lo, M_hi, G_hi, H_hi, ws, mt)
                    ded_count += 1
                    pair_count += 1
                    method === :maxcut_edge ? (edge_count += 1) : (tri_count += 1)
                    tris_total += tris_used
                    fill_total += f_chosen
                    push!(contractions, (deepcopy(s.labels[elim]), deepcopy(s.labels[rep_v]), raw_step.sign))
                    changed_in_sweep = true
                    elim == u && break
                end
            end
        end
        changed_in_sweep || break
    end
    stop = ded_count > 0 ? :quiescent : (fill_skipped ? :fill_limit : :no_persistency)
    return finish(stop)
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

@inline function _can_possibly_contract(
    ws::Workspace,
    elim::Int,
    rep::Int,
    q::_Exact,
    direction::Int,
    map::Union{Nothing,DomainGaugeMap},
)
    st, s = ws._state, ws._snapshot
    (st.lower !== nothing && st.upper !== nothing) || return true
    iszero(q) && return false
    is_spin_dom = s.domain === QT.SpinDomain
    tot_scale = is_spin_dom ? 0.5 : 0.25
    j_scale = is_spin_dom ? 1.0 : 0.25
    up_e_lo, _ = _enclose(st.upper[elim])
    _, lo_e_hi = _enclose(st.lower[elim])
    tot_e_lo = prevfloat(tot_scale * prevfloat(up_e_lo - lo_e_hi))
    g_e = map === nothing ? 1 : map.gauge[elim]
    g_r = map === nothing ? 1 : map.gauge[rep]
    he_raw = _spin_field(ws, elim)
    he_lo, he_hi = _enclose(he_raw)
    he_abs_hi = max(abs(he_lo), abs(he_hi))
    he_abs_lo = (he_lo <= 0.0 && he_hi >= 0.0) ? 0.0 : min(abs(he_lo), abs(he_hi))
    q_lo, q_hi = _enclose(q)
    two_c_hi = nextfloat(2.0 * nextfloat(j_scale * max(abs(q_lo), abs(q_hi))))
    if isfinite(tot_e_lo) && isfinite(he_abs_hi) && isfinite(two_c_hi)
        nextfloat(two_c_hi + he_abs_hi) < tot_e_lo && return false
        if nextfloat(two_c_hi - he_abs_lo) < tot_e_lo
            iszero(he_raw) && return false
            up_r_lo, _ = _enclose(st.upper[rep])
            _, lo_r_hi = _enclose(st.lower[rep])
            tot_r_lo = prevfloat(tot_scale * prevfloat(up_r_lo - lo_r_hi))
            hr_raw = _spin_field(ws, rep)
            hrr_lo, hrr_hi = _enclose(hr_raw)
            hr_lo, hr_hi = (direction * g_r >= 0) ? (hrr_lo, hrr_hi) : (-hrr_hi, -hrr_lo)
            q_mapped_nonpos = (direction * (g_e * g_r) >= 0) ? (q < 0) : (q > 0)
            σ = q_mapped_nonpos ? 1 : -1
            he_pos = (direction * g_e >= 0) ? (he_raw > 0) : (he_raw < 0)
            σ_he_pos = (σ == 1) ? he_pos : !he_pos
            req_hr_hi = σ_he_pos ? hr_hi : -hr_lo
            if isfinite(tot_r_lo) && isfinite(req_hr_hi) && nextfloat(two_c_hi + req_hr_hi) < tot_r_lo
                return false
            end
        end
    end
    return true
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
    nbrs = Pair{Int,_Exact}[]
    for (w, q) in st.adjacency[u]
        _expired(deadline_ns) && return (:deadline, 0, 0, 0, 0, 0, 0)
        if st.fixed[w] == 2 && !iszero(q)
            push!(nbrs, w => q)
        end
    end
    sort!(nbrs; by=first)
    u_visits = 0
    u_exact = 0
    u_fb = 0
    called_witness = false
    min_blocked = typemax(Int)
    fills_uv = fill(-1, length(nbrs))
    for (idx, (v, q)) in enumerate(nbrs)
        can_uv = _can_possibly_contract(ws, u, v, q, direction, map)
        if !can_uv && (mf == typemax(Int) || min_blocked <= mf + 1)
            continue
        end
        f_uv = _contraction_fill(st, u, v)
        fills_uv[idx] = f_uv
        if f_uv <= mf
            can_uv || continue
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
    for (idx, (v, q)) in enumerate(nbrs)
        can_vu = _can_possibly_contract(ws, v, u, q, direction, map)
        if !can_vu && (mf == typemax(Int) || min_blocked <= mf + 1)
            continue
        end
        f_uv = fills_uv[idx]
        if f_uv >= 0 && f_uv <= mf && st.rel_queued[v]
            if st.degrees[v] - 1 > mf && (can_vu || min_blocked > mf + 1)
                f_vu = _contraction_fill(st, v, u)
                f_vu > mf && (min_blocked = min(min_blocked, f_vu))
            end
            continue
        end
        if f_uv < 0 && st.rel_queued[v]
            if st.degrees[v] - 1 > mf && (can_vu || min_blocked > mf + 1)
                f_vu = _contraction_fill(st, v, u)
                f_vu > mf && (min_blocked = min(min_blocked, f_vu))
            end
            continue
        end
        f_vu = _contraction_fill(st, v, u)
        if f_vu <= mf
            can_vu || continue
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
        else
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
        step = entry.proof::Union{RelationStep,MaxCutStep}
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
[`EliminationStep`](@ref), [`ProbingStep`](@ref)) in application order for all
certified reductions committed on `ws`, optionally added after a valid ancestor
checkpoint `since`.
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
