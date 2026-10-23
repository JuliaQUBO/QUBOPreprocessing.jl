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

function _propagation_report!(ws,reason,candidates,edges,deductions,exact)
    st = ws._state
    st.total_candidates += candidates
    st.total_edges += edges
    st.total_exact += exact
    return PropagationReport(generation(ws),checkpoint(ws),reason,candidates,edges,deductions,exact,
        length(st.queue)-st.head+1,
        (candidates=st.total_candidates,edge_visits=st.total_edges,exact_work=st.total_exact))
end

function _pop_queue!(ws::Workspace)
    st = ws._state
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    i = st.queue[st.head]
    entry = _UndoQueue(st.serial+1,length(st.fixes),i,st.head,st.queued[i])
    _reserve!(st.trail,length(st.trail)+1)
    push!(st.trail,entry)
    st.serial += 1
    st.queued[i] = false
    st.head += 1
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
        candidates+edges < max_work || return finish(:work_limit)
        i = st.queue[st.head]
        if st.fixed[i] == 2 && direction != 0
            exact < max_exact_work || return finish(:verification_limit)
        end
        candidates += 1
        if st.fixed[i] != 2 || direction == 0
            _pop_queue!(ws)
            continue
        end
        exact += 1
        step = _cached_step(ws,i,direction;allow_weak)
        if step === nothing && allow_weak
            m_step, m_reason, _, m_visits, _, m_exact = _marginal_dominance_witness(
                ws, i, nothing, nothing, direction, 0, 0,
                Int(max_work - candidates - edges), Int(max_exact_work - exact),
                deadline_ns, st.proof_count, length(st.callers),
            )
            edges += m_visits
            exact += m_exact
            m_reason in (:work_limit, :verification_limit, :deadline) && return finish(m_reason)
            step = m_step
        end
        if step === nothing
            _pop_queue!(ws)
            continue
        end
        degree = length(st.adjacency[i])
        degree <= max_work-candidates-edges || return finish(:work_limit)
        remaining = max_exact_work-exact
        remaining >= 1 && degree <= (remaining-1)÷3 || return finish(:verification_limit)
        reserved = 1+3*degree
        st.serial <= typemax(UInt64)-2 || throw(ArgumentError("trail serial exhausted; reset workspace"))
        _reserve!(st.trail,length(st.trail)+2)
        result = _fix!(ws,i,step.value;proof=step,max_work=max_work-candidates-edges,deadline_ns)
        edges += result.edge_visits
        exact += reserved
        result.stop_reason === :applied || return finish(result.stop_reason)
        deductions += 1
        _pop_queue!(ws)
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
        _, _, _, dm = _poly_marginal_diff(_init_poly_from_ws(ws), i, nothing)
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

function _init_poly_from_ws(ws::Workspace)
    st, s = ws._state, ws._snapshot
    n = length(s.labels)
    active = BitVector(st.fixed[k] == 2 for k in 1:n)
    adj = [Pair{Int,_Exact}[p for p in st.adjacency[k] if st.fixed[p.first] == 2] for k in 1:n]
    h_spin = s.domain === QT.SpinDomain ? copy(st.fields) : copy(st.dual_fields)
    c_spin = _spin_constant(ws)
    return _PolyState(n, s.domain, s.sense, s.scale, active, copy(st.fields), adj, st.constant,
                      h_spin, c_spin, c_spin, nothing)
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
    eliminate_variable!(ws, label; map=nothing, tie_break=:low,
                        max_work=typemax(Int), max_exact_work=typemax(Int),
                        deadline_ns=nothing)

Certify and transactionally eliminate a free variable of active degree `0..3`
from `ws`, recording an [`EliminationStep`](@ref) with its exact argmin
reconstruction table and updating surviving neighbor fields, fill edges and
degrees on the reversible trail. Returns an [`UpdateReport`](@ref).
"""
function eliminate_variable!(ws::Workspace, label;
                             map::Union{Nothing,DomainGaugeMap}=nothing,
                             tie_break::Symbol=:low,
                             max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    u = _variable(ws, label)
    st = ws._state
    raw_step, reason, _, visits, _ = _elimination_witness(
        ws, u; map, tie_break, max_work, max_exact_work, deadline_ns,
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
