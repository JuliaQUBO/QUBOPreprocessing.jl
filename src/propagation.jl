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
    sizehint!(st.trail,length(st.trail)+1)
    push!(st.trail,entry)
    st.serial += 1
    st.queued[i] = false
    st.head += 1
    return nothing
end

function _cached_step(ws::Workspace,i::Int,direction::Int)
    st = ws._state
    direction == 0 && return nothing
    lower,upper = direction > 0 ? (st.lower[i],st.upper[i]) : (-st.upper[i],-st.lower[i])
    value = _strict_value(lower,upper,ws._snapshot.domain)
    value === nothing && return nothing
    return DominanceStep(i,value,deepcopy(lower),deepcopy(upper),deepcopy(st.constant),
                         st.proof_count,:exact,length(st.callers))
end

"""
    propagate!(ws; max_work=typemax(Int), max_deductions=typemax(Int),
               max_exact_work=typemax(Int), deadline_ns=nothing)

Run deterministic strict dominance on a workspace selected with
`rules=:dominance`. Exact derivative-bound caches are prepared once and updated
with touched free neighbors; a dirty candidate reads its cached bounds without
rescanning its adjacency. Ties/zero scale produce no fixing. No weak or heuristic
rule is enabled. Calls never build a residual or copy the source graph.

Per-call `max_work` bounds examined candidates plus adjacency entries visited
while installing deductions. Exact work reserves one cached sign check and,
for an attempted update, one constant plus three values per incident edge;
fixed-neighbor skips may make this conservative. Bit complexity is additional.
Reserve complete updates before committing. A refused update leaves its queue
entry pending; its charged check can be repeated on resumption. Stops retain a
sound prefix with `:work_limit`, `:deduction_limit`, `:verification_limit` or
`:deadline`; `:quiescent` means the queue is empty, not solver optimality.

Queue consumption and deductions are trailed. Rollback restores queue/caches/
proofs; execution counters retain actual work. Initialization may scan the graph;
subsequent no-change calls are constant-size. Arbitrary caller unfix conservatively
rebuilds/replays explicit assumptions and discards deductions before resumption.
"""
function propagate!(ws::Workspace;max_work=typemax(Int),max_deductions=typemax(Int),
                     max_exact_work=typemax(Int),deadline_ns=nothing)
    _limits(max_work,deadline_ns)
    _limits(max_deductions,deadline_ns)
    _limits(max_exact_work,deadline_ns)
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
        step = _cached_step(ws,i,direction)
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
        sizehint!(st.trail,length(st.trail)+2)
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
    deductions(ws; since=nothing)

Return owned original-label/value pairs for certified deductions, optionally
added after a valid ancestor checkpoint. Scan only fixing records in that range;
queue-only history and the source graph are not scanned. Caller assumptions
remain available separately through `assumptions`/`changes`.
"""
function deductions(ws::Workspace;since=nothing)
    since === nothing || _validate_checkpoint(ws,since)
    start = since === nothing ? 1 : since._fix_depth+1
    st,s = ws._state,ws._snapshot
    entries = (st.trail[st.fixes[k]] for k in start:length(st.fixes))
    return [_owned_labels([s.labels[e.index]])[1]=>e.value for e in entries if e.proof !== nothing]
end

_proof_steps(ws::Workspace) = Tuple(deepcopy(ws._state.trail[p].proof) for p in ws._state.fixes
                                   if ws._state.trail[p].proof !== nothing)

function _export_certificate(ws::Workspace,source::_Snapshot)
    ws._state.proof_count == 0 && return nothing
    return DominanceCertificate(generation(ws),checkpoint(ws),_caller_scope(ws),_proof_steps(ws),source)
end

"""
    export_certificate(ws)

Explicitly capture the complete owned strong-deduction chain and caller scope,
or return `nothing` in constant-size work if no deduction exists. Source/proof
copying is O(n+m+number of steps), plus scalar bit/label-copy costs. Verify with
`verify_certificate`; applicability requires the captured current trail tip.
No inference, solver dispatch or residual materialization occurs here.
"""
function export_certificate(ws::Workspace)
    ws._state.proof_count == 0 && return nothing
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels,source.labels)
    return _export_certificate(ws,source)
end
