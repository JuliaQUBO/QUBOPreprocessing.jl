# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

function _incremental(s::_Snapshot;rules=:identity)
    n = length(s.labels)
    adjacency = [Pair{Int,_Exact}[] for _ in 1:n]
    fields = fill(_Exact(0), n)
    f = QT.Form{Float64}(n, _thaw(s.linear), _thaw(s.quadratic), s.scale, s.offset;
                         sense=s.sense, domain=s.domain)
    for (i, v) in QT.linear_terms(f)
        fields[i] = _Exact(v)
    end
    for ((i,j), v) in QT.quadratic_terms(f)
        iszero(v) && continue
        q = _Exact(v)
        push!(adjacency[i], j=>q)
        push!(adjacency[j], i=>q)
    end
    degrees = [length(adj) for adj in adjacency]
    dual_fields = Vector{_Exact}(undef, n)
    quad_sum = _Exact(0)
    for i in 1:n
        csum = _Exact(0)
        for (j, q) in adjacency[i]
            csum += q
            i < j && (quad_sum += q)
        end
        dual_fields[i] = s.domain === QT.BoolDomain ? (fields[i] // 2 + csum // 4) :
                                                      (2 * fields[i] - 2 * csum)
    end
    field_sum = sum(fields; init=_Exact(0))
    dual_constant = s.domain === QT.BoolDomain ?
        (_Exact(s.offset) + field_sum // 2 + quad_sum // 4) :
        (_Exact(s.offset) - field_sum + quad_sum)
    lower,upper = nothing,nothing
    if rules === :dominance
        lower,upper = copy(fields),copy(fields)
        for i in 1:n, (_,q) in adjacency[i]
            lower[i] += s.domain === QT.BoolDomain ? min(0,q) : -abs(q)
            upper[i] += s.domain === QT.BoolDomain ? max(0,q) : abs(q)
        end
    end
    queue = rules === :dominance ? collect(1:n) : Int[]
    queued = rules === :dominance ? trues(n) : falses(n)
    return _Incremental(Dict{Any,Int}(v=>i for (i,v) in enumerate(s.labels)),
                        adjacency, fields, _Exact(s.offset), fill(Int8(2), n),
                        queue, queued, _UndoEntry[], 0, uuid4(),rules,lower,upper,1,
                        Int[],Int[],zeros(Int,n),0,0,0,0,dual_fields,dual_constant,degrees)
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
end

"""`checkpoint(ws)` captures a constant-size position without copying the model."""
function checkpoint(ws::Workspace)
    t = ws._state.trail
    return _checkpoint_at(ws,length(t))
end

function _checkpoint_at(ws::Workspace,depth::Int)
    t = ws._state.trail
    return Checkpoint(generation(ws),ws._state.epoch,depth,depth == 0 ? 0 : t[depth].serial,
                      depth == 0 ? 0 : t[depth].fix_depth)
end

function _validate_checkpoint(ws::Workspace, cp::Checkpoint)
    t = ws._state.trail
    cp._generation == generation(ws) && cp._epoch == ws._state.epoch &&
        0 <= cp._depth <= length(t) &&
        (cp._depth == 0 ? cp._serial == 0 && cp._fix_depth == 0 :
            t[cp._depth].serial == cp._serial && t[cp._depth].fix_depth == cp._fix_depth) ||
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
    assume!(ws, label, value; max_work=typemax(Int), deadline_ns=nothing)

Condition on one explicit original-label assignment, never a certified deduction.
Repeat assignments are no-ops, including a matching certified deduction; they
do not promote deductions into independent caller assumptions. Roll back before
imposing such an independent assumption. Conflicts/invalid values throw before mutation.
Reserve the variable's complete adjacency work before starting. A work/deadline
stop leaves state unchanged. Preparation checks the deadline per incident edge;
commit is one atomic algorithmic boundary (not asynchronous interrupt safety).
An applied update costs O(degree), stores touched free fields and queues affected
free neighbors once. Arithmetic uses exact rationals of the stored Float64 data;
integer bit complexity and allocations are additional to edge counts.
"""
function assume!(ws::Workspace, label, value; max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    i, v = _variable(ws, label), _assignment(ws, value)
    st = ws._state
    if st.fixed[i] != 2
        st.fixed[i] == v || throw(ArgumentError("conflicting caller assumption"))
        return UpdateReport(:unchanged, 0, 0)
    end
    return _fix!(ws,i,v;max_work,deadline_ns)
end

function _fix!(ws::Workspace,i::Int,v::Int;proof=nothing,max_work=typemax(Int),deadline_ns=nothing)
    st = ws._state
    st.fixed[i] == 2 || throw(ArgumentError("fixing requires a free variable"))
    edges = st.adjacency[i]
    length(edges) <= max_work || return UpdateReport(:work_limit, 0, 0)
    _expired(deadline_ns) && return UpdateReport(:deadline, 0, 0)
    is_bool = ws._snapshot.domain === QT.BoolDomain
    dual_v = is_bool ? (2 * v - 1) : ((v + 1) ÷ 2)
    old = _NeighborRecord[]
    updated = _NeighborRecord[]
    old_dual = Pair{Int,_Exact}[]
    updated_dual = Pair{Int,_Exact}[]
    visits = 0
    for (j,q) in edges
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits += 1
        st.fixed[j] == 2 || continue
        field = st.fields[j] + q*v
        dual_q = is_bool ? (q // 4) : (4 * q)
        push!(old_dual, j => st.dual_fields[j])
        push!(updated_dual, j => (st.dual_fields[j] + dual_q * dual_v))
        if st.lower === nothing
            push!(old,(j,st.fields[j],st.fields[j],st.fields[j]))
            push!(updated,(j,field,field,field))
        else
            a = is_bool ? min(0,q) : -abs(q)
            b = is_bool ? max(0,q) : abs(q)
            push!(old,(j,st.fields[j],st.lower[j],st.upper[j]))
            push!(updated,(j,field,st.lower[j]+q*v-a,st.upper[j]+q*v-b))
        end
    end
    constant = st.constant + st.fields[i]*v
    dual_constant = st.dual_constant + st.dual_fields[i]*dual_v
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    # Complete allocation before committing field, queue and trail changes.
    sizehint!(st.queue, length(st.queue) + length(updated))
    sizehint!(st.trail, length(st.trail) + 1)
    sizehint!(st.fixes,length(st.fixes)+1)
    proof === nothing && sizehint!(st.callers,length(st.callers)+1)
    entry = _UndoFix(st.serial + 1,length(st.fixes)+1,i,v,st.constant,old,length(st.queue),proof,st.dual_constant,old_dual)
    push!(st.trail, entry)
    push!(st.fixes,length(st.trail))
    proof === nothing ? push!(st.callers,length(st.trail)) : (st.proof_count += 1)
    st.entries[i] = length(st.trail)
    st.serial += 1
    st.constant = constant
    st.dual_constant = dual_constant
    st.fixed[i] = v
    st.degrees[i] = 0
    for (j, df) in updated_dual
        st.dual_fields[j] = df
        st.degrees[j] -= 1
    end
    for (j,field,lower,upper) in updated
        st.fields[j] = field
        if st.lower !== nothing
            st.lower[j],st.upper[j] = lower,upper
        end
        if !st.queued[j]
            push!(st.queue, j)
            st.queued[j] = true
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
    captured = if report
        callers,deductions = Pair{Int,Int}[],Pair{Int,Int}[]
        for k in length(st.fixes):-1:cp._fix_depth+1
            e = st.trail[st.fixes[k]]
            push!(e.proof === nothing ? callers : deductions,e.index=>e.value)
        end
        RollbackReport(generation(ws),cp,callers,deductions)
    else
        nothing
    end
    while length(st.trail) > cp._depth
        undo = pop!(st.trail)
        if undo isa _UndoQueue
            st.head = undo.head
            st.queued[undo.index] = undo.queued
        else
            for (j,field,lower,upper) in undo.fields
                st.fields[j] = field
                if st.lower !== nothing
                    st.lower[j],st.upper[j] = lower,upper
                end
            end
            for (j, df) in undo.dual_fields
                st.dual_fields[j] = df
                st.degrees[j] += 1
            end
            while length(st.queue) > undo.queue_length
                st.queued[pop!(st.queue)] = false
            end
            st.fixed[undo.index] = 2
            st.degrees[undo.index] = length(undo.fields)
            st.entries[undo.index] = 0
            pop!(st.fixes)
            undo.proof === nothing ? pop!(st.callers) : (st.proof_count -= 1)
            st.constant = undo.constant
            st.dual_constant = undo.dual_constant
        end
    end
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
        degree = length(st.adjacency[e.index])
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

"""
    ConditionedExport

Owned historical residual under explicit caller assumptions and/or certified
deductions. `status=:certified` certifies exact algebra/transport within that
scope, not that caller assumptions retain a global optimum. The certificate
contains the ordered strong-deduction proof when present; no solver proof is produced.
Original labels/maps, scope and exact residual data are immutable snapshots;
`export_model` returns a separately owned QUBOTools model.
"""
struct ConditionedExport{T}
    _snapshot::_Snapshot
    generation::Generation
    status::Symbol
    certificate::NamedTuple
    _fixed::Tuple
    _free::Tuple
    _linear::Tuple
    _quadratic::Tuple
    _constant::T
    _scale::T
    _map::Union{Nothing,DomainGaugeMap}
end
ConditionedExport{T}(s,g,st,cert,fix,free,lin,quad,c,sc) where T =
    ConditionedExport{T}(s,g,st,cert,fix,free,lin,quad,c,sc,nothing)
generation(r::ConditionedExport) = r.generation
original_variables(r::ConditionedExport) = _owned_labels(r._snapshot.label_type[r._snapshot.labels...])
function index_map(r::ConditionedExport)
    map = zeros(Int, length(r._fixed))
    for (j,i) in enumerate(r._free)
        map[i] = j
    end
    return map
end

function _transport(::Type{Float64}, q::_Exact)
    v = Float64(q)
    isfinite(v) && _Exact(v) == q || throw(ArgumentError(
        "conditioned coefficient cannot be represented exactly as Float64; use Rational{BigInt}"))
    return v
end
_transport(::Type{_Exact}, q::_Exact) = deepcopy(q)

function _conditioned_export(ws::Workspace, ::Type{T}; map::Union{Nothing,DomainGaugeMap}=nothing) where T
    T in (Float64, _Exact) || throw(ArgumentError("supported transport: Float64 or Rational{BigInt}"))
    map === nothing || _validate_domain_map(ws, map; full=true)
    s, st = ws._snapshot, ws._state
    snapshot = deepcopy(s)
    _validate_label_copy(s.labels, snapshot.labels)
    owned_map = map === nothing ? nothing : deepcopy(map)
    free = findall(==(2), st.fixed)
    idxmap = index_map(ws)
    linear = Tuple(_transport(T, _mapped_field(ws, i, owned_map)) for i in free)
    quadratic = Tuple((idxmap[i],idxmap[j],_transport(T,_mapped_coupling(ws,i,j,q,owned_map)))
                      for i in free for (j,q) in st.adjacency[i] if i < j && st.fixed[j] == 2)
    scope = _caller_scope(ws)
    proof = _export_certificate(ws,snapshot;map=owned_map)
    steps = proof === nothing ? () : proof.steps
    unchanged = isempty(st.fixes) && (owned_map === nothing ||
        (owned_map.target_domain === owned_map.source_domain && owned_map._identity_gauge))
    return ConditionedExport{T}(snapshot, generation(ws), :certified,
        (scope=isempty(scope) ? :original : :assumptions, assumptions=scope,
         reduction_chain=steps, unchanged_representation=unchanged,proof=proof),
        Tuple(st.fixed), Tuple(free), linear, quadratic,
        _transport(T,_mapped_constant(ws,owned_map)), _transport(T,_Exact(s.scale)), owned_map)
end

function export_model(r::ConditionedExport{T}) where T
    s = r._snapshot
    V, U = s.label_type, s.state_type
    labels = original_variables(r)[collect(r._free)]
    vm = QT.VariableMap{V}(Dict{V,Int}(v=>i for (i,v) in enumerate(labels)), labels)
    lf = QT.DictLinearForm{T}(Dict{Int,T}(i=>deepcopy(v) for (i,v) in enumerate(r._linear)))
    qf = QT.DictQuadraticForm{T}(Dict{Tuple{Int,Int},T}((i,j)=>deepcopy(q) for (i,j,q) in r._quadratic))
    dom = r._map === nothing ? s.domain : _qt_domain(r._map.target_domain)
    f = QT.Form{T}(length(labels), lf, qf, deepcopy(r._scale), deepcopy(r._constant);
                   sense=s.sense, domain=dom)
    return QT.Model{V,T,U}(vm, f)
end

function _lift_state(r::ConditionedExport, y::AbstractVector)
    Base.require_one_based_indexing(y)
    length(y) == length(r._free) || throw(ArgumentError("state must cover every free variable"))
    target_dom = r._map === nothing ? _domain_symbol(r._snapshot.domain) : r._map.target_domain
    low = target_dom === :bool ? 0 : -1
    state = Int[r._fixed...]
    for (j,i) in enumerate(r._free)
        v = y[j]
        v isa Real && isfinite(v) && (v == low || v == 1) ||
            throw(ArgumentError("state value is outside the residual domain"))
        iv = Int(v)
        state[i] = r._map === nothing ? iv : _lift_index_value(r._map, i, iv)
    end
    return state
end
function reconstruct(r::ConditionedExport,y::AbstractVector)
    state = _lift_state(r,y)
    return _evaluate_state(r,state,_source_evaluator(r._snapshot))
end
reconstruct(::ConditionedExport, y) = throw(ArgumentError("state must be a complete ordered residual vector"))
