# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

function _incremental(s::_Snapshot)
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
    return _Incremental(Dict{Any,Int}(v=>i for (i,v) in enumerate(s.labels)),
                        adjacency, fields, _Exact(s.offset), fill(Int8(2), n),
                        Int[], falses(n), _UndoFix[], 0, uuid4())
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
end

"""`checkpoint(ws)` captures a constant-size position without copying the model."""
function checkpoint(ws::Workspace)
    t = ws._state.trail
    return Checkpoint(generation(ws), ws._state.epoch, length(t), isempty(t) ? 0 : t[end].serial)
end

function _validate_checkpoint(ws::Workspace, cp::Checkpoint)
    t = ws._state.trail
    cp._generation == generation(ws) && cp._epoch == ws._state.epoch &&
        0 <= cp._depth <= length(t) &&
        (cp._depth == 0 ? cp._serial == 0 : t[cp._depth].serial == cp._serial) ||
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
Repeat assignments are no-ops; conflicts/invalid values throw before mutation.
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
    edges = st.adjacency[i]
    length(edges) <= max_work || return UpdateReport(:work_limit, 0, 0)
    _expired(deadline_ns) && return UpdateReport(:deadline, 0, 0)
    old = Pair{Int,_Exact}[]
    updated = Pair{Int,_Exact}[]
    visits = 0
    for (j,q) in edges
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits += 1
        st.fixed[j] == 2 || continue
        push!(old, j=>st.fields[j])
        push!(updated, j=>(st.fields[j] + q*v))
    end
    constant = st.constant + st.fields[i]*v
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    # Complete allocation before committing field, queue and trail changes.
    sizehint!(st.queue, length(st.queue) + length(updated))
    sizehint!(st.trail, length(st.trail) + 1)
    entry = _UndoFix(st.serial + 1, i, v, st.constant, old, length(st.queue))
    push!(st.trail, entry)
    st.serial += 1
    st.constant = constant
    st.fixed[i] = v
    for (j,field) in updated
        st.fields[j] = field
        if !st.queued[j]
            push!(st.queue, j)
            st.queued[j] = true
        end
    end
    return UpdateReport(:applied, visits, 1)
end

"""
    rollback!(ws, checkpoint)

Restore fields, constant, free/fixed values, queue flags and assumptions exactly
in reverse trail order. Cost is proportional to undone entries/touched fields
and appended queue entries. No source graph copy or floating subtraction occurs.
Invalid checkpoints fail before mutation. Rollback completes without a work or
deadline limit; callers bound its cost by bounding preceding updates.
"""
function rollback!(ws::Workspace, cp::Checkpoint)
    _validate_checkpoint(ws, cp)
    st = ws._state
    while length(st.trail) > cp._depth
        undo = pop!(st.trail)
        for (j,field) in undo.fields
            st.fields[j] = field
        end
        while length(st.queue) > undo.queue_length
            st.queued[pop!(st.queue)] = false
        end
        st.fixed[undo.index] = 2
        st.constant = undo.constant
    end
    return ws
end

"""
    assumptions(ws)

Return owned original-label/value pairs in application order, O(k) for k active
assumptions. No graph scan, residual construction or proof claim is involved.
"""
function assumptions(ws::Workspace)
    s = ws._snapshot
    return [_owned_labels([s.labels[e.index]])[1]=>e.value for e in ws._state.trail]
end

"""
    changes(ws, checkpoint)

Return owned caller assumptions added since a still-valid ancestor checkpoint,
in application order; O(number of changes), with no full residual copy.
"""
function changes(ws::Workspace, cp::Checkpoint)
    _validate_checkpoint(ws, cp)
    s, t = ws._snapshot, ws._state.trail
    return [_owned_labels([s.labels[t[k].index]])[1]=>t[k].value for k in cp._depth+1:length(t)]
end

"""
    unfix!(ws, label; max_work=typemax(Int), deadline_ns=nothing)

Remove a caller assumption. The most recent one rolls back locally. Otherwise
build fresh algebra and replay all retained assumptions, then replace state only
on success; every prior checkpoint is invalidated. This conservative path costs
O(n+m + retained adjacency work), plus exact arithmetic, and allocates a new
workspace state. `max_work` bounds replay adjacency visits, not initialization;
the latter always costs O(n+m). Deadline/work stops preserve the old state.
No inferred deductions exist yet; their invalidation belongs to issue #5.
"""
function unfix!(ws::Workspace, label; max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work, deadline_ns)
    i = _variable(ws, label)
    st = ws._state
    st.fixed[i] == 2 && return UpdateReport(:unchanged, 0, 0)
    _expired(deadline_ns) && return UpdateReport(:deadline, 0, 0)
    if st.trail[end].index == i
        d = length(st.trail)-1
        cp = Checkpoint(generation(ws), st.epoch, d, d == 0 ? 0 : st.trail[d].serial)
        rollback!(ws, cp)
        return UpdateReport(:applied, 0, 1)
    end
    work = 0
    for e in st.trail
        e.index == i && continue
        degree = length(st.adjacency[e.index])
        degree <= max_work - work || return UpdateReport(:work_limit, 0, 0)
        work += degree
    end
    staged = Workspace(ws._snapshot, generation(ws), _incremental(ws._snapshot))
    visits = 0
    for e in st.trail
        e.index == i && continue
        r = assume!(staged, ws._snapshot.labels[e.index], e.value; max_work=max_work-visits, deadline_ns)
        visits += r.edge_visits
        r.stop_reason === :applied || return UpdateReport(r.stop_reason, visits, 0)
    end
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
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

Owned historical residual under explicit caller assumptions. `status=:certified`
certifies exact algebra/transport within that scope, not that the assumptions
retain a global optimum. No inference certificate or solver proof is produced.
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
end
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

function _conditioned_export(ws::Workspace, ::Type{T}) where T
    T in (Float64, _Exact) || throw(ArgumentError("supported transport: Float64 or Rational{BigInt}"))
    s, st = ws._snapshot, ws._state
    snapshot = deepcopy(s)
    _validate_label_copy(s.labels, snapshot.labels)
    free = findall(==(2), st.fixed)
    map = index_map(ws)
    linear = Tuple(_transport(T, st.fields[i]) for i in free)
    quadratic = Tuple((map[i],map[j],_transport(T,q)) for i in free for (j,q) in st.adjacency[i]
                      if i < j && st.fixed[j] == 2)
    scope = Tuple(e.index=>e.value for e in st.trail)
    return ConditionedExport{T}(snapshot, generation(ws), :certified,
        (scope=:assumptions, assumptions=scope, reduction_chain=(), unchanged_representation=false),
        Tuple(st.fixed), Tuple(free), linear, quadratic,
        _transport(T,st.constant), _transport(T,_Exact(s.scale)))
end

function export_model(r::ConditionedExport{T}) where T
    s = r._snapshot
    V, U = s.label_type, s.state_type
    labels = original_variables(r)[collect(r._free)]
    vm = QT.VariableMap{V}(Dict{V,Int}(v=>i for (i,v) in enumerate(labels)), labels)
    lf = QT.DictLinearForm{T}(Dict{Int,T}(i=>deepcopy(v) for (i,v) in enumerate(r._linear)))
    qf = QT.DictQuadraticForm{T}(Dict{Tuple{Int,Int},T}((i,j)=>deepcopy(q) for (i,j,q) in r._quadratic))
    f = QT.Form{T}(length(labels), lf, qf, deepcopy(r._scale), deepcopy(r._constant);
                   sense=s.sense, domain=s.domain)
    return QT.Model{V,T,U}(vm, f)
end

function reconstruct(r::ConditionedExport, y::AbstractVector)
    Base.require_one_based_indexing(y)
    length(y) == length(r._free) || throw(ArgumentError("state must cover every free variable"))
    low = r._snapshot.domain === QT.BoolDomain ? 0 : -1
    state = Int[r._fixed...]
    for (j,i) in enumerate(r._free)
        v = y[j]
        v isa Real && isfinite(v) && (v == low || v == 1) ||
            throw(ArgumentError("state value is outside the original domain"))
        state[i] = Int(v)
    end
    identity = ExportResult(r._snapshot, generation(r), :certified,
                            (scope=:original, reduction_chain=(), unchanged_representation=true))
    return reconstruct(identity, state)
end
reconstruct(::ConditionedExport, y) = throw(ArgumentError("state must be a complete ordered residual vector"))
