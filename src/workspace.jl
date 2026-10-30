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
    fields::Vector{_Exact},
    dual_fields::Vector{_Exact},
    adjacency::Vector{Vector{Pair{Int,_Exact}}},
    fixed::Union{Nothing,Vector{Int8}},
    u::Int,
)
    h_u = is_bool ? dual_fields[u] : fields[u]
    iszero(h_u) && return true
    abs_h = abs(h_u)
    sum_J = _Exact(0)
    max_J = _Exact(0)
    cnt = 0
    for (w, q) in adjacency[u]
        ((fixed === nothing || fixed[w] == 2) && !iszero(q)) || continue
        cnt += 1
        cnt > 3 && return false
        aJ = abs(is_bool ? (q // 4) : q)
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
    return iszero(_spin_field(ws, u)) || _is_quadratic_deg3(ws, u)
end

function _incremental(s::_Snapshot;rules=:identity)
    n = length(s.labels)
    adjacency = [Pair{Int,_Exact}[] for _ in 1:n]
    adj_pos = [Dict{Int,Int}() for _ in 1:n]
    fields = fill(_Exact(0), n)
    f = QT.Form{Float64}(n, _thaw(s.linear), _thaw(s.quadratic), s.scale, s.offset;
                         sense=s.sense, domain=s.domain)
    for (i, v) in QT.linear_terms(f)
        fields[i] = _to_exact(v)
    end
    deg_init = zeros(Int, n)
    for ((i, j), v) in QT.quadratic_terms(f)
        iszero(v) && continue
        deg_init[i] += 1
        deg_init[j] += 1
    end
    for i in 1:n
        d_i = deg_init[i]
        if d_i > 0
            sizehint!(adjacency[i], d_i)
            sizehint!(adj_pos[i], d_i)
        end
    end
    for ((i,j), v) in QT.quadratic_terms(f)
        iszero(v) && continue
        q = _to_exact(v)
        push!(adjacency[i], j=>q)
        adj_pos[i][j] = length(adjacency[i])
        push!(adjacency[j], i=>q)
        adj_pos[j][i] = length(adjacency[j])
    end
    degrees = deg_init
    initial_degrees = copy(degrees)
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
    offset_ex = _to_exact(s.offset)
    dual_constant = s.domain === QT.BoolDomain ?
        (offset_ex + field_sum // 2 + quad_sum // 4) :
        (offset_ex - field_sum + quad_sum)
    lower,upper = nothing,nothing
    if rules in (:dominance, :elimination, :relations, :mixed)
        lower,upper = copy(fields),copy(fields)
        for i in 1:n, (_,q) in adjacency[i]
            lower[i] += s.domain === QT.BoolDomain ? min(0,q) : -abs(q)
            upper[i] += s.domain === QT.BoolDomain ? max(0,q) : abs(q)
        end
    end
    queue = rules in (:dominance, :elimination, :relations, :mixed) ? collect(1:n) : Int[]
    queued = rules in (:dominance, :elimination, :relations, :mixed) ? trues(n) : falses(n)
    is_bool = s.domain === QT.BoolDomain
    is_quad_deg3(i) = _is_quadratic_deg3(is_bool, fields, dual_fields, adjacency, nothing, i)
    elim_queues = ntuple(b -> Int[i for i in 1:n if degrees[i] == b - 1 && (b < 4 || is_quad_deg3(i))], 4)
    elim_queued = ntuple(b -> BitVector(degrees[i] == b - 1 && (b < 4 || is_quad_deg3(i)) for i in 1:n), 4)
    elim_blocked_fill = ntuple(_ -> fill(typemax(Int), n), 4)
    rel_queue = Int[i for i in 1:n if degrees[i] >= 1]
    rel_queued = BitVector(degrees[i] >= 1 for i in 1:n)
    m_init = sum(degrees; init=0) ÷ 2
    return _Incremental(_label_index_dict(s.labels),
                        adjacency, adj_pos, fields, _Exact(s.offset), fill(Int8(2), n),
                        queue, queued, _UndoEntry[], 0, uuid4(),rules,lower,upper,1,
                        Int[],Int[],zeros(Int,n),0,0,0,0,0,0,dual_fields,dual_constant,
                        degrees, initial_degrees, elim_queues, elim_queued, [1, 1, 1, 1],
                        elim_blocked_fill,
                        rel_queue, rel_queued, 1, fill(typemax(Int), n), trues(n),
                        (Int[], Int[], Int[], Int[]), Int[], Int[], 0,
                        m_init, m_init, 1, 1)
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
assumptions before imposing the new assumption.
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
        replay_count = length(st.callers) - c_idx + 1
        replay_list = Vector{Pair{Int,Int}}(undef, replay_count)
        for (offset, k) in enumerate(replay_start:length(st.callers))
            e = st.trail[st.callers[k]]::_UndoFix
            replay_list[offset] = e.index => e.value
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
        return UpdateReport(:applied, total_visits, 1)
    end
    return _fix!(ws, i, v; max_work, deadline_ns)
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
    sizehint!(old, length(edges))
    sizehint!(updated, length(edges))
    sizehint!(old_dual, length(edges))
    sizehint!(updated_dual, length(edges))
    visits = 0
    for (j,q) in edges
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits += 1
        st.fixed[j] == 2 || continue
        field = v == 0 ? st.fields[j] : (v == 1 ? (st.fields[j] + q) : (st.fields[j] - q))
        df_new = if dual_v == 0
            st.dual_fields[j]
        else
            dual_q = is_bool ? (q // 4) : (4 * q)
            dual_v == 1 ? (st.dual_fields[j] + dual_q) : (st.dual_fields[j] - dual_q)
        end
        push!(old_dual, j => st.dual_fields[j])
        push!(updated_dual, j => df_new)
        if st.lower === nothing
            push!(old,(j,st.fields[j],st.fields[j],st.fields[j]))
            push!(updated,(j,field,field,field))
        else
            new_lo, new_hi = if is_bool
                if v == 0
                    q >= 0 ? (st.lower[j], st.upper[j] - q) : (st.lower[j] - q, st.upper[j])
                else
                    q >= 0 ? (st.lower[j] + q, st.upper[j]) : (st.lower[j], st.upper[j] + q)
                end
            else
                if (v == 1 && q >= 0) || (v == -1 && q <= 0)
                    (st.lower[j] + 2 * abs(q), st.upper[j])
                else
                    (st.lower[j], st.upper[j] - 2 * abs(q))
                end
            end
            push!(old,(j,st.fields[j],st.lower[j],st.upper[j]))
            push!(updated,(j,field,new_lo,new_hi))
        end
    end
    constant = v == 0 ? st.constant : (v == 1 ? (st.constant + st.fields[i]) : (st.constant - st.fields[i]))
    dual_constant = dual_v == 0 ? st.dual_constant : (dual_v == 1 ? (st.dual_constant + st.dual_fields[i]) : (st.dual_constant - st.dual_fields[i]))
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    # Complete allocation before committing field, queue and trail changes.
    _reserve!(st.queue, length(st.queue) + length(updated))
    for b in 1:4
        _reserve!(st.elim_queues[b], length(st.elim_queues[b]) + length(updated))
    end
    _reserve!(st.rel_queue, length(st.rel_queue) + length(updated))
    _reserve!(st.trail, length(st.trail) + 1)
    _reserve!(st.fixes, length(st.fixes) + 1)
    proof === nothing && _reserve!(st.callers, length(st.callers) + 1)
    elim_lens = ntuple(b -> length(st.elim_queues[b]), 4)
    entry = _UndoFix(st.serial + 1,length(st.fixes)+1,i,v,st.constant,old,length(st.queue),proof,st.dual_constant,old_dual,elim_lens,length(st.rel_queue))
    push!(st.trail, entry)
    push!(st.fixes,length(st.trail))
    if proof === nothing
        push!(st.callers,length(st.trail))
    else
        st.proof_count == 0 && (st.first_proof_pos = length(st.trail))
        st.proof_count += 1
        (proof isa ProbingStep || proof isa RoofDualityStep || proof isa SubmodularCutStep || proof isa MaxCutStep ||
         (hasproperty(proof, :method) && proof.method === :marginal)) &&
            (st.marginal_count += 1)
    end
    st.entries[i] = length(st.trail)
    st.serial += 1
    st.constant = constant
    st.dual_constant = dual_constant
    st.fixed[i] = v
    st.degrees[i] = 0
    st.active_edges -= length(updated_dual)
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
    for (j, df) in updated_dual
        st.dual_fields[j] = df
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

function _adj_set!(st::_Incremental, adj_edits::Vector{_AdjacencyEdit}, a::Int, b::Int, q_new::_Exact)
    pos = get(st.adj_pos[a], b, 0)
    if pos == 0
        !iszero(q_new) || return nothing
        push!(st.adjacency[a], b => q_new)
        st.adj_pos[a][b] = length(st.adjacency[a])
        push!(adj_edits, (:pop, a, 0, b => _Exact(0)))
    else
        old_pair = st.adjacency[a][pos]
        if iszero(q_new)
            last_pos = length(st.adjacency[a])
            if pos != last_pos
                tail_pair = st.adjacency[a][last_pos]
                st.adjacency[a][pos] = tail_pair
                st.adj_pos[a][tail_pair.first] = pos
            end
            pop!(st.adjacency[a])
            delete!(st.adj_pos[a], b)
            push!(adj_edits, (:swap_remove, a, pos, old_pair))
        else
            st.adjacency[a][pos] = b => q_new
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
    is_bool = ws._snapshot.domain === QT.BoolDomain
    visits = precharged_visits
    u_free_edges = Pair{Int,_Exact}[]
    touched = Int[]
    touched_seen = Set{Int}()
    for (w, q) in st.adjacency[u]
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
    merged_q = Dict{Tuple{Int,Int},_Exact}()
    merged_order = Tuple{Int,Int}[]
    for (a, b, dq) in quad_deltas
        iszero(dq) && continue
        a != b && a != u && b != u && st.fixed[a] == 2 && st.fixed[b] == 2 ||
            throw(ArgumentError("quadratic delta targets non-free or identical variables"))
        j, k = min(a, b), max(a, b)
        !haskey(merged_q, (j, k)) && push!(merged_order, (j, k))
        merged_q[(j, k)] = get(merged_q, (j, k), _Exact(0)) + dq
        _touch!(touched, touched_seen, j)
        _touch!(touched, touched_seen, k)
    end
    merged_quad_deltas = Tuple{Int,Int,_Exact}[
        (j, k, merged_q[(j, k)]) for (j, k) in merged_order if !iszero(merged_q[(j, k)])
    ]
    for _ in merged_quad_deltas
        2 <= max_work - visits || return UpdateReport(:work_limit, visits, 0)
        _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
        visits += 2
    end
    old_fields = Vector{_NeighborRecord}(undef, length(touched))
    old_dual = Vector{_DualDegreeRecord}(undef, length(touched) + 1)
    old_dual[1] = (u, st.dual_fields[u], st.degrees[u])
    for (idx, w) in enumerate(touched)
        lo_w = st.lower === nothing ? st.fields[w] : st.lower[w]
        hi_w = st.upper === nothing ? st.fields[w] : st.upper[w]
        old_fields[idx] = (w, st.fields[w], lo_w, hi_w)
        old_dual[idx + 1] = (w, st.dual_fields[w], st.degrees[w])
    end
    f_map = Dict{Int,_Exact}(w => _Exact(0) for w in touched)
    lo_map = Dict{Int,_Exact}(w => _Exact(0) for w in touched)
    hi_map = Dict{Int,_Exact}(w => _Exact(0) for w in touched)
    qsum_map = Dict{Int,_Exact}(w => _Exact(0) for w in touched)
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
        q_old = pos_j == 0 ? _Exact(0) : st.adjacency[j][pos_j].second
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
    old_f_u = st.fields[u]
    old_h_u = _spin_field(ws, u)
    total_f_delta = -old_f_u + sum(values(f_map); init=_Exact(0))
    total_q_delta = -sum((q for (_, q) in u_free_edges); init=_Exact(0)) +
                    sum((dq for (_, _, dq) in merged_quad_deltas); init=_Exact(0))
    new_constant = st.constant + const_delta
    new_dual_constant = is_bool ?
        (st.dual_constant + const_delta + total_f_delta // 2 + total_q_delta // 4) :
        (st.dual_constant + const_delta - total_f_delta + total_q_delta)
    spin_const_delta = is_bool ? (new_dual_constant - st.dual_constant) : const_delta
    spin_field_deltas = Pair{Int,_Exact}[u => -old_h_u]
    for w in touched
        dh_w = is_bool ? (f_map[w] // 2 + qsum_map[w] // 4) : f_map[w]
        !iszero(dh_w) && push!(spin_field_deltas, w => dh_w)
    end
    spin_coupling_deltas = Tuple{Int,Int,_Exact}[]
    for (w, q_uw) in u_free_edges
        push!(spin_coupling_deltas, (min(u, w), max(u, w), -_spin_coupling(ws, q_uw)))
    end
    for (j, k, dq) in merged_quad_deltas
        push!(spin_coupling_deltas, (j, k, _spin_coupling(ws, dq)))
    end
    _expired(deadline_ns) && return UpdateReport(:deadline, visits, 0)
    st.serial == typemax(UInt64) && throw(ArgumentError("trail serial exhausted; reset workspace"))
    _reserve!(st.queue, length(st.queue) + length(touched))
    for b in 1:4
        _reserve!(st.elim_queues[b], length(st.elim_queues[b]) + length(touched))
    end
    _reserve!(st.rel_queue, length(st.rel_queue) + length(touched))
    _reserve!(st.trail, length(st.trail) + 1)
    _reserve!(st.fixes, length(st.fixes) + 1)
    for w in touched
        grow_map[w] > 0 && _reserve!(st.adjacency[w], length(st.adjacency[w]) + grow_map[w])
    end
    adj_edits = _AdjacencyEdit[]
    _reserve!(adj_edits, length(u_free_edges) + 2 * length(merged_quad_deltas))
    for (w, _) in u_free_edges
        _adj_set!(st, adj_edits, w, u, _Exact(0))
    end
    for (j, k, dq) in merged_quad_deltas
        pos_j = get(st.adj_pos[j], k, 0)
        q_old = pos_j == 0 ? _Exact(0) : st.adjacency[j][pos_j].second
        q_new = q_old + dq
        _adj_set!(st, adj_edits, j, k, q_new)
        _adj_set!(st, adj_edits, k, j, q_new)
    end
    elim_lens = ntuple(b -> length(st.elim_queues[b]), 4)
    entry = _UndoReduction(
        st.serial + 1,
        length(st.fixes) + 1,
        u,
        status,
        st.constant,
        st.dual_constant,
        old_fields,
        old_dual,
        adj_edits,
        length(st.queue),
        proof,
        spin_const_delta,
        spin_field_deltas,
        spin_coupling_deltas,
        elim_lens,
        length(st.rel_queue),
    )
    push!(st.trail, entry)
    push!(st.fixes, length(st.trail))
    st.proof_count == 0 && (st.first_proof_pos = length(st.trail))
    st.proof_count += 1
    (proof isa MaxCutStep || (proof isa RelationStep && proof.method in (:probing_pair, :roof_scc_pair))) && (st.marginal_count += 1)
    st.entries[u] = length(st.trail)
    st.serial += 1
    st.constant = new_constant
    st.dual_constant = new_dual_constant
    st.fixed[u] = status
    st.degrees[u] = 0
    st.active_edges += (-old_dual[1][3] + sum(values(deg_map); init=0)) ÷ 2
    for w in touched
        st.fields[w] += f_map[w]
        st.dual_fields[w] += is_bool ? (f_map[w] // 2 + qsum_map[w] // 4) :
                                       (2 * f_map[w] - 2 * qsum_map[w])
        st.degrees[w] += deg_map[w]
        if st.lower !== nothing
            st.lower[w] += lo_map[w]
            st.upper[w] += hi_map[w]
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
    captured = if report
        callers,deductions = Pair{Int,Int}[],Pair{Int,Int}[]
        for k in length(st.fixes):-1:cp._fix_depth+1
            e = st.trail[st.fixes[k]]
            if e isa _UndoFix
                push!(e.proof === nothing ? callers : deductions,e.index=>e.value)
            end
        end
        RollbackReport(generation(ws),cp,callers,deductions)
    else
        nothing
    end
    while length(st.trail) > cp._depth
        undo = pop!(st.trail)
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
                    popped = pop!(st.adjacency[a])
                    delete!(st.adj_pos[a], popped.first)
                elseif op === :swap_remove
                    if pos <= length(st.adjacency[a])
                        moved_pair = st.adjacency[a][pos]
                        push!(st.adjacency[a], moved_pair)
                        st.adj_pos[a][moved_pair.first] = length(st.adjacency[a])
                        st.adjacency[a][pos] = old_pair
                    else
                        push!(st.adjacency[a], old_pair)
                    end
                    st.adj_pos[a][old_pair.first] = pos
                else
                    st.adjacency[a][pos] = old_pair
                end
            end
            for (j, field, lower, upper) in undo.fields
                st.fields[j] = field
                if st.lower !== nothing
                    st.lower[j], st.upper[j] = lower, upper
                end
            end
            deg_delta = 0
            for (j, df, deg) in undo.dual_fields
                deg_delta += deg - st.degrees[j]
                st.dual_fields[j] = df
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
            st.constant = undo.constant
            st.dual_constant = undo.dual_constant
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
            st.constant = undo.constant
            st.dual_constant = undo.dual_constant
        end
    end
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
generation(r::ConditionedExport) = r.generation
original_variables(r::ConditionedExport) = _labels_vector(r._snapshot)

function Base.deepcopy_internal(r::ConditionedExport{T}, dict::IdDict) where T
    haskey(dict, r) && return dict[r]::ConditionedExport{T}
    cert_copy = (
        scope=r.certificate.scope,
        assumptions=_deepcopy_tuple(r.certificate.assumptions, dict),
        reduction_chain=_deepcopy_tuple(r.certificate.reduction_chain, dict),
        unchanged_representation=r.certificate.unchanged_representation,
        proof=Base.deepcopy_internal(r.certificate.proof, dict),
    )
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
        map[free[j]::Int] = j
    end
    return map
end

function index_map(r::ConditionedExport)
    map = zeros(Int, length(r._fixed))
    return _fill_index_map!(map, r._free)
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
    c_export = _direct_mapped_constant(ws, owned_map)
    return ConditionedExport{T}(snapshot, generation(ws), :certified,
        (scope=isempty(scope) ? :original : :assumptions, assumptions=scope,
         reduction_chain=steps, unchanged_representation=unchanged,proof=proof),
        Tuple(st.fixed), Tuple(free), linear, quadratic,
        _transport(T, c_export), _transport(T,_Exact(s.scale)), owned_map)
end

function _build_export_linear(::Type{T}, @nospecialize(lin::Tuple)) where T
    n = length(lin)
    d = Dict{Int,T}()
    sizehint!(d, n)
    for i in 1:n
        d[i] = deepcopy(lin[i]::T)
    end
    return QT.DictLinearForm{T}(d)
end

function _build_export_quadratic(::Type{T}, @nospecialize(quad::Tuple)) where T
    m = length(quad)
    d = Dict{Tuple{Int,Int},T}()
    sizehint!(d, m)
    for k in 1:m
        item = quad[k]::Tuple{Int,Int,T}
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
        i = free[j]::Int
        v = y[j]
        v isa Real && isfinite(v) && (v == low || v == 1) ||
            throw(ArgumentError("state value is outside the residual domain"))
        iv = Int(v)
        state[i] = r._map === nothing ? iv : _lift_index_value(r._map, i, iv)
    end
    for k in length(steps):-1:1
        step = steps[k]
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
