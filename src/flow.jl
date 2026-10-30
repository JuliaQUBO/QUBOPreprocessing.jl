# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

mutable struct _FlowEdge
    to::Int
    rev::Int
    cap::_Exact
    flow::_Exact
end

struct _FlowNetwork
    n_verts::Int
    source::Int
    sink::Int
    adj::Vector{Vector{_FlowEdge}}
end

function _FlowNetwork(n_verts::Int, source::Int, sink::Int)
    adj = [_FlowEdge[] for _ in 1:n_verts]
    return _FlowNetwork(n_verts, source, sink, adj)
end

function _add_directed_pair!(net::_FlowNetwork, u::Int, v::Int, cap_uv::_Exact, cap_vu::_Exact)
    (u == v || (cap_uv <= 0 && cap_vu <= 0)) && return nothing
    idx_u = length(net.adj[u]) + 1
    idx_v = length(net.adj[v]) + 1
    push!(net.adj[u], _FlowEdge(v, idx_v, cap_uv, _Exact(0)))
    push!(net.adj[v], _FlowEdge(u, idx_u, cap_vu, _Exact(0)))
    return nothing
end

function _dinic_bfs!(
    net::_FlowNetwork,
    level::Vector{Int},
    queue::Vector{Int};
    max_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    fill!(level, -1)
    level[net.source] = 0
    queue[1] = net.source
    head = 1
    tail = 1
    visits = 0
    while head <= tail
        _expired(deadline_ns) && return (:deadline, visits)
        u = queue[head]
        head += 1
        lu = level[u] + 1
        for e in net.adj[u]
            _expired(deadline_ns) && return (:deadline, visits)
            visits < max_work || return (:work_limit, visits)
            visits += 1
            if e.cap > e.flow && level[e.to] == -1
                level[e.to] = lu
                tail += 1
                queue[tail] = e.to
            end
        end
    end
    return (level[net.sink] != -1 ? :reachable : :done, visits)
end

function _dinic_dfs!(
    net::_FlowNetwork,
    u::Int,
    pushed::_Exact,
    level::Vector{Int},
    ptr::Vector{Int},
    work_ref::Base.RefValue{Int},
    exact_ref::Base.RefValue{Int},
    stop_ref::Base.RefValue{Symbol},
    max_work::Int,
    max_exact_work::Int,
    deadline_ns,
)
    iszero(pushed) && return _Exact(0)
    u == net.sink && return pushed
    adj_u = net.adj[u]
    n_edges = length(adj_u)
    while ptr[u] <= n_edges
        if _expired(deadline_ns)
            stop_ref[] = :deadline
            return _Exact(0)
        end
        if work_ref[] >= max_work
            stop_ref[] = :work_limit
            return _Exact(0)
        end
        work_ref[] += 1
        cid = ptr[u]
        e = adj_u[cid]
        tr = e.to
        if level[u] + 1 == level[tr] && e.cap > e.flow
            if exact_ref[] >= max_exact_work
                stop_ref[] = :verification_limit
                return _Exact(0)
            end
            exact_ref[] += 1
            avail = e.cap - e.flow
            tr_pushed = _dinic_dfs!(
                net, tr, min(pushed, avail),
                level, ptr, work_ref, exact_ref, stop_ref,
                max_work, max_exact_work, deadline_ns,
            )
            stop_ref[] === :ok || return _Exact(0)
            if tr_pushed > 0
                if exact_ref[] >= max_exact_work
                    stop_ref[] = :verification_limit
                    return _Exact(0)
                end
                exact_ref[] += 1
                e.flow += tr_pushed
                net.adj[tr][e.rev].flow -= tr_pushed
                return tr_pushed
            end
        end
        ptr[u] += 1
    end
    return _Exact(0)
end

function _dinic_max_flow!(
    net::_FlowNetwork;
    max_work::Int=typemax(Int),
    max_exact_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    level = fill(-1, net.n_verts)
    ptr = fill(1, net.n_verts)
    queue = Vector{Int}(undef, net.n_verts)
    work_ref = Ref(0)
    exact_ref = Ref(0)
    stop_ref = Ref(:ok)
    total_flow = _Exact(0)
    INF = typemax(Int64) // 1
    for u in 1:net.n_verts
        for e in net.adj[u]
            e.cap > 0 && (INF += e.cap)
        end
    end
    while true
        _expired(deadline_ns) && return (false, :deadline, total_flow, work_ref[], exact_ref[])
        bfs_status, bfs_visits = _dinic_bfs!(
            net, level, queue;
            max_work=max_work - work_ref[], deadline_ns=deadline_ns,
        )
        work_ref[] += bfs_visits
        bfs_status === :deadline && return (false, :deadline, total_flow, work_ref[], exact_ref[])
        bfs_status === :work_limit && return (false, :work_limit, total_flow, work_ref[], exact_ref[])
        bfs_status === :done && break
        fill!(ptr, 1)
        while true
            pushed = _dinic_dfs!(
                net, net.source, INF,
                level, ptr, work_ref, exact_ref, stop_ref,
                max_work, max_exact_work, deadline_ns,
            )
            stop_ref[] === :ok || return (false, stop_ref[], total_flow, work_ref[], exact_ref[])
            iszero(pushed) && break
            total_flow += pushed
        end
    end
    return (true, :ok, total_flow, work_ref[], exact_ref[])
end

function _residual_reachability(net::_FlowNetwork)
    R_S = falses(net.n_verts)
    R_T = falses(net.n_verts)
    queue = Vector{Int}(undef, net.n_verts)
    visits = 0

    # Forward residual reachability from source: e.cap - e.flow > 0
    R_S[net.source] = true
    queue[1] = net.source
    head = 1
    tail = 1
    while head <= tail
        u = queue[head]
        head += 1
        for e in net.adj[u]
            visits += 1
            if e.cap > e.flow && !R_S[e.to]
                R_S[e.to] = true
                tail += 1
                queue[tail] = e.to
            end
        end
    end

    # Backward residual reachability to sink: reverse edge rev_e has rev_e.cap - rev_e.flow > 0
    R_T[net.sink] = true
    queue[1] = net.sink
    head = 1
    tail = 1
    while head <= tail
        v = queue[head]
        head += 1
        for e in net.adj[v]
            visits += 1
            u = e.to
            rev_e = net.adj[u][e.rev]
            if rev_e.cap > rev_e.flow && !R_T[u]
                R_T[u] = true
                tail += 1
                queue[tail] = u
            end
        end
    end

    return (R_S, R_T, visits)
end

function _extract_flow_edges(net::_FlowNetwork)
    edges = Tuple{Int,Int,_Exact}[]
    for u in 1:net.n_verts
        for e in net.adj[u]
            if e.flow > 0
                push!(edges, (u, e.to, deepcopy(e.flow)))
            end
        end
    end
    sort!(edges; by=x -> (x[1], x[2]))
    return Tuple(edges)
end

function _verify_flow_and_reachability!(
    net::_FlowNetwork,
    flow_edges::Tuple{Vararg{Tuple{Int,Int,_Exact}}},
    claimed_max_flow::_Exact,
    deadline=nothing,
)
    claimed_max_flow >= 0 || return (false, :invalid_flow, 0, falses(0), falses(0))
    visits = 0
    net_out = zeros(_Exact, net.n_verts)
    prev_ab = (0, 0)
    for (a, b, f_ab) in flow_edges
        _expired(deadline) && return (false, :deadline, visits, falses(0), falses(0))
        visits += 1
        (1 <= a <= net.n_verts && 1 <= b <= net.n_verts && a != b) ||
            return (false, :invalid_flow, visits, falses(0), falses(0))
        (a, b) > prev_ab || return (false, :invalid_flow, visits, falses(0), falses(0))
        prev_ab = (a, b)
        f_ab > 0 || return (false, :invalid_flow, visits, falses(0), falses(0))
        adj_a = net.adj[a]
        pos = findfirst(e -> e.to == b, adj_a)
        pos !== nothing || return (false, :invalid_flow, visits, falses(0), falses(0))
        e = adj_a[pos]
        (iszero(e.flow) && f_ab <= e.cap) || return (false, :invalid_flow, visits, falses(0), falses(0))
        e.flow = f_ab
        net.adj[b][e.rev].flow = -f_ab
        net_out[a] += f_ab
        net_out[b] -= f_ab
    end
    for v in 1:net.n_verts
        _expired(deadline) && return (false, :deadline, visits, falses(0), falses(0))
        visits += 1
        if v == net.source
            net_out[v] == claimed_max_flow || return (false, :invalid_flow, visits, falses(0), falses(0))
        elseif v == net.sink
            net_out[v] == -claimed_max_flow || return (false, :invalid_flow, visits, falses(0), falses(0))
        else
            iszero(net_out[v]) || return (false, :invalid_flow, visits, falses(0), falses(0))
        end
    end
    R_S, R_T, reach_visits = _residual_reachability(net)
    visits += reach_visits
    (!R_S[net.sink] && !R_T[net.source]) || return (false, :invalid_cut, visits, R_S, R_T)
    cut_S = _Exact(0)
    cut_T = _Exact(0)
    for u in 1:net.n_verts
        _expired(deadline) && return (false, :deadline, visits, R_S, R_T)
        for e in net.adj[u]
            visits += 1
            e.cap > 0 || continue
            if R_S[u] && !R_S[e.to]
                cut_S += e.cap
            end
            if !R_T[u] && R_T[e.to]
                cut_T += e.cap
            end
        end
    end
    (cut_S == claimed_max_flow && cut_T == claimed_max_flow) ||
        return (false, :invalid_cut, visits, R_S, R_T)
    return (true, :verified, visits, R_S, R_T)
end

function _cut_capacity(net::_FlowNetwork, in_S::BitVector)
    cap = _Exact(0)
    for u in 1:net.n_verts
        in_S[u] || continue
        for e in net.adj[u]
            (!in_S[e.to] && e.cap > 0) && (cap += e.cap)
        end
    end
    return cap
end

@inline _lit_complement(a::Int) = isodd(a) ? (a + 1) : (a - 1)
@inline _lit_var(a::Int) = (a + 1) >> 1
@inline _lit_spin(a::Int) = isodd(a) ? 1 : -1

function _symmetrized_residual_cap(net::_FlowNetwork, a::Int, idx::Int, e::_FlowEdge)
    b = e.to
    n_lit = net.n_verts - 2
    (1 <= a <= n_lit && 1 <= b <= n_lit && _lit_var(a) != _lit_var(b)) || return _Exact(0)
    r_ab = e.cap - e.flow
    bar_a = _lit_complement(a)
    bar_b = _lit_complement(b)
    adj_bar_a = net.adj[bar_a]
    r_dual = _Exact(0)
    if idx <= length(adj_bar_a) && adj_bar_a[idx].to == bar_b
        e_bar_a = adj_bar_a[idx]
        dual_e = net.adj[bar_b][e_bar_a.rev]
        r_dual = dual_e.cap - dual_e.flow
    end
    return r_ab + r_dual
end

function _half_integral_literals(net::_FlowNetwork, R_S::BitVector, R_T::BitVector, active_var_fn)
    n_lit = net.n_verts - 2
    n = n_lit >> 1
    in_half = falses(n_lit)
    for u in 1:n
        active_var_fn(u) || continue
        a_pos = 2 * u - 1
        a_neg = 2 * u
        if !R_S[a_pos] && !R_T[a_pos] && !R_S[a_neg] && !R_T[a_neg]
            in_half[a_pos] = true
            in_half[a_neg] = true
        end
    end
    return in_half
end

function _tarjan_residual_sccs(
    net::_FlowNetwork,
    in_half::BitVector,
    min_sym_cap::_Exact;
    max_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    n_lit = length(in_half)
    disc = zeros(Int, n_lit)
    low = zeros(Int, n_lit)
    on_stack = falses(n_lit)
    scc_id = zeros(Int, n_lit)
    sccs = Vector{Int}[]
    tarjan_stack = Int[]
    call_u = Int[]
    call_idx = Int[]
    timer = 0
    visits = 0
    for start in 1:n_lit
        (in_half[start] && disc[start] == 0) || continue
        _expired(deadline_ns) && return (false, :deadline, scc_id, sccs, visits)
        visits < max_work || return (false, :work_limit, scc_id, sccs, visits)
        visits += 1
        timer += 1
        disc[start] = low[start] = timer
        push!(tarjan_stack, start)
        on_stack[start] = true
        push!(call_u, start)
        push!(call_idx, 1)
        while !isempty(call_u)
            _expired(deadline_ns) && return (false, :deadline, scc_id, sccs, visits)
            u = call_u[end]
            idx = call_idx[end]
            adj_u = net.adj[u]
            if idx <= length(adj_u)
                call_idx[end] = idx + 1
                visits < max_work || return (false, :work_limit, scc_id, sccs, visits)
                visits += 1
                e = adj_u[idx]
                v = e.to
                (1 <= v <= n_lit && in_half[v]) || continue
                rc = _symmetrized_residual_cap(net, u, idx, e)
                rc > min_sym_cap || continue
                if disc[v] == 0
                    timer += 1
                    disc[v] = low[v] = timer
                    push!(tarjan_stack, v)
                    on_stack[v] = true
                    push!(call_u, v)
                    push!(call_idx, 1)
                elseif on_stack[v]
                    low[u] = min(low[u], disc[v])
                end
            else
                pop!(call_u)
                pop!(call_idx)
                if !isempty(call_u)
                    p = call_u[end]
                    low[p] = min(low[p], low[u])
                end
                if low[u] == disc[u]
                    comp = Int[]
                    cid = length(sccs) + 1
                    while true
                        w = pop!(tarjan_stack)
                        on_stack[w] = false
                        scc_id[w] = cid
                        push!(comp, w)
                        w == u && break
                    end
                    sort!(comp)
                    push!(sccs, comp)
                end
            end
        end
    end
    return (true, :ok, scc_id, sccs, visits)
end

function _is_closed_residual_scc(
    net::_FlowNetwork,
    in_half::BitVector,
    scc_id::Vector{Int},
    K::Vector{Int},
)
    length(K) >= 2 || return false
    cid = scc_id[K[1]]
    n_lit = length(in_half)
    for a in K
        scc_id[_lit_complement(a)] == cid && return false
        adj_a = net.adj[a]
        for (idx, e) in enumerate(adj_a)
            b = e.to
            (1 <= b <= n_lit && in_half[b]) || continue
            # Check outgoing residual capacity a -> b and incoming residual capacity b -> a:
            # Since R_sym(b -> a) = R_sym(_lit_complement(a) -> _lit_complement(b)), we can check both!
            rc_out = _symmetrized_residual_cap(net, a, idx, e)
            if rc_out > 0 && scc_id[b] != cid
                return false
            end
            bar_a = _lit_complement(a)
            bar_b = _lit_complement(b)
            adj_bar_a = net.adj[bar_a]
            if idx <= length(adj_bar_a) && adj_bar_a[idx].to == bar_b
                rc_in = _symmetrized_residual_cap(net, bar_a, idx, adj_bar_a[idx])
                if rc_in > 0 && scc_id[b] != cid
                    return false
                end
            end
        end
    end
    return true
end

function _widest_scc_path(
    net::_FlowNetwork,
    scc_id::Vector{Int},
    cid::Int,
    K::Vector{Int},
    src::Int,
    dst::Int,
    min_sym_cap::_Exact,
)
    src == dst && return _Exact(0)
    (scc_id[src] == cid && scc_id[dst] == cid) || return _Exact(0)
    n_lit = length(scc_id)
    best = Dict{Int,_Exact}()
    visited = Set{Int}()
    for x in K
        best[x] = _Exact(0)
    end
    # Initialize from src's outgoing edges in K
    for (idx, e) in enumerate(net.adj[src])
        y = e.to
        (1 <= y <= n_lit && scc_id[y] == cid) || continue
        rc = _symmetrized_residual_cap(net, src, idx, e)
        if rc > min_sym_cap && rc > best[y]
            best[y] = rc
        end
    end
    push!(visited, src)
    while length(visited) < length(K)
        best_u = 0
        best_val = _Exact(0)
        for x in K
            x in visited && continue
            v = best[x]
            if v > best_val
                best_val = v
                best_u = x
            end
        end
        best_u == 0 && break
        best_u == dst && return best_val
        push!(visited, best_u)
        for (idx, e) in enumerate(net.adj[best_u])
            y = e.to
            (1 <= y <= n_lit && scc_id[y] == cid && !(y in visited)) || continue
            rc = _symmetrized_residual_cap(net, best_u, idx, e)
            rc > min_sym_cap || continue
            cand = min(best_val, rc)
            if cand > best[y]
                best[y] = cand
            end
        end
    end
    return get(best, dst, _Exact(0))
end

function _scc_cycle_bottleneck(
    net::_FlowNetwork,
    scc_id::Vector{Int},
    cid::Int,
    K::Vector{Int},
    a::Int,
    b::Int,
    min_sym_cap::_Exact,
)
    b1 = _widest_scc_path(net, scc_id, cid, K, a, b, min_sym_cap)
    b1 > min_sym_cap || return _Exact(0)
    b2 = _widest_scc_path(net, scc_id, cid, K, b, a, min_sym_cap)
    b2 > min_sym_cap || return _Exact(0)
    return min(b1, b2)
end

function _build_implication_network(
    ws::Workspace;
    max_work::Int=typemax(Int),
    max_exact_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    s = ws._snapshot
    st = ws._state
    n = length(s.labels)
    direction = _direction(s)
    direction != 0 || return (false, :zero_scale, nothing, _Exact(0), 0, 0)
    S_node = 2 * n + 1
    T_node = 2 * n + 2
    net = _FlowNetwork(2 * n + 2, S_node, T_node)
    graph_work = 0
    exact_work = 0
    exact_work < max_exact_work || return (false, :verification_limit, nothing, _Exact(0), graph_work, exact_work)
    exact_work += 1
    C_base = direction * _spin_constant(ws)
    for u in 1:n
        st.fixed[u] == 2 || continue
        _expired(deadline_ns) && return (false, :deadline, nothing, _Exact(0), graph_work, exact_work)
        graph_work < max_work || return (false, :work_limit, nothing, _Exact(0), graph_work, exact_work)
        graph_work += 1
        exact_work < max_exact_work || return (false, :verification_limit, nothing, _Exact(0), graph_work, exact_work)
        exact_work += 1
        h_u = direction * _spin_field(ws, u)
        if !iszero(h_u)
            ah = abs(h_u)
            C_base -= ah
            if h_u > 0
                _add_directed_pair!(net, S_node, 2 * u, ah, _Exact(0))
                _add_directed_pair!(net, 2 * u - 1, T_node, ah, _Exact(0))
            else
                _add_directed_pair!(net, S_node, 2 * u - 1, ah, _Exact(0))
                _add_directed_pair!(net, 2 * u, T_node, ah, _Exact(0))
            end
        end
        for (v, q) in st.adjacency[u]
            _expired(deadline_ns) && return (false, :deadline, nothing, _Exact(0), graph_work, exact_work)
            graph_work < max_work || return (false, :work_limit, nothing, _Exact(0), graph_work, exact_work)
            graph_work += 1
            (st.fixed[v] == 2 && u < v) || continue
            exact_work < max_exact_work || return (false, :verification_limit, nothing, _Exact(0), graph_work, exact_work)
            exact_work += 1
            J_uv = direction * _spin_coupling(ws, q)
            iszero(J_uv) && continue
            aJ = abs(J_uv)
            C_base -= aJ
            if J_uv < 0
                _add_directed_pair!(net, 2 * u - 1, 2 * v - 1, aJ, aJ)
                _add_directed_pair!(net, 2 * u, 2 * v, aJ, aJ)
            else
                _add_directed_pair!(net, 2 * u - 1, 2 * v, aJ, aJ)
                _add_directed_pair!(net, 2 * u, 2 * v - 1, aJ, aJ)
            end
        end
    end
    return (true, :ok, net, C_base, graph_work, exact_work)
end

function _build_poly_implication_network(p, deadline=nothing)
    n = p.n
    direction = _direction_poly(p)
    is_bool = p.domain === QT.BoolDomain
    S_node = 2 * n + 1
    T_node = 2 * n + 2
    net = _FlowNetwork(2 * n + 2, S_node, T_node)
    C_base = direction * p.c_spin
    visits = 0
    for u in 1:n
        _expired(deadline) && return nothing
        p.active[u] || continue
        visits += 1
        h_u = direction * p.h_spin[u]
        if !iszero(h_u)
            ah = abs(h_u)
            C_base -= ah
            if h_u > 0
                _add_directed_pair!(net, S_node, 2 * u, ah, _Exact(0))
                _add_directed_pair!(net, 2 * u - 1, T_node, ah, _Exact(0))
            else
                _add_directed_pair!(net, S_node, 2 * u - 1, ah, _Exact(0))
                _add_directed_pair!(net, 2 * u, T_node, ah, _Exact(0))
            end
        end
        for (v, q) in p.adj[u]
            _expired(deadline) && return nothing
            visits += 1
            (p.active[v] && u < v) || continue
            J_uv_raw = is_bool ? (q // 4) : q
            J_uv = direction * J_uv_raw
            iszero(J_uv) && continue
            aJ = abs(J_uv)
            C_base -= aJ
            if J_uv < 0
                _add_directed_pair!(net, 2 * u - 1, 2 * v - 1, aJ, aJ)
                _add_directed_pair!(net, 2 * u, 2 * v, aJ, aJ)
            else
                _add_directed_pair!(net, 2 * u - 1, 2 * v, aJ, aJ)
                _add_directed_pair!(net, 2 * u, 2 * v - 1, aJ, aJ)
            end
        end
    end
    return (net, C_base, visits)
end

"""
    SubmodularComponent{V}

Result of structural gauge-submodularity recognition on a candidate residual
component, recording original-order `variables::Vector{V}`, internal
`indices::Vector{Int}`, whether the subset has no free external neighbors
(`is_closed::Bool`), whether a consistent spin gauge makes all active couplings
nonpositive (`is_submodular::Bool`), `stop_reason::Symbol` (`:submodular`,
`:frustrated_cycle`, `:boundary_coupled`, `:already_fixed`, `:zero_scale`,
`:work_limit`, or `:deadline`), the discovered `gauge::Vector{Int}` (`{-1, +1}`),
and `recognition_work::Int`.
"""
struct SubmodularComponent{V}
    variables::Vector{V}
    indices::Vector{Int}
    is_closed::Bool
    is_submodular::Bool
    stop_reason::Symbol
    gauge::Vector{Int}
    recognition_work::Int
end

function _recognize_component_indices(
    ws::Workspace,
    comp_indices::Vector{Int};
    max_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    n = length(s.labels)
    vars = V[deepcopy(s.labels[u]) for u in comp_indices]
    for u in comp_indices
        st.fixed[u] == 2 ||
            return SubmodularComponent{V}(vars, comp_indices, false, false, :already_fixed, Int[], 0)
    end
    direction = _direction(s)
    direction != 0 ||
        return SubmodularComponent{V}(vars, comp_indices, false, false, :zero_scale, Int[], 0)
    in_comp = falses(n)
    for u in comp_indices
        in_comp[u] = true
    end
    work = 0
    for u in comp_indices
        _expired(deadline_ns) &&
            return SubmodularComponent{V}(vars, comp_indices, false, false, :deadline, Int[], work)
        work < max_work ||
            return SubmodularComponent{V}(vars, comp_indices, false, false, :work_limit, Int[], work)
        work += 1
        for (v, q) in st.adjacency[u]
            _expired(deadline_ns) &&
                return SubmodularComponent{V}(vars, comp_indices, false, false, :deadline, Int[], work)
            work < max_work ||
                return SubmodularComponent{V}(vars, comp_indices, false, false, :work_limit, Int[], work)
            work += 1
            st.fixed[v] == 2 || continue
            iszero(_spin_coupling(ws, q)) && continue
            if !in_comp[v]
                return SubmodularComponent{V}(vars, comp_indices, false, false, :boundary_coupled, Int[], work)
            end
        end
    end
    sigma = zeros(Int, n)
    queue = Int[]
    for r in comp_indices
        sigma[r] != 0 && continue
        sigma[r] = 1
        empty!(queue)
        push!(queue, r)
        head = 1
        while head <= length(queue)
            _expired(deadline_ns) &&
                return SubmodularComponent{V}(vars, comp_indices, true, false, :deadline, Int[], work)
            u = queue[head]
            head += 1
            for (v, q) in st.adjacency[u]
                _expired(deadline_ns) &&
                    return SubmodularComponent{V}(vars, comp_indices, true, false, :deadline, Int[], work)
                work < max_work ||
                    return SubmodularComponent{V}(vars, comp_indices, true, false, :work_limit, Int[], work)
                work += 1
                st.fixed[v] == 2 || continue
                dJ = direction * _spin_coupling(ws, q)
                iszero(dJ) && continue
                req = dJ < 0 ? sigma[u] : -sigma[u]
                if sigma[v] == 0
                    sigma[v] = req
                    push!(queue, v)
                elseif sigma[v] != req
                    return SubmodularComponent{V}(vars, comp_indices, true, false, :frustrated_cycle, Int[], work)
                end
            end
        end
    end
    gauge = Int[sigma[u] for u in comp_indices]
    return SubmodularComponent{V}(vars, comp_indices, true, true, :submodular, gauge, work)
end

"""
    recognize_submodular_component(ws, component; max_work=typemax(Int), deadline_ns=nothing)

Check whether `component` (an iterable of original variable labels) is a closed
active residual component (no free external neighbors with nonzero coupling) and
whether a spin gauge ``\\sigma_u \\in \\{-1, +1\\}`` makes every active coupling in
`component` nonpositive (``\\sigma_u \\sigma_v \\tilde{J}_{uv} \\le 0``). Returns a
[`SubmodularComponent`](@ref) without constructing a flow network.
"""
function recognize_submodular_component(
    ws::Workspace,
    component;
    max_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    seen = Set{Int}()
    comp_indices = Int[]
    for label in component
        u = _variable(ws, label)
        if !(u in seen)
            push!(comp_indices, u)
            push!(seen, u)
        end
    end
    isempty(comp_indices) && throw(ArgumentError("component must contain at least one variable"))
    sort!(comp_indices)
    return _recognize_component_indices(ws, comp_indices; max_work=max_work, deadline_ns=deadline_ns)
end

"""
    recognize_submodular_components(ws; max_work=typemax(Int), deadline_ns=nothing)

Partition all currently free variables in `ws` into connected residual components
and test each component for gauge-submodularity via bipartite edge-parity BFS.
Returns `(components::Vector{SubmodularComponent{V}}, stop_reason::Symbol, recognition_work::Int)`.
"""
function recognize_submodular_components(
    ws::Workspace;
    max_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    n = length(s.labels)
    direction = _direction(s)
    direction != 0 || return (SubmodularComponent{V}[], :zero_scale, 0)
    visited = falses(n)
    raw_comps = Vector{Vector{Int}}()
    work = 0
    queue = Int[]
    for r in 1:n
        (st.fixed[r] == 2 && !visited[r]) || continue
        _expired(deadline_ns) && return (SubmodularComponent{V}[], :deadline, work)
        work < max_work || return (SubmodularComponent{V}[], :work_limit, work)
        work += 1
        visited[r] = true
        empty!(queue)
        push!(queue, r)
        head = 1
        while head <= length(queue)
            _expired(deadline_ns) && return (SubmodularComponent{V}[], :deadline, work)
            u = queue[head]
            head += 1
            for (v, q) in st.adjacency[u]
                _expired(deadline_ns) && return (SubmodularComponent{V}[], :deadline, work)
                work < max_work || return (SubmodularComponent{V}[], :work_limit, work)
                work += 1
                (st.fixed[v] == 2 && !visited[v] && !iszero(_spin_coupling(ws, q))) || continue
                visited[v] = true
                push!(queue, v)
            end
        end
        comp = sort!(copy(queue))
        push!(raw_comps, comp)
    end
    results = SubmodularComponent{V}[]
    for comp in raw_comps
        rec = _recognize_component_indices(
            ws, comp; max_work=max_work - work, deadline_ns=deadline_ns,
        )
        work += rec.recognition_work
        push!(results, rec)
        if rec.stop_reason in (:deadline, :work_limit)
            return (results, rec.stop_reason, work)
        end
    end
    return (results, :completed, work)
end

function _build_submodular_cut_network(
    ws::Workspace,
    comp_indices::Vector{Int},
    gauge::Vector{Int};
    max_work::Int=typemax(Int),
    max_exact_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    s = ws._snapshot
    st = ws._state
    direction = _direction(s)
    k = length(comp_indices)
    S_node = k + 1
    T_node = k + 2
    net = _FlowNetwork(k + 2, S_node, T_node)
    local_idx = Dict{Int,Int}(comp_indices[a] => a for a in 1:k)
    C_comp = _Exact(0)
    graph_work = 0
    exact_work = 0
    for a in 1:k
        _expired(deadline_ns) && return (false, :deadline, nothing, _Exact(0), graph_work, exact_work)
        graph_work < max_work || return (false, :work_limit, nothing, _Exact(0), graph_work, exact_work)
        graph_work += 1
        exact_work < max_exact_work || return (false, :verification_limit, nothing, _Exact(0), graph_work, exact_work)
        exact_work += 1
        u = comp_indices[a]
        g_a = gauge[a]
        h_prime = g_a * direction * _spin_field(ws, u)
        if !iszero(h_prime)
            ah = abs(h_prime)
            C_comp -= ah
            if h_prime > 0
                _add_directed_pair!(net, a, T_node, 2 * ah, _Exact(0))
            else
                _add_directed_pair!(net, S_node, a, 2 * ah, _Exact(0))
            end
        end
        for (v, q) in st.adjacency[u]
            _expired(deadline_ns) && return (false, :deadline, nothing, _Exact(0), graph_work, exact_work)
            graph_work < max_work || return (false, :work_limit, nothing, _Exact(0), graph_work, exact_work)
            graph_work += 1
            st.fixed[v] == 2 || continue
            J_raw = _spin_coupling(ws, q)
            iszero(J_raw) && continue
            b = get(local_idx, v, 0)
            b > 0 || return (false, :boundary_coupled, nothing, _Exact(0), graph_work, exact_work)
            u < v || continue
            exact_work < max_exact_work || return (false, :verification_limit, nothing, _Exact(0), graph_work, exact_work)
            exact_work += 1
            J_prime = g_a * gauge[b] * direction * J_raw
            J_prime < 0 || return (false, :frustrated_cycle, nothing, _Exact(0), graph_work, exact_work)
            aJ = abs(J_prime)
            C_comp -= aJ
            _add_directed_pair!(net, a, b, 2 * aJ, 2 * aJ)
        end
    end
    return (true, :ok, net, C_comp, graph_work, exact_work)
end

function _build_poly_submodular_cut_network(
    p,
    comp_indices::Tuple{Vararg{Int}},
    gauge::Tuple{Vararg{Int}},
    deadline=nothing,
)
    k = length(comp_indices)
    length(gauge) == k && k > 0 || return (false, :invalid_step, nothing, _Exact(0), 0)
    direction = _direction_poly(p)
    is_bool = p.domain === QT.BoolDomain
    S_node = k + 1
    T_node = k + 2
    net = _FlowNetwork(k + 2, S_node, T_node)
    local_idx = Dict{Int,Int}()
    for a in 1:k
        u = comp_indices[a]
        (1 <= u <= p.n && p.active[u] && gauge[a] in (-1, 1)) ||
            return (false, :invalid_step, nothing, _Exact(0), 0)
        (a > 1 && comp_indices[a - 1] >= u) &&
            return (false, :invalid_step, nothing, _Exact(0), 0)
        local_idx[u] = a
    end
    C_comp = _Exact(0)
    visits = 0
    for a in 1:k
        _expired(deadline) && return (false, :deadline, nothing, _Exact(0), visits)
        visits += 1
        u = comp_indices[a]
        g_a = gauge[a]
        h_prime = g_a * direction * p.h_spin[u]
        if !iszero(h_prime)
            ah = abs(h_prime)
            C_comp -= ah
            if h_prime > 0
                _add_directed_pair!(net, a, T_node, 2 * ah, _Exact(0))
            else
                _add_directed_pair!(net, S_node, a, 2 * ah, _Exact(0))
            end
        end
        for (v, q) in p.adj[u]
            _expired(deadline) && return (false, :deadline, nothing, _Exact(0), visits)
            visits += 1
            (p.active[v] && !iszero(q)) || continue
            b = get(local_idx, v, 0)
            b > 0 || return (false, :boundary_coupled, nothing, _Exact(0), visits)
            u < v || continue
            J_uv_raw = is_bool ? (q // 4) : q
            J_prime = g_a * gauge[b] * direction * J_uv_raw
            J_prime <= 0 || return (false, :frustrated_cycle, nothing, _Exact(0), visits)
            aJ = abs(J_prime)
            C_comp -= aJ
            _add_directed_pair!(net, a, b, 2 * aJ, 2 * aJ)
        end
    end
    return (true, :ok, net, C_comp, visits)
end
