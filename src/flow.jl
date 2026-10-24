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
