# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    MaxCutGraph{V}

Exact signed weighted Max-Cut representation of the active direction-normalized
Ising residual of a [`Workspace`](@ref):

```math
\\tilde{F}(t) = \\tilde{c}_{\\text{spin}} + \\sum_{u \\in F} \\tilde{h}_u t_u + \\sum_{u < v \\in F} \\tilde{J}_{uv} t_u t_v
  = C_{\\text{cut}} - \\sum_{(a, b) \\in E_{\\text{cut}}} w_{ab} \\, \\delta(z_a \\ne z_b),
```

where `reference_vertex == 0` carries spin ``z_0 \\in \\{-1, +1\\}``, each active
variable ``u \\in F`` carries cut spin ``z_u \\in \\{-1, +1\\}`` related to gauged
spin ``t_u = z_0 z_u`` (and original canonical spin ``s_u = g_u z_0 z_u``),
reference edges have weight ``w_{0,u} = 2\\tilde{h}_u``, internal edges have
weight ``w_{uv} = 2\\tilde{J}_{uv}``, and
``C_{\\text{cut}} = \\tilde{c}_{\\text{spin}} + \\sum_{u \\in F} \\tilde{h}_u + \\sum_{u < v \\in F} \\tilde{J}_{uv}``.

Global cut reversal ``z \\mapsto -z`` preserves both ``\\operatorname{CutWeight}(z)``
and every physical spin ``s_u = g_u z_0 z_u``.
"""
struct MaxCutGraph{V}
    generation::Generation
    reference_vertex::Int
    variables::Vector{V}
    indices::Vector{Int}
    gauge::Vector{Int}
    cut_constant::_Exact
    scale::_Exact
    reference_weights::Vector{Pair{V,_Exact}}
    edge_weights::Vector{Tuple{V,V,_Exact}}
    reference_degree::Int
    internal_edges::Int
    total_edges::Int
    stop_reason::Symbol
    graph_work::Int
    exact_work::Int
end
generation(mc::MaxCutGraph) = mc.generation

function _reference_degree(ws::Workspace)
    st = ws._state
    n = length(ws._snapshot.labels)
    deg = 0
    for u in 1:n
        st.fixed[u] == 2 || continue
        !iszero(_spin_field(ws, u)) && (deg += 1)
    end
    return deg
end

"""
    maxcut_graph(ws; map=nothing, max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Construct an owned [`MaxCutGraph`](@ref) representing the active residual of `ws`
as a signed weighted Max-Cut instance on ``\\{0\\} \\cup F`` with explicit reference
vertex `0`.
"""
function maxcut_graph(
    ws::Workspace;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map; full=true)
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    n = length(s.labels)
    direction = _direction(s)
    if direction == 0
        return MaxCutGraph{V}(
            generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
            Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :zero_scale, 0, 0,
        )
    end
    1 <= max_exact_work || return MaxCutGraph{V}(
        generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
        Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :verification_limit, 0, 0,
    )
    vars = V[]
    indices = Int[]
    gauge = Int[]
    ref_weights = Pair{V,_Exact}[]
    edge_weights = Tuple{V,V,_Exact}[]
    c_cut = direction * _spin_constant(ws)
    graph_work = 0
    exact_work = 1
    for u in 1:n
        _expired(deadline_ns) && return MaxCutGraph{V}(
            generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
            Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :deadline, graph_work, exact_work,
        )
        st.fixed[u] == 2 || continue
        graph_work < max_work || return MaxCutGraph{V}(
            generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
            Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :work_limit, graph_work, exact_work,
        )
        graph_work += 1
        exact_work < max_exact_work || return MaxCutGraph{V}(
            generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
            Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :verification_limit, graph_work, exact_work,
        )
        exact_work += 1
        lbl_u = deepcopy(s.labels[u])
        g_u = map === nothing ? 1 : map.gauge[u]
        push!(vars, lbl_u)
        push!(indices, u)
        push!(gauge, g_u)
        h_u = direction * g_u * _spin_field(ws, u)
        if !iszero(h_u)
            c_cut += h_u
            push!(ref_weights, lbl_u => 2 * h_u)
        end
        for (v, q) in st.adjacency[u]
            _expired(deadline_ns) && return MaxCutGraph{V}(
                generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
                Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :deadline, graph_work, exact_work,
            )
            graph_work < max_work || return MaxCutGraph{V}(
                generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
                Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :work_limit, graph_work, exact_work,
            )
            graph_work += 1
            (st.fixed[v] == 2 && u < v) || continue
            J_raw = _spin_coupling(ws, q)
            iszero(J_raw) && continue
            exact_work < max_exact_work || return MaxCutGraph{V}(
                generation(ws), 0, V[], Int[], Int[], _Exact(0), _Exact(0),
                Pair{V,_Exact}[], Tuple{V,V,_Exact}[], 0, 0, 0, :verification_limit, graph_work, exact_work,
            )
            exact_work += 1
            g_v = map === nothing ? 1 : map.gauge[v]
            J_uv = direction * (g_u * g_v) * J_raw
            c_cut += J_uv
            push!(edge_weights, (lbl_u, deepcopy(s.labels[v]), 2 * J_uv))
        end
    end
    ref_deg = length(ref_weights)
    int_edges = length(edge_weights)
    scale_val = _Exact(s.scale) * direction
    return MaxCutGraph{V}(
        generation(ws), 0, vars, indices, gauge, deepcopy(c_cut), deepcopy(scale_val),
        ref_weights, edge_weights, ref_deg, int_edges, ref_deg + int_edges,
        :completed, graph_work, exact_work,
    )
end

function _extract_cut_sides(mc::MaxCutGraph{V}, cut_side) where V
    k = length(mc.variables)
    z = Vector{Int}(undef, k)
    z0 = 1
    if cut_side isa AbstractVector
        Base.require_one_based_indexing(cut_side)
        if length(cut_side) == k + 1
            v0 = cut_side[1]
            v0 isa Integer && !(v0 isa Bool) && v0 in (-1, 1) ||
                throw(ArgumentError("reference cut side must be -1 or +1"))
            z0 = Int(v0)
            for a in 1:k
                va = cut_side[a + 1]
                va isa Integer && !(va isa Bool) && va in (-1, 1) ||
                    throw(ArgumentError("cut side at position $(a + 1) must be -1 or +1"))
                z[a] = Int(va)
            end
        elseif length(cut_side) == k
            for a in 1:k
                va = cut_side[a]
                va isa Integer && !(va isa Bool) && va in (-1, 1) ||
                    throw(ArgumentError("cut side at position $a must be -1 or +1"))
                z[a] = Int(va)
            end
        else
            throw(ArgumentError("cut_side vector must have length $(k) (active variables) or $(k + 1) (reference + active variables)"))
        end
    elseif cut_side isa AbstractDict
        if haskey(cut_side, 0) && !(0 in mc.variables)
            v0 = cut_side[0]
            v0 isa Integer && !(v0 isa Bool) && v0 in (-1, 1) ||
                throw(ArgumentError("reference cut side for key 0 must be -1 or +1"))
            z0 = Int(v0)
        elseif haskey(cut_side, :reference)
            v0 = cut_side[:reference]
            v0 isa Integer && !(v0 isa Bool) && v0 in (-1, 1) ||
                throw(ArgumentError("reference cut side for :reference must be -1 or +1"))
            z0 = Int(v0)
        end
        for (a, lbl) in enumerate(mc.variables)
            haskey(cut_side, lbl) ||
                throw(ArgumentError("cut_side dictionary is missing variable $(repr(lbl))"))
            va = cut_side[lbl]
            va isa Integer && !(va isa Bool) && va in (-1, 1) ||
                throw(ArgumentError("cut side for $(repr(lbl)) must be -1 or +1"))
            z[a] = Int(va)
        end
    else
        throw(ArgumentError("cut_side must be a vector or dictionary of {-1, +1} cut sides"))
    end
    return z0, z
end

"""
    maxcut_cut_weight(mc::MaxCutGraph, cut_side)

Evaluate the exact rational cut weight
``\\operatorname{CutWeight}(z) = \\sum_{(a, b) \\in E_{\\text{cut}}} w_{ab} \\, \\delta(z_a \\ne z_b)``
for a cut assignment `cut_side` (`{-1, +1}` vector of length `length(mc.variables)`
with implicit `z_0 = +1`, vector of length `length(mc.variables) + 1` starting with
`z_0`, or dictionary mapping active labels and optionally `0` / `:reference` to `{-1, +1}`).
"""
function maxcut_cut_weight(mc::MaxCutGraph{V}, cut_side) where V
    mc.stop_reason === :completed ||
        throw(ArgumentError("MaxCutGraph is incomplete (stop_reason = $(repr(mc.stop_reason)))"))
    z0, z = _extract_cut_sides(mc, cut_side)
    lbl_to_pos = Dict{V,Int}(mc.variables[a] => a for a in eachindex(mc.variables))
    total = _Exact(0)
    for (lbl_u, w_0u) in mc.reference_weights
        z_u = z[lbl_to_pos[lbl_u]]
        z0 != z_u && (total += w_0u)
    end
    for (lbl_u, lbl_v, w_uv) in mc.edge_weights
        z_u = z[lbl_to_pos[lbl_u]]
        z_v = z[lbl_to_pos[lbl_v]]
        z_u != z_v && (total += w_uv)
    end
    return total
end

"""
    maxcut_energy(mc::MaxCutGraph, cut_side; scaled=false)

Evaluate the exact normalized active spin energy
``\\tilde{F}(z) = C_{\\text{cut}} - \\operatorname{CutWeight}(z)`` (or scaled by
`mc.scale` when `scaled=true`).
"""
function maxcut_energy(mc::MaxCutGraph, cut_side; scaled::Bool=false)
    val = mc.cut_constant - maxcut_cut_weight(mc, cut_side)
    return scaled ? mc.scale * val : val
end

"""
    maxcut_to_spin(mc::MaxCutGraph, cut_side; mapped=false)

Project a cut assignment `cut_side` on ``\\{0\\} \\cup F`` to an ordered spin vector
``s_u = g_u z_0 z_u \\in \\{-1, +1\\}`` in original canonical spin coordinates
(or gauged spin coordinates ``t_u = z_0 z_u`` when `mapped=true`). Invariant
under global cut reversal ``z \\mapsto -z``.
"""
function maxcut_to_spin(mc::MaxCutGraph, cut_side; mapped::Bool=false)
    mc.stop_reason === :completed ||
        throw(ArgumentError("MaxCutGraph is incomplete (stop_reason = $(repr(mc.stop_reason)))"))
    z0, z = _extract_cut_sides(mc, cut_side)
    k = length(mc.variables)
    out = Vector{Int}(undef, k)
    for a in 1:k
        t_a = z0 * z[a]
        out[a] = mapped ? t_a : (mc.gauge[a] * t_a)
    end
    return out
end

"""
    spin_to_maxcut(mc::MaxCutGraph, spin_state; reference_side=1, mapped=false)

Embed an active spin state `spin_state` (`{-1, +1}` vector or label dictionary)
into a cut-side vector `[z_0, z_1, ..., z_k]` on ``\\{0\\} \\cup F`` with
`z_0 == reference_side` (`-1` or `+1`).
"""
function spin_to_maxcut(mc::MaxCutGraph{V}, spin_state; reference_side::Int=1, mapped::Bool=false) where V
    mc.stop_reason === :completed ||
        throw(ArgumentError("MaxCutGraph is incomplete (stop_reason = $(repr(mc.stop_reason)))"))
    !(reference_side isa Bool) && reference_side in (-1, 1) ||
        throw(ArgumentError("reference_side must be -1 or +1"))
    k = length(mc.variables)
    out = Vector{Int}(undef, k + 1)
    out[1] = reference_side
    if spin_state isa AbstractVector
        Base.require_one_based_indexing(spin_state)
        length(spin_state) == k ||
            throw(ArgumentError("spin_state vector must have length $(k)"))
        for a in 1:k
            sv = spin_state[a]
            sv isa Integer && !(sv isa Bool) && sv in (-1, 1) ||
                throw(ArgumentError("spin value at position $a must be -1 or +1"))
            t_a = mapped ? Int(sv) : (mc.gauge[a] * Int(sv))
            out[a + 1] = reference_side * t_a
        end
    elseif spin_state isa AbstractDict
        for (a, lbl) in enumerate(mc.variables)
            haskey(spin_state, lbl) ||
                throw(ArgumentError("spin_state dictionary is missing variable $(repr(lbl))"))
            sv = spin_state[lbl]
            sv isa Integer && !(sv isa Bool) && sv in (-1, 1) ||
                throw(ArgumentError("spin value for $(repr(lbl)) must be -1 or +1"))
            t_a = mapped ? Int(sv) : (mc.gauge[a] * Int(sv))
            out[a + 1] = reference_side * t_a
        end
    else
        throw(ArgumentError("spin_state must be a vector or dictionary of {-1, +1} spin values"))
    end
    return out
end

function _ws_mc_J(ws::Workspace, x::Int, y::Int, direction::Int)
    x == y && return _Exact(0)
    st = ws._state
    if x == 0 || y == 0
        u = x == 0 ? y : x
        st.fixed[u] == 2 || return _Exact(0)
        return direction * _spin_field(ws, u)
    end
    (st.fixed[x] == 2 && st.fixed[y] == 2) || return _Exact(0)
    pos = get(st.adj_pos[x], y, 0)
    pos == 0 && return _Exact(0)
    return direction * _spin_coupling(ws, st.adjacency[x][pos].second)
end

function _ws_mc_total_abs_weight(
    ws::Workspace,
    x::Int,
    direction::Int;
    max_work::Int=typemax(Int),
    max_exact_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    st = ws._state
    n = length(ws._snapshot.labels)
    visits = 0
    exact_work = 0
    total = _Exact(0)
    if x == 0
        for d in 1:n
            _expired(deadline_ns) && return (false, :deadline, _Exact(0), visits, exact_work)
            visits < max_work || return (false, :work_limit, _Exact(0), visits, exact_work)
            visits += 1
            st.fixed[d] == 2 || continue
            exact_work < max_exact_work || return (false, :verification_limit, _Exact(0), visits, exact_work)
            exact_work += 1
            total += abs(direction * _spin_field(ws, d))
        end
        return (true, :ok, total, visits, exact_work)
    else
        st.fixed[x] == 2 || return (false, :already_fixed, _Exact(0), 0, 0)
        exact_work < max_exact_work || return (false, :verification_limit, _Exact(0), 0, 0)
        exact_work += 1
        total += abs(direction * _spin_field(ws, x))
        for (d, q) in st.adjacency[x]
            _expired(deadline_ns) && return (false, :deadline, _Exact(0), visits, exact_work)
            visits < max_work || return (false, :work_limit, _Exact(0), visits, exact_work)
            visits += 1
            st.fixed[d] == 2 || continue
            exact_work < max_exact_work || return (false, :verification_limit, _Exact(0), visits, exact_work)
            exact_work += 1
            total += abs(direction * _spin_coupling(ws, q))
        end
        return (true, :ok, total, visits, exact_work)
    end
end

function _poly_mc_J(p, x::Int, y::Int, direction::Int)
    x == y && return _Exact(0)
    is_bool = p.domain === QT.BoolDomain
    if x == 0 || y == 0
        u = x == 0 ? y : x
        (1 <= u <= p.n && p.active[u]) || return _Exact(0)
        return direction * p.h_spin[u]
    end
    (1 <= x <= p.n && 1 <= y <= p.n && p.active[x] && p.active[y]) || return _Exact(0)
    pos = get(p.adj_pos[x], y, 0)
    pos == 0 && return _Exact(0)
    q = p.adj[x][pos].second
    return direction * (is_bool ? (q // 4) : q)
end

function _poly_mc_total_abs_weight(p, x::Int, direction::Int, deadline=nothing)
    is_bool = p.domain === QT.BoolDomain
    total = _Exact(0)
    if x == 0
        for d in 1:p.n
            _expired(deadline) && return nothing
            p.active[d] || continue
            total += abs(direction * p.h_spin[d])
        end
        return total
    else
        (1 <= x <= p.n && p.active[x]) || return nothing
        total += abs(direction * p.h_spin[x])
        for (d, q) in p.adj[x]
            _expired(deadline) && return nothing
            p.active[d] || continue
            J_xd = is_bool ? (q // 4) : q
            total += abs(direction * J_xd)
        end
        return total
    end
end

function _eval_maxcut_anchor(
    ws::Workspace,
    a::Int,
    b::Int,
    cand_signs::Tuple{Vararg{Int}},
    direction::Int,
    allow_weak::Bool,
    max_triangles::Int,
    max_work::Int,
    max_exact_work::Int,
    deadline_ns,
)
    st = ws._state
    _expired(deadline_ns) &&
        return (false, :deadline, :none, 0, _Exact(0), _Exact(0), _Exact(0), (), 0, 0, 0)
    1 <= max_exact_work ||
        return (false, :verification_limit, :none, 0, _Exact(0), _Exact(0), _Exact(0), (), 0, 0, 0)
    J_a0 = direction * _spin_field(ws, a)
    W_a = abs(J_a0)
    J_ab = b == 0 ? J_a0 : _Exact(0)
    a_nbrs = Pair{Int,_Exact}[]
    if b != 0 && !iszero(J_a0)
        J_b0 = direction * _spin_field(ws, b)
        !iszero(J_b0) && push!(a_nbrs, 0 => J_a0)
    end
    graph_work = 0
    tri_work = 0
    exact_work = 1
    for (w, q) in st.adjacency[a]
        _expired(deadline_ns) &&
            return (false, :deadline, :maxcut_edge, 0, _Exact(0), _Exact(0), _Exact(0), (), graph_work, tri_work, exact_work)
        graph_work < max_work ||
            return (false, :work_limit, :maxcut_edge, 0, _Exact(0), _Exact(0), _Exact(0), (), graph_work, tri_work, exact_work)
        graph_work += 1
        st.fixed[w] == 2 || continue
        J_aw = direction * _spin_coupling(ws, q)
        iszero(J_aw) && continue
        exact_work < max_exact_work ||
            return (false, :verification_limit, :maxcut_edge, 0, _Exact(0), _Exact(0), _Exact(0), (), graph_work, tri_work, exact_work)
        exact_work += 1
        W_a += abs(J_aw)
        if w == b
            J_ab = J_aw
        else
            push!(a_nbrs, w => J_aw)
        end
    end
    non_tri_0 = W_a - abs(J_ab)
    best_edge_sigma = cand_signs[1]
    best_edge_margin = -best_edge_sigma * J_ab - non_tri_0
    for idx in 2:length(cand_signs)
        s_cand = cand_signs[idx]
        m_cand = -s_cand * J_ab - non_tri_0
        if m_cand > best_edge_margin
            best_edge_sigma = s_cand
            best_edge_margin = m_cand
        end
    end
    if best_edge_margin > 0 || (max_triangles == 0 && allow_weak && best_edge_margin >= 0)
        direct_0 = -best_edge_sigma * J_ab
        return (
            true, :proved, :maxcut_edge, best_edge_sigma,
            best_edge_margin, direct_0, non_tri_0, (),
            graph_work, tri_work, exact_work,
        )
    end
    if max_triangles == 0 || isempty(a_nbrs)
        direct_0 = -best_edge_sigma * J_ab
        return (
            false, :not_strict, :maxcut_edge, best_edge_sigma,
            best_edge_margin, direct_0, non_tri_0, (),
            graph_work, tri_work, exact_work,
        )
    end
    common_info = Tuple{Int,_Exact,_Exact,_Exact}[]
    for (c, J_ac) in a_nbrs
        _expired(deadline_ns) &&
            return (false, :deadline, :maxcut_triangle, 0, _Exact(0), _Exact(0), _Exact(0), (), graph_work, tri_work, exact_work)
        graph_work + tri_work < max_work ||
            return (false, :work_limit, :maxcut_triangle, 0, _Exact(0), _Exact(0), _Exact(0), (), graph_work, tri_work, exact_work)
        tri_work += 1
        J_bc = _ws_mc_J(ws, b, c, direction)
        iszero(J_bc) && continue
        can_help = false
        for s_cand in cand_signs
            sgn_ac = s_cand * J_ac > 0 ? 1 : -1
            if abs(J_ac) + sgn_ac * J_bc > 0
                can_help = true
                break
            end
        end
        can_help || continue
        ok_c, reason_c, W_c, dw_c, dx_c = _ws_mc_total_abs_weight(
            ws, c, direction;
            max_work=max_work - graph_work - tri_work,
            max_exact_work=max_exact_work - exact_work,
            deadline_ns=deadline_ns,
        )
        tri_work += dw_c
        exact_work += dx_c
        ok_c || return (
            false, reason_c, :maxcut_triangle, 0,
            _Exact(0), _Exact(0), _Exact(0), (),
            graph_work, tri_work, exact_work,
        )
        R_c = W_c - abs(J_ac) - abs(J_bc)
        push!(common_info, (c, J_ac, J_bc, R_c))
    end
    best_sigma = best_edge_sigma
    best_margin = best_edge_margin
    best_direct = -best_edge_sigma * J_ab
    best_non_tri = non_tri_0
    best_tris = Tuple{Int,_Exact,_Exact,_Exact,_Exact}[]
    for (s_idx, s_cand) in enumerate(cand_signs)
        scored = Tuple{_Exact,Int,_Exact,_Exact,_Exact,_Exact}[]
        for (c, J_ac, J_bc, R_c) in common_info
            sgn_ac = s_cand * J_ac > 0 ? 1 : -1
            gamma_c = max(-abs(J_ac), min(abs(J_ac), sgn_ac * J_bc - R_c))
            gain_c = gamma_c + abs(J_ac)
            if gain_c > 0
                push!(scored, (gain_c, c, J_ac, J_bc, R_c, gamma_c))
            end
        end
        sort!(scored; by=t -> (-t[1], t[2]))
        take_k = min(max_triangles, length(scored))
        chosen = Tuple{Int,_Exact,_Exact,_Exact,_Exact}[
            (scored[i][2], scored[i][3], scored[i][4], scored[i][5], scored[i][6])
            for i in 1:take_k
        ]
        sort!(chosen; by=first)
        sum_abs_ac = sum((abs(t[2]) for t in chosen); init=_Exact(0))
        sum_gamma = sum((t[5] for t in chosen); init=_Exact(0))
        direct_s = -s_cand * J_ab
        non_tri_s = W_a - abs(J_ab) - sum_abs_ac
        margin_s = direct_s + sum_gamma - non_tri_s
        if s_idx == 1 || margin_s > best_margin
            best_sigma = s_cand
            best_margin = margin_s
            best_direct = direct_s
            best_non_tri = non_tri_s
            best_tris = chosen
        end
    end
    meth = isempty(best_tris) ? :maxcut_edge : :maxcut_triangle
    proved = best_margin > 0 || (allow_weak && best_margin >= 0)
    return (
        proved, proved ? :proved : :not_strict, meth, best_sigma,
        best_margin, best_direct, best_non_tri, Tuple(best_tris),
        graph_work, tri_work, exact_work,
    )
end

function _maxcut_witness(
    ws::Workspace,
    u::Int,
    v::Int=0;
    sign::Union{Nothing,Int}=nothing,
    value=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    max_triangles=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
    predecessors::Int=0,
    scope_length::Int=-1,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    max_triangles isa Integer && !(max_triangles isa Bool) && 0 <= max_triangles <= typemax(Int) ||
        throw(ArgumentError("max_triangles must be a nonnegative machine-sized integer"))
    map === nothing || _validate_domain_map(ws, map)
    st, s = ws._state, ws._snapshot
    mt = Int(max_triangles)
    if v == 0
        sign === nothing || throw(ArgumentError("use value keyword for unary Max-Cut proof"))
        req_orig = if value === nothing
            nothing
        elseif map === nothing
            _assignment(ws, value)
        else
            _lift_index_value(map, u, _check_domain_scalar(value, map.target_domain))
        end
        st.fixed[u] == 2 || return (nothing, :already_fixed, :none, nothing, 0, 0, 0, 0)
        direction = _direction(s)
        direction != 0 || return (nothing, :zero_scale, :none, nothing, 0, 0, 0, 0)
        g_u = map === nothing ? 1 : map.gauge[u]
        cand_signs = if req_orig !== nothing
            s_req = (s.domain === QT.BoolDomain && req_orig == 0) ? -1 : req_orig
            (s_req,)
        else
            J_u0 = direction * _spin_field(ws, u)
            pref = g_u * J_u0 <= 0 ? g_u : -g_u
            (pref, -pref)
        end
        ok, reason, meth, orig_sigma, margin, direct_w, non_tri, tris, g_w, t_w, ex_w = _eval_maxcut_anchor(
            ws, u, 0, cand_signs, direction, allow_weak, mt,
            Int(max_work), Int(max_exact_work), deadline_ns,
        )
        total_visits = g_w + t_w
        if !ok
            return (
                nothing, reason, meth, reason in (:deadline, :work_limit, :verification_limit) ? nothing : margin,
                length(tris), g_w, t_w, ex_w,
            )
        end
        low_orig = s.domain === QT.BoolDomain ? 0 : -1
        orig_val = orig_sigma == 1 ? 1 : low_orig
        mapped_sigma = g_u * orig_sigma
        c_val = _mapped_constant(ws, map)
        pers = margin > 0 ? :strong : :weak
        step = MaxCutStep(
            u, 0, u, mapped_sigma, orig_sigma, orig_val,
            deepcopy(margin), deepcopy(direct_w), deepcopy(non_tri), tris,
            deepcopy(c_val), predecessors, meth, scope_length, pers,
        )
        return (step, :proved, meth, deepcopy(margin), length(tris), g_w, t_w, ex_w)
    else
        value === nothing || throw(ArgumentError("use sign keyword for pair Max-Cut proof"))
        sign === nothing || (!(sign isa Bool) && sign in (-1, 1)) ||
            throw(ArgumentError("Max-Cut relation sign must be -1, +1 or nothing"))
        u != v || throw(ArgumentError("Max-Cut pair relation requires two distinct variables"))
        (st.fixed[u] == 2 && st.fixed[v] == 2) ||
            return (nothing, :already_fixed, :none, nothing, 0, 0, 0, 0)
        direction = _direction(s)
        direction != 0 || return (nothing, :zero_scale, :none, nothing, 0, 0, 0, 0)
        g_u = map === nothing ? 1 : map.gauge[u]
        g_v = map === nothing ? 1 : map.gauge[v]
        cand_signs = if sign !== nothing
            (g_u * g_v * Int(sign),)
        else
            J_uv = _ws_mc_J(ws, u, v, direction)
            pref = (g_u * g_v) * J_uv <= 0 ? (g_u * g_v) : -(g_u * g_v)
            (pref, -pref)
        end
        ok_u, reason_u, meth_u, sig_u, marg_u, dir_u, ntri_u, tris_u, gw_u, tw_u, ex_u = _eval_maxcut_anchor(
            ws, u, v, cand_signs, direction, allow_weak, mt,
            Int(max_work), Int(max_exact_work), deadline_ns,
        )
        if reason_u in (:deadline, :work_limit, :verification_limit)
            return (nothing, reason_u, meth_u, nothing, 0, gw_u, tw_u, ex_u)
        end
        if ok_u && marg_u > 0 && meth_u === :maxcut_edge
            mapped_sigma = g_u * g_v * sig_u
            c_val = _mapped_constant(ws, map)
            step = MaxCutStep(
                u, v, u, mapped_sigma, sig_u, 0,
                deepcopy(marg_u), deepcopy(dir_u), deepcopy(ntri_u), tris_u,
                deepcopy(c_val), predecessors, meth_u, scope_length, :strong,
            )
            return (step, :proved, meth_u, deepcopy(marg_u), length(tris_u), gw_u, tw_u, ex_u)
        end
        rem_work = Int(max_work) - gw_u - tw_u
        rem_exact = Int(max_exact_work) - ex_u
        ok_v, reason_v, meth_v, sig_v, marg_v, dir_v, ntri_v, tris_v, gw_v, tw_v, ex_v = _eval_maxcut_anchor(
            ws, v, u, cand_signs, direction, allow_weak, mt,
            rem_work, rem_exact, deadline_ns,
        )
        gw_tot = gw_u + gw_v
        tw_tot = tw_u + tw_v
        ex_tot = ex_u + ex_v
        if reason_v in (:deadline, :work_limit, :verification_limit)
            return (nothing, reason_v, meth_v, nothing, 0, gw_tot, tw_tot, ex_tot)
        end
        use_v = if ok_v && !ok_u
            true
        elseif ok_u && ok_v
            marg_v > marg_u
        else
            marg_v > marg_u
        end
        chosen_ok = use_v ? ok_v : ok_u
        chosen_anchor = use_v ? v : u
        chosen_meth = use_v ? meth_v : meth_u
        chosen_sig = use_v ? sig_v : sig_u
        chosen_marg = use_v ? marg_v : marg_u
        chosen_dir = use_v ? dir_v : dir_u
        chosen_ntri = use_v ? ntri_v : ntri_u
        chosen_tris = use_v ? tris_v : tris_u
        if !chosen_ok
            return (nothing, :not_strict, chosen_meth, deepcopy(chosen_marg), length(chosen_tris), gw_tot, tw_tot, ex_tot)
        end
        mapped_sigma = g_u * g_v * chosen_sig
        c_val = _mapped_constant(ws, map)
        pers = chosen_marg > 0 ? :strong : :weak
        step = MaxCutStep(
            u, v, chosen_anchor, mapped_sigma, chosen_sig, 0,
            deepcopy(chosen_marg), deepcopy(chosen_dir), deepcopy(chosen_ntri), chosen_tris,
            deepcopy(c_val), predecessors, chosen_meth, scope_length, pers,
        )
        return (step, :proved, chosen_meth, deepcopy(chosen_marg), length(chosen_tris), gw_tot, tw_tot, ex_tot)
    end
end

