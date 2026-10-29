# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    DominanceStep

Compact unary dominance/persistency witness. Bounds enclose the normalized
derivative (or component-marginal difference when `method === :marginal`) of
the unscaled objective: normalization multiplies by the sign of scale and
objective sense, never by a potentially overflowing magnitude. `predecessors`
is the number of preceding steps in the ordered certificate prefix; every
preceding deduction is therefore explicit without copying the chain per step.
`constant` binds the exact conditioned offset. `persistency` is `:strong`
(all optima satisfy `variable == value`) or `:weak` (at least one optimum of
the current conditioned residual satisfies `variable == value`). Indices refer
to original variable order.
"""
struct DominanceStep <: _ProofRecord
    variable::Int
    value::Int
    lower::_Exact
    upper::_Exact
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
    persistency::Symbol
end
DominanceStep(i,v,lo,hi,c,p,m) = DominanceStep(i,v,lo,hi,c,p,m,-1,:strong)
DominanceStep(i,v,lo,hi,c,p,m,s) = DominanceStep(i,v,lo,hi,c,p,m,s,:strong)

"""
    RelationStep

Compact signed pair relation witness certifying the substitution
``s_{\\text{eliminated}} = \\sigma_{\\text{orig}} s_{\\text{representative}}`` in
original canonical spin coordinates (equivalently ``x_u = x_v`` for
``\\sigma_{\\text{orig}} = +1`` and ``x_u = 1 - x_v`` for
``\\sigma_{\\text{orig}} = -1`` in binary coordinates), and
``t_{\\text{eliminated}} = \\sigma t_{\\text{representative}}`` (`sign`) in the
certificate's active coordinate representation. For `method in (:interval, :exact)`,
`lower` and `upper` enclose the normalized single-flip spin energy difference
``-\\sigma \\tilde{J}_{uv} \\mp (|\\tilde{h}_u| + \\sum_{w \\ne v} |\\tilde{J}_{uw}|)``.
For `method === :glk_pair`, `lower` and `upper` record the exact Glover–Lewis–Kochenberger
cross-endpoint flip margins ruling out the two violating states
``(t_u, t_v) \\in \\{(-\\sigma, +1), (+\\sigma, -1)\\}``.
For `method === :coflip_pair`, `lower` and `upper` record the exact shared-neighborhood
co-flip bounds ``-\\sigma \\tilde{J}_{uv} \\mp \\frac{1}{2}(|\\tilde{h}_u - \\sigma \\tilde{h}_v| + \\sum_{w \\notin \\{u,v\\}} |\\tilde{J}_{uw} - \\sigma \\tilde{J}_{vw}|)``.
`persistency` is `:strong` when `lower > 0` and `:weak` when `lower == 0`.
"""
struct RelationStep <: _ProofRecord
    eliminated::Int
    representative::Int
    sign::Int
    orig_sign::Int
    lower::_Exact
    upper::_Exact
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
    persistency::Symbol
end
RelationStep(u,v,s,os,lo,hi,c,p,m) = RelationStep(u,v,s,os,lo,hi,c,p,m,-1,:strong)
RelationStep(u,v,s,os,lo,hi,c,p,m,sc) = RelationStep(u,v,s,os,lo,hi,c,p,m,sc,:strong)

"""
    EliminationStep

Compact bounded-degree (`0 <= length(neighbors) <= 3`) exact local variable
elimination witness certifying
``F'(y) = \\operatorname{opt}_{x_u} F(y, x_u)`` across all ``2^d \\le 8``
boundary assignments of `neighbors` (stored in ascending original-index order).
`table` stores the reconstructing original-domain assignment for `variable`
indexed by `1 + sum(((z_b == 1) << (b - 1)) for b in 1:d)`. `constant_delta`,
`linear_deltas` and `quadratic_deltas` store the exact source-domain polynomial
update induced by eliminating `variable`. `unique_argmin` is `true` when the
minimizing value of `variable` is strict (`L_u(z) != 0`) for every boundary
configuration `z`.
"""
struct EliminationStep <: _ProofRecord
    variable::Int
    neighbors::Tuple{Vararg{Int}}
    table::Tuple{Vararg{Int}}
    constant_delta::_Exact
    linear_deltas::Tuple{Vararg{Pair{Int,_Exact}}}
    quadratic_deltas::Tuple{Vararg{Tuple{Int,Int,_Exact}}}
    constant::_Exact
    predecessors::Int
    scope_length::Int
    unique_argmin::Bool
end
EliminationStep(u,nbrs,tbl,cd,ld,qd,c,p) = EliminationStep(u,nbrs,tbl,cd,ld,qd,c,p,-1,true)

"""
    ProbingStep

Compact trial-branch probing witness certifying `variable == value` by refuting
the opposite assignment `variable == probed_value` against a verified parent-scope
feasible witness `witness_state` with normalized energy `witness_upper`. After
temporarily conditioning on `variable == probed_value` and applying the certified
trial deductions `branch_steps`, `branch_lower` bounds the normalized trial-branch
objective from below and strictly exceeds `witness_upper` (`branch_lower > witness_upper`,
`persistency === :strong`).
"""
struct ProbingStep <: _ProofRecord
    variable::Int
    value::Int
    probed_value::Int
    branch_lower::_Exact
    witness_upper::_Exact
    witness_state::Tuple{Vararg{Int}}
    branch_steps::Tuple{Vararg{DominanceStep}}
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
    persistency::Symbol
end
ProbingStep(i, v, pv, blo, wup, ws, bs, c, p, m) =
    ProbingStep(i, v, pv, blo, wup, ws, bs, c, p, m, -1, :strong)
ProbingStep(i, v, pv, blo, wup, ws, bs, c, p, m, sc) =
    ProbingStep(i, v, pv, blo, wup, ws, bs, c, p, m, sc, :strong)

"""
    RoofDualityStep

Recorded strongly persistent variable-fixing proof step derived from the exact
rational implication-network (posiform / roof-duality) relaxation on the
active residual model.
"""
struct RoofDualityStep <: _ProofRecord
    variable::Int
    value::Int
    roof_lower::_Exact
    max_flow::_Exact
    flow_edges::Tuple{Vararg{Tuple{Int,Int,_Exact}}}
    batch_fixings::Tuple{Vararg{Pair{Int,Int}}}
    batch_index::Int
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
    persistency::Symbol
end
RoofDualityStep(i, v, rlo, mf, fe, bf, bi, c, p, m) =
    RoofDualityStep(i, v, rlo, mf, fe, bf, bi, c, p, m, -1, :strong)
RoofDualityStep(i, v, rlo, mf, fe, bf, bi, c, p, m, sc) =
    RoofDualityStep(i, v, rlo, mf, fe, bf, bi, c, p, m, sc, :strong)

"""
    SubmodularCutStep

Recorded variable-fixing proof step derived from an exact rational Kolmogorov–Zabih
``s``–``t`` min-cut / max-flow pass on a closed gauge-submodular residual
component `component_variables` with certified bipartite spin gauge `gauge`.
Tagged `:strong` when the variable's cut side is mandatory across all minimum
cuts (``u \\in \\mathcal{R}_S \\cup \\mathcal{R}_T``), or `:weak` when
`allow_weak=true` commits a jointly compatible minimum cut across the entire
closed component.
"""
struct SubmodularCutStep <: _ProofRecord
    variable::Int
    value::Int
    component_variables::Tuple{Vararg{Int}}
    gauge::Tuple{Vararg{Int}}
    component_opt::_Exact
    max_flow::_Exact
    flow_edges::Tuple{Vararg{Tuple{Int,Int,_Exact}}}
    batch_fixings::Tuple{Vararg{Pair{Int,Int}}}
    batch_index::Int
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
    persistency::Symbol
end
SubmodularCutStep(i, v, cv, g, copt, mf, fe, bf, bi, c, p, m) =
    SubmodularCutStep(i, v, cv, g, copt, mf, fe, bf, bi, c, p, m, -1, :strong)
SubmodularCutStep(i, v, cv, g, copt, mf, fe, bf, bi, c, p, m, sc) =
    SubmodularCutStep(i, v, cv, g, copt, mf, fe, bf, bi, c, p, m, sc, :strong)

"""
    MaxCutStep

Compact weighted Max-Cut edge or triangle preprocessing witness on the active
residual Max-Cut graph ``G_{\\text{MC}} = (\\{0\\} \\cup F, E_{\\text{cut}}, w)``.
When `representative == 0`, certifies the unary variable fixing
`eliminated => value` (``s_{\\text{eliminated}} = \\sigma_{\\text{orig}}`` via
contraction with reference vertex `0`). When `representative > 0`, certifies the
signed pair contraction ``s_{\\text{eliminated}} = \\sigma_{\\text{orig}} s_{\\text{representative}}``
(and ``t_{\\text{eliminated}} = \\sigma t_{\\text{representative}}`` in the active
coordinate representation). `anchor` (`eliminated` or `representative`) records
the vertex whose subset-flip neighborhood ``\\{a\\} \\cup S_{\\text{flip}}``
produces the exact normalized energy-improvement lower bound `margin`
(`direct_weight + sum(t[5] for t in triangles) - non_triangle_slack`).
`method` is `:maxcut_edge` when `isempty(triangles)` and `:maxcut_triangle`
when at least one triangle witness `(c, J_ac, J_bc, R_c, gamma_c)` contributes
a strictly positive net gain ``\\gamma_c > -|J_{ac}|``.
"""
struct MaxCutStep <: _ProofRecord
    eliminated::Int
    representative::Int
    anchor::Int
    sign::Int
    orig_sign::Int
    value::Int
    margin::_Exact
    direct_weight::_Exact
    non_triangle_slack::_Exact
    triangles::Tuple{Vararg{Tuple{Int,_Exact,_Exact,_Exact,_Exact}}}
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
    persistency::Symbol
end
MaxCutStep(u, v, a, s, os, val, mrg, dw, nts, tris, c, p, m) =
    MaxCutStep(u, v, a, s, os, val, mrg, dw, nts, tris, c, p, m, -1, :strong)
MaxCutStep(u, v, a, s, os, val, mrg, dw, nts, tris, c, p, m, sc) =
    MaxCutStep(u, v, a, s, os, val, mrg, dw, nts, tris, c, p, m, sc, :strong)

"""
    DominanceCertificate

Owned source/generation, explicit caller scope and ordered reduction steps
([`DominanceStep`](@ref), [`RelationStep`](@ref), [`EliminationStep`](@ref),
[`ProbingStep`](@ref), [`RoofDualityStep`](@ref), [`SubmodularCutStep`](@ref),
[`MaxCutStep`](@ref)).
Every step retains all scoped optima (`:strong`) or at least one scoped optimum
of the evolving residual (`:weak` / non-unique argmin). Also aliased as
[`ReductionCertificate`](@ref).
"""
struct DominanceCertificate
    generation::Generation
    _scope_checkpoint::Checkpoint
    assumptions::Tuple
    steps::Tuple
    _source::_Snapshot
    _map::Union{Nothing,DomainGaugeMap}
end
DominanceCertificate(g,cp,a,s,src) = DominanceCertificate(g,cp,a,s,src,nothing)
generation(c::DominanceCertificate) = c.generation

function Base.deepcopy_internal(s::EliminationStep, dict::IdDict)
    haskey(dict, s) && return dict[s]::EliminationStep
    return EliminationStep(
        s.variable,
        _deepcopy_tuple(s.neighbors, dict),
        _deepcopy_tuple(s.table, dict),
        Base.deepcopy_internal(s.constant_delta, dict),
        _deepcopy_tuple(s.linear_deltas, dict),
        _deepcopy_tuple(s.quadratic_deltas, dict),
        Base.deepcopy_internal(s.constant, dict),
        s.predecessors,
        s.scope_length,
        s.unique_argmin,
    )
end

function Base.deepcopy_internal(s::ProbingStep, dict::IdDict)
    haskey(dict, s) && return dict[s]::ProbingStep
    return ProbingStep(
        s.variable,
        s.value,
        s.probed_value,
        Base.deepcopy_internal(s.branch_lower, dict),
        Base.deepcopy_internal(s.witness_upper, dict),
        _deepcopy_tuple(s.witness_state, dict),
        _deepcopy_tuple(s.branch_steps, dict),
        Base.deepcopy_internal(s.constant, dict),
        s.predecessors,
        s.method,
        s.scope_length,
        s.persistency,
    )
end

function Base.deepcopy_internal(s::RoofDualityStep, dict::IdDict)
    haskey(dict, s) && return dict[s]::RoofDualityStep
    return RoofDualityStep(
        s.variable,
        s.value,
        Base.deepcopy_internal(s.roof_lower, dict),
        Base.deepcopy_internal(s.max_flow, dict),
        _deepcopy_tuple(s.flow_edges, dict),
        _deepcopy_tuple(s.batch_fixings, dict),
        s.batch_index,
        Base.deepcopy_internal(s.constant, dict),
        s.predecessors,
        s.method,
        s.scope_length,
        s.persistency,
    )
end

function Base.deepcopy_internal(s::SubmodularCutStep, dict::IdDict)
    haskey(dict, s) && return dict[s]::SubmodularCutStep
    return SubmodularCutStep(
        s.variable,
        s.value,
        _deepcopy_tuple(s.component_variables, dict),
        _deepcopy_tuple(s.gauge, dict),
        Base.deepcopy_internal(s.component_opt, dict),
        Base.deepcopy_internal(s.max_flow, dict),
        _deepcopy_tuple(s.flow_edges, dict),
        _deepcopy_tuple(s.batch_fixings, dict),
        s.batch_index,
        Base.deepcopy_internal(s.constant, dict),
        s.predecessors,
        s.method,
        s.scope_length,
        s.persistency,
    )
end

function Base.deepcopy_internal(s::MaxCutStep, dict::IdDict)
    haskey(dict, s) && return dict[s]::MaxCutStep
    return MaxCutStep(
        s.eliminated,
        s.representative,
        s.anchor,
        s.sign,
        s.orig_sign,
        s.value,
        Base.deepcopy_internal(s.margin, dict),
        Base.deepcopy_internal(s.direct_weight, dict),
        Base.deepcopy_internal(s.non_triangle_slack, dict),
        _deepcopy_tuple(s.triangles, dict),
        Base.deepcopy_internal(s.constant, dict),
        s.predecessors,
        s.method,
        s.scope_length,
        s.persistency,
    )
end

function Base.deepcopy_internal(c::DominanceCertificate, dict::IdDict)
    haskey(dict, c) && return dict[c]::DominanceCertificate
    return DominanceCertificate(
        c.generation,
        c._scope_checkpoint,
        _deepcopy_tuple(c.assumptions, dict),
        _deepcopy_tuple(c.steps, dict),
        Base.deepcopy_internal(c._source, dict),
        Base.deepcopy_internal(c._map, dict),
    )
end

"""
    ReductionCertificate

Alias for [`DominanceCertificate`](@ref) representing an ordered certificate
chain of unary dominance restrictions, signed pair relation contractions,
bounded-degree exact variable eliminations, and certified probing steps.
"""
const ReductionCertificate = DominanceCertificate

"""
    step_guarantee(step_or_map)

Return the algebraic guarantee class of a preprocessing step or coordinate map:
- `:energy_identity` for [`DomainGaugeMap`](@ref),
- `:exact_elimination` for [`EliminationStep`](@ref),
- `:optimum_preserving_restriction` for [`DominanceStep`](@ref), [`RelationStep`](@ref), [`ProbingStep`](@ref), [`RoofDualityStep`](@ref), [`SubmodularCutStep`](@ref), and [`MaxCutStep`](@ref).
"""
step_guarantee(::DomainGaugeMap) = :energy_identity
step_guarantee(::EliminationStep) = :exact_elimination
step_guarantee(::Union{DominanceStep,RelationStep,ProbingStep,RoofDualityStep,SubmodularCutStep,MaxCutStep}) = :optimum_preserving_restriction

"""
    persistency(step_or_certificate)

Return `:strong` when a step, map, or certificate preserves all optima on its
scope, or `:weak` when any step relies on tie-breaking / weak persistency.
"""
persistency(::DomainGaugeMap) = :strong
persistency(step::Union{DominanceStep,RelationStep,ProbingStep,RoofDualityStep,SubmodularCutStep,MaxCutStep}) = step.persistency
persistency(step::EliminationStep) = step.unique_argmin ? :strong : :weak
persistency(cert::DominanceCertificate) =
    any(s -> persistency(s) === :weak, cert.steps) ? :weak : :strong

"""
    certificate_guarantee(cert::DominanceCertificate)

Return the overall guarantee class of `cert`:
- `:energy_identity` when `cert.steps` is empty,
- `:exact_elimination` when every step in `cert.steps` is an [`EliminationStep`](@ref),
- `:optimum_preserving_restriction` when `cert.steps` contains any [`DominanceStep`](@ref), [`RelationStep`](@ref), [`ProbingStep`](@ref), or [`RoofDualityStep`](@ref).
"""
function certificate_guarantee(cert::DominanceCertificate)
    isempty(cert.steps) && return :energy_identity
    all(s -> s isa EliminationStep, cert.steps) && return :exact_elimination
    return :optimum_preserving_restriction
end

"""Proof attempt with optional `certificate`, `stop_reason`, numeric `method`,
adjacency `edge_visits`, and explicit `exact_fallbacks`/`exact_work` counters."""
struct DominanceAttempt
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    edge_visits::Int
    exact_fallbacks::Int
    exact_work::Int
end

"""Relation proof attempt with optional `certificate`, `stop_reason`, numeric
`method`, adjacency `edge_visits`, and explicit `exact_fallbacks`/`exact_work` counters."""
struct RelationAttempt
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    edge_visits::Int
    exact_fallbacks::Int
    exact_work::Int
end

"""Local variable elimination proof attempt with optional `certificate`,
`stop_reason`, numeric `method`, adjacency `edge_visits`, and `exact_work`."""
struct EliminationAttempt
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    edge_visits::Int
    exact_work::Int
end

"""Certified probing proof attempt with optional `certificate`, `stop_reason`,
numeric `method`, adjacency `edge_visits`, and explicit `exact_fallbacks`/`exact_work` counters."""
struct ProbingAttempt
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    edge_visits::Int
    exact_fallbacks::Int
    exact_work::Int
end

"""Certified roof-duality proof attempt with optional `certificate`, `stop_reason`,
`method`, exact normalized `lower_bound`, scaled `objective_bound`, implication-network
`max_flow`, strongly persistent `fixings`, and phase-separated work counters."""
struct RoofDualityAttempt{V,S}
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    lower_bound::Union{Nothing,_Exact}
    objective_bound::Union{Nothing,_Exact}
    max_flow::Union{Nothing,_Exact}
    fixings::Vector{Pair{V,S}}
    graph_work::Int
    flow_work::Int
    verification_work::Int
    edge_visits::Int
    exact_work::Int
end

"""Certified gauge-submodular component cut proof attempt with optional `certificate`,
`stop_reason`, `method`, exact normalized `component_opt`, `max_flow`, discovered
bipartite `gauge`, complete optimal component `assignment`, certified `fixings`,
and phase-separated work counters (`recognition_work`, `graph_work`, `flow_work`,
`verification_work`, `edge_visits`, `exact_work`)."""
struct SubmodularCutAttempt{V,S}
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    component_opt::Union{Nothing,_Exact}
    max_flow::Union{Nothing,_Exact}
    gauge::Vector{Pair{V,Int}}
    assignment::Vector{Pair{V,S}}
    fixings::Vector{Pair{V,S}}
    recognition_work::Int
    graph_work::Int
    flow_work::Int
    verification_work::Int
    edge_visits::Int
    exact_work::Int
end

"""Certified weighted Max-Cut edge or triangle proof attempt with optional
`certificate`, `stop_reason`, `method` (`:maxcut_edge` or `:maxcut_triangle`),
exact normalized flip `margin`, `triangles_used`, and phase-separated work
counters (`graph_work`, `triangle_work`, `edge_visits`, `exact_work`)."""
struct MaxCutAttempt
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    margin::Union{Nothing,_Exact}
    triangles_used::Int
    graph_work::Int
    triangle_work::Int
    edge_visits::Int
    exact_work::Int
end

"""Read-only verification result: `valid`, `stop_reason` and charged `term_visits`.
A budget/deadline stop is not verification success."""
struct VerificationResult
    valid::Bool
    stop_reason::Symbol
    term_visits::Int
end

_caller_scope(ws::Workspace) = Tuple((ws._state.trail[p]::_UndoFix).index => (ws._state.trail[p]::_UndoFix).value
                                    for p in ws._state.callers)
_direction(s::_Snapshot) = iszero(s.scale) ? 0 :
    (s.sense === QT.Min ? 1 : -1) * (signbit(s.scale) ? -1 : 1)

# Check the enclosure against the exact cached field rather than assuming a
# rational-to-float conversion is correctly rounded. No global rounding mode.
function _enclose(q::_Exact)
    v = Float64(q)
    isfinite(v) || return (-Inf,Inf)
    exact = _Exact(v)
    if exact == q
        return v, v
    elseif exact > q
        lo = prevfloat(v)
        isfinite(lo) && _Exact(lo) <= q || return (-Inf,Inf)
        return lo, v
    else
        hi = nextfloat(v)
        isfinite(hi) && q <= _Exact(hi) || return (-Inf,Inf)
        return v, hi
    end
end

@inline _prevfloat_finite(x::Float64) = isfinite(x) ? prevfloat(x) : NaN
@inline _nextfloat_finite(x::Float64) = isfinite(x) ? nextfloat(x) : NaN
@inline _min_nan(a::Float64, b::Float64) = (isnan(a) || isnan(b)) ? NaN : min(a, b)
@inline _max_nan(a::Float64, b::Float64) = (isnan(a) || isnan(b)) ? NaN : max(a, b)

function _strict_value(lower, upper, domain)
    lower > 0 && return domain === QT.BoolDomain ? 0 : -1
    upper < 0 && return 1
    return nothing
end

function _weak_value(lower, upper, domain)
    lower >= 0 && return domain === QT.BoolDomain ? 0 : -1
    upper <= 0 && return 1
    return nothing
end

const _MAX_MARGINAL_COMPONENT = 4

function _marginal_dominance_witness(
    ws::Workspace,
    i::Int,
    map::Union{Nothing,DomainGaugeMap},
    req_mapped::Union{Nothing,Int},
    direction::Int,
    visits::Int,
    exact_work::Int,
    max_work::Int,
    max_exact_work::Int,
    deadline_ns,
    predecessors::Int,
    scope_length::Int,
)
    st, s = ws._state, ws._snapshot
    comp = Int[i]
    head = 1
    while head <= length(comp)
        u = comp[head]
        head += 1
        for (w, q) in st.adjacency[u]
            _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, 1, exact_work)
            visits < max_work || return (nothing, :work_limit, :exact, visits, 1, exact_work)
            visits += 1
            (st.fixed[w] == 2 && !iszero(q)) || continue
            if !(w in comp)
                length(comp) < _MAX_MARGINAL_COMPONENT ||
                    return (nothing, :not_strict, :exact, visits, 1, exact_work)
                push!(comp, w)
            end
        end
    end
    others = sort!(comp[2:end])
    d_c = length(others)
    num_states = 1 << (d_c + 1)
    num_states <= max_exact_work - exact_work ||
        return (nothing, :verification_limit, :exact, visits, 1, exact_work)
    is_bool = s.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    sub_edges = Tuple{Int,Int,_Exact}[]
    all_nodes = vcat(i, others)
    for a in 1:length(all_nodes)
        u = all_nodes[a]
        for (w, q) in st.adjacency[u]
            st.fixed[w] == 2 && u < w && !iszero(q) || continue
            b = findfirst(==(w), all_nodes)
            b !== nothing && push!(sub_edges, (a, b, q))
        end
    end
    best_orig = Dict{Int,_Exact}()
    vals = Vector{Int}(undef, length(all_nodes))
    for x_i in (low_orig, 1)
        vals[1] = x_i
        best_val = _Exact(0)
        has_best = false
        for mask in 0:((1 << d_c) - 1)
            _expired(deadline_ns) && return (nothing, :deadline, :marginal, visits, 1, exact_work)
            exact_work += 1
            for b in 1:d_c
                vals[b + 1] = ((mask >> (b - 1)) & 1) == 1 ? 1 : low_orig
            end
            e = _Exact(0)
            for a in 1:length(all_nodes)
                e += st.fields[all_nodes[a]] * vals[a]
            end
            for (a, b, q) in sub_edges
                e += q * vals[a] * vals[b]
            end
            de = direction * e
            if !has_best || de < best_val
                best_val = de
                has_best = true
            end
        end
        best_orig[x_i] = best_val
    end
    target_dom = map === nothing ? s.domain : _qt_domain(map.target_domain)
    low_target = target_dom === QT.BoolDomain ? 0 : -1
    orig_at_low = map === nothing ? low_orig : _lift_index_value(map, i, low_target)
    orig_at_high = map === nothing ? 1 : _lift_index_value(map, i, 1)
    delta_marg = best_orig[orig_at_high] - best_orig[orig_at_low]
    chosen_mapped = if req_mapped !== nothing
        ok = req_mapped == low_target ? (delta_marg >= 0) : (delta_marg <= 0)
        ok ? req_mapped : nothing
    else
        delta_marg >= 0 ? low_target : 1
    end
    chosen_mapped === nothing && return (nothing, :not_strict, :exact, visits, 1, exact_work)
    chosen_orig = map === nothing ? chosen_mapped : _lift_index_value(map, i, chosen_mapped)
    c_val = _mapped_constant(ws, map)
    pers = iszero(delta_marg) ? :weak : :strong
    step = DominanceStep(
        i,
        chosen_orig,
        deepcopy(delta_marg),
        deepcopy(delta_marg),
        deepcopy(c_val),
        predecessors,
        :marginal,
        scope_length,
        pers,
    )
    return (step, :proved, :marginal, visits, 1, exact_work)
end

# Internal numeric seam for #4, #13 and #14: no model copy, proof export or assumption scan.
# Caller supplies predecessor count and persists the returned compact step.
function _dominance_witness(ws::Workspace, i::Int; map::Union{Nothing,DomainGaugeMap}=nothing,
                            allow_weak::Bool=false, value=nothing,
                            max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing,
                            predecessors=0, scope_length=-1)
    _limits(max_work,deadline_ns)
    _limits(max_exact_work,deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    st, s = ws._state, ws._snapshot
    req_mapped = if value === nothing
        nothing
    elseif map === nothing
        _assignment(ws, value)
    else
        _check_domain_scalar(value, map.target_domain)
    end
    st.fixed[i] == 2 || return (nothing,:already_fixed,:none,0,0,0)
    direction = _direction(s)
    direction != 0 || return (nothing,:zero_scale,:none,0,0,0)
    degree = length(st.adjacency[i])
    degree <= max_work || return (nothing,:work_limit,:none,0,0,0)
    _expired(deadline_ns) && return (nothing,:deadline,:none,0,0,0)
    target_dom = map === nothing ? s.domain : _qt_domain(map.target_domain)
    low_target = target_dom === QT.BoolDomain ? 0 : -1
    gauged_bool = map !== nothing && map.target_domain === :bool && !map._identity_gauge
    init_field = if map === nothing
        direction * st.fields[i]
    elseif map.target_domain === :spin
        direction * map.gauge[i] * _spin_field(ws, i)
    elseif !gauged_bool
        direction * _bool_field(ws, i)
    else
        2 * direction * map.gauge[i] * _spin_field(ws, i)
    end
    lo, hi = _enclose(init_field)
    lo_in, hi_in = hi, lo
    visits = 0
    for (j,q) in st.adjacency[i]
        _expired(deadline_ns) && return (nothing,:deadline,:interval,visits,0,0)
        visits += 1
        st.fixed[j] == 2 || continue
        if map === nothing
            q_lo, q_hi = _enclose(q)
            c_lo, c_hi = direction >= 0 ? (q_lo, q_hi) : (-q_hi, -q_lo)
            if s.domain === QT.BoolDomain
                a, b = min(0.0, c_lo), max(0.0, c_hi)
                a_in, b_in = min(0.0, c_hi), max(0.0, c_lo)
            else
                m = max(abs(c_lo), abs(c_hi))
                m_in = (c_lo <= 0.0 && c_hi >= 0.0) ? 0.0 : min(abs(c_lo), abs(c_hi))
                a, b = -m, m
                a_in, b_in = -m_in, m_in
            end
        elseif map.target_domain === :spin
            c_lo, c_hi = _enclose(direction * _mapped_coupling(ws, i, j, q, map))
            m = max(abs(c_lo), abs(c_hi))
            m_in = (c_lo <= 0.0 && c_hi >= 0.0) ? 0.0 : min(abs(c_lo), abs(c_hi))
            a, b = -m, m
            a_in, b_in = -m_in, m_in
        elseif !gauged_bool
            c_lo, c_hi = _enclose(direction * _bool_coupling(ws, q))
            a, b = min(0.0, c_lo), max(0.0, c_hi)
            a_in, b_in = min(0.0, c_hi), max(0.0, c_lo)
        else
            c_lo, c_hi = _enclose(2 * _spin_coupling(ws, q))
            m = max(abs(c_lo), abs(c_hi))
            m_in = (c_lo <= 0.0 && c_hi >= 0.0) ? 0.0 : min(abs(c_lo), abs(c_hi))
            a, b = -m, m
            a_in, b_in = -m_in, m_in
        end
        lo = _prevfloat_finite(lo + a)
        hi = _nextfloat_finite(hi + b)
        lo_in = _nextfloat_finite(lo_in + a_in)
        hi_in = _prevfloat_finite(hi_in + b_in)
    end
    mapped_val = isfinite(lo) && isfinite(hi) ? _strict_value(lo,hi,target_dom) : nothing
    _expired(deadline_ns) && return (nothing,:deadline,:interval,visits,0,0)
    if mapped_val !== nothing && (req_mapped === nothing || mapped_val == req_mapped)
        val = map === nothing ? mapped_val : _lift_index_value(map, i, mapped_val)
        c_val = _mapped_constant(ws, map)
        step = DominanceStep(i,val,_Exact(lo),_Exact(hi),deepcopy(c_val),predecessors,:interval,scope_length,:strong)
        return (step,:proved,:interval,visits,0,0)
    end
    if !allow_weak && isfinite(lo_in) && isfinite(hi_in)
        strictly_unproved = if req_mapped === nothing
            lo_in < 0.0 && hi_in > 0.0
        elseif req_mapped == low_target
            lo_in < 0.0
        else
            hi_in > 0.0
        end
        strictly_unproved && return (nothing,:not_strict,:interval,visits,0,0)
    end
    # Reserve the complete fallback before doing it. Exact work counts the
    # initial field and each free coefficient addition; adjacency visits include
    # both passes, including fixed neighbors skipped by arithmetic.
    degree <= max_work - visits || return (nothing,:work_limit,:interval,visits,0,0)
    degree < max_exact_work || return (nothing,:verification_limit,:interval,visits,0,0)
    lower = init_field
    upper = lower
    exact_work = 1
    for (j,q) in st.adjacency[i]
        _expired(deadline_ns) && return (nothing,:deadline,:exact,visits,1,exact_work)
        visits += 1
        st.fixed[j] == 2 || continue
        if map === nothing
            a = direction*q
            lower += s.domain === QT.BoolDomain ? min(0,a) : -abs(a)
            upper += s.domain === QT.BoolDomain ? max(0,a) : abs(a)
        elseif map.target_domain === :spin
            c = abs(_mapped_coupling(ws, i, j, q, map))
            lower -= c
            upper += c
        elseif !gauged_bool
            c = direction * _bool_coupling(ws, q)
            lower += min(0, c)
            upper += max(0, c)
        else
            c = 2 * abs(_spin_coupling(ws, q))
            lower -= c
            upper += c
        end
        exact_work += 1
    end
    _expired(deadline_ns) && return (nothing,:deadline,:exact,visits,1,exact_work)
    mapped_val = _strict_value(lower,upper,target_dom)
    if mapped_val !== nothing && (req_mapped === nothing || mapped_val == req_mapped)
        val = map === nothing ? mapped_val : _lift_index_value(map, i, mapped_val)
        c_val = _mapped_constant(ws, map)
        step = DominanceStep(i,val,deepcopy(lower),deepcopy(upper),deepcopy(c_val),predecessors,:exact,scope_length,:strong)
        return (step,:proved,:exact,visits,1,exact_work)
    end
    allow_weak || return (nothing,:not_strict,:exact,visits,1,exact_work)
    weak_mapped = if req_mapped !== nothing
        ok = req_mapped == low_target ? (lower >= 0) : (upper <= 0)
        ok ? req_mapped : nothing
    else
        _weak_value(lower, upper, target_dom)
    end
    if weak_mapped !== nothing
        val = map === nothing ? weak_mapped : _lift_index_value(map, i, weak_mapped)
        c_val = _mapped_constant(ws, map)
        step = DominanceStep(i,val,deepcopy(lower),deepcopy(upper),deepcopy(c_val),predecessors,:exact,scope_length,:weak)
        return (step,:proved,:exact,visits,1,exact_work)
    end
    return _marginal_dominance_witness(
        ws, i, map, req_mapped, direction, visits, exact_work,
        Int(max_work), Int(max_exact_work), deadline_ns, predecessors, scope_length,
    )
end

function _relation_deltas(ws::Workspace, u::Int, v::Int, orig_σ::Int)
    st, s = ws._state, ws._snapshot
    f_u = st.fields[u]
    q_uv = _Exact(0)
    other_edges = Pair{Int,_Exact}[]
    for (w, q) in st.adjacency[u]
        st.fixed[w] == 2 || continue
        if w == v
            q_uv = q
        else
            push!(other_edges, w => q)
        end
    end
    if s.domain === QT.SpinDomain
        const_delta = orig_σ * q_uv
        field_deltas = Pair{Int,_Exact}[v => orig_σ * f_u]
        quad_deltas = Tuple{Int,Int,_Exact}[
            (min(v, w), max(v, w), orig_σ * q) for (w, q) in other_edges
        ]
        return const_delta, field_deltas, quad_deltas
    elseif orig_σ == 1
        const_delta = _Exact(0)
        field_deltas = Pair{Int,_Exact}[v => (f_u + q_uv)]
        quad_deltas = Tuple{Int,Int,_Exact}[
            (min(v, w), max(v, w), q) for (w, q) in other_edges
        ]
        return const_delta, field_deltas, quad_deltas
    else
        const_delta = f_u
        field_deltas = Pair{Int,_Exact}[v => -f_u]
        for (w, q) in other_edges
            push!(field_deltas, w => q)
        end
        quad_deltas = Tuple{Int,Int,_Exact}[
            (min(v, w), max(v, w), -q) for (w, q) in other_edges
        ]
        return const_delta, field_deltas, quad_deltas
    end
end

function _relation_witness(ws::Workspace, u::Int, v::Int;
                           sign::Union{Nothing,Int}=nothing,
                           map::Union{Nothing,DomainGaugeMap}=nothing,
                           allow_weak::Bool=false,
                           max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing,
                           predecessors=0, scope_length=-1)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    sign === nothing || (!(sign isa Bool) && sign in (-1, 1)) ||
        throw(ArgumentError("relation sign must be -1, +1 or nothing"))
    u != v || throw(ArgumentError("relation requires two distinct variables"))
    st, s = ws._state, ws._snapshot
    (st.fixed[u] == 2 && st.fixed[v] == 2) || return (nothing, :already_fixed, :none, 0, 0, 0)
    direction = _direction(s)
    direction != 0 || return (nothing, :zero_scale, :none, 0, 0, 0)
    degree = length(st.adjacency[u])
    degree <= max_work || return (nothing, :work_limit, :none, 0, 0, 0)
    _expired(deadline_ns) && return (nothing, :deadline, :none, 0, 0, 0)
    g_u = map === nothing ? 1 : map.gauge[u]
    g_v = map === nothing ? 1 : map.gauge[v]
    h_u_raw = _spin_field(ws, u)
    hu_lo, hu_hi = _enclose(h_u_raw)
    h_lo, h_hi = (direction * g_u >= 0) ? (hu_lo, hu_hi) : (-hu_hi, -hu_lo)
    h_abs_hi = max(abs(h_lo), abs(h_hi))
    h_abs_lo = (h_lo <= 0.0 && h_hi >= 0.0) ? 0.0 : min(abs(h_lo), abs(h_hi))
    rad_hi = h_abs_hi
    rad_other_lo = 0.0
    shared_v_lo = 0.0
    cancel_pos_hi = 0.0
    cancel_neg_hi = 0.0
    j_uv_lo, j_uv_hi = 0.0, 0.0
    q_uv = _Exact(0)
    visits = 0
    is_spin_dom = s.domain === QT.SpinDomain
    for (w, q) in st.adjacency[u]
        _expired(deadline_ns) && return (nothing, :deadline, :interval, visits, 0, 0)
        visits += 1
        st.fixed[w] == 2 || continue
        g_w = map === nothing ? 1 : map.gauge[w]
        q_lo, q_hi = _enclose(q)
        if !is_spin_dom
            q_lo = prevfloat(0.25 * q_lo)
            q_hi = nextfloat(0.25 * q_hi)
        end
        c_lo, c_hi = (direction * (g_u * g_w) >= 0) ? (q_lo, q_hi) : (-q_hi, -q_lo)
        if w == v
            q_uv = q
            j_uv_lo, j_uv_hi = c_lo, c_hi
        else
            m = max(abs(c_lo), abs(c_hi))
            m_in = (c_lo <= 0.0 && c_hi >= 0.0) ? 0.0 : min(abs(c_lo), abs(c_hi))
            rad_hi = _nextfloat_finite(rad_hi + m)
            rad_other_lo = _prevfloat_finite(rad_other_lo + m_in)
            pos_vw = get(st.adj_pos[v], w, 0)
            if pos_vw != 0
                q_vw = st.adjacency[v][pos_vw].second
                if !iszero(q_vw)
                    qv_lo, qv_hi = _enclose(q_vw)
                    if !is_spin_dom
                        qv_lo = prevfloat(0.25 * qv_lo)
                        qv_hi = nextfloat(0.25 * qv_hi)
                    end
                    cv_lo, cv_hi = (direction * (g_v * g_w) >= 0) ? (qv_lo, qv_hi) : (-qv_hi, -qv_lo)
                    mv_hi = max(abs(cv_lo), abs(cv_hi))
                    mv_lo = (cv_lo <= 0.0 && cv_hi >= 0.0) ? 0.0 : min(abs(cv_lo), abs(cv_hi))
                    shared_v_lo = _prevfloat_finite(shared_v_lo + mv_lo)
                    if (c_hi > 0.0 && cv_hi > 0.0) || (c_lo < 0.0 && cv_lo < 0.0)
                        cancel_pos_hi = _nextfloat_finite(cancel_pos_hi + min(m, mv_hi))
                    end
                    if (c_hi > 0.0 && cv_lo < 0.0) || (c_lo < 0.0 && cv_hi > 0.0)
                        cancel_neg_hi = _nextfloat_finite(cancel_neg_hi + min(m, mv_hi))
                    end
                end
            end
        end
    end
    q_uv_mapped_nonpos = iszero(q_uv) || ((direction * (g_u * g_v) >= 0) ? (q_uv < 0) : (q_uv > 0))
    σ = sign !== nothing ? Int(sign) : (q_uv_mapped_nonpos ? 1 : -1)
    orig_σ = g_u * g_v * σ
    center_lo, center_hi = σ == 1 ? (-j_uv_hi, -j_uv_lo) : (j_uv_lo, j_uv_hi)
    lo = _prevfloat_finite(center_lo - rad_hi)
    hi = _nextfloat_finite(center_hi + rad_hi)
    _expired(deadline_ns) && return (nothing, :deadline, :interval, visits, 0, 0)
    if isfinite(lo) && isfinite(hi) && lo > 0
        c_val = _mapped_constant(ws, map)
        step = RelationStep(u, v, σ, orig_σ, _Exact(lo), _Exact(hi), deepcopy(c_val),
                            predecessors, :interval, scope_length, :strong)
        return (step, :proved, :interval, visits, 0, 0)
    end
    hv_raw = _spin_field(ws, v)
    hvr_lo, hvr_hi = _enclose(hv_raw)
    hv_lo, hv_hi = (direction * g_v >= 0) ? (hvr_lo, hvr_hi) : (-hvr_hi, -hvr_lo)
    rv_lo = shared_v_lo
    has_summary = st.lower !== nothing && st.upper !== nothing
    rad_v_other_lo = 0.0
    if has_summary
        up_v_lo, _ = _enclose(st.upper[v])
        _, lo_v_hi = _enclose(st.lower[v])
        scale_inv = is_spin_dom ? 0.5 : 0.25
        tot_v_lo = _prevfloat_finite(scale_inv * _prevfloat_finite(up_v_lo - lo_v_hi))
        j_abs_hi = max(abs(j_uv_lo), abs(j_uv_hi))
        rad_v_other_lo = _prevfloat_finite(tot_v_lo - j_abs_hi)
        rv_lo = max(rv_lo, rad_v_other_lo)
    end
    function _coflip_cand_possible(s_cand::Int; strict_only::Bool=false)
        c_cand_hi = s_cand == 1 ? -j_uv_lo : j_uv_hi
        if iszero(q_uv)
            (!strict_only && allow_weak && st.degrees[u] == st.degrees[v] && abs(h_u_raw) == abs(hv_raw)) || return false
            (direction * g_u * h_u_raw) == s_cand * (direction * g_v * hv_raw) || return false
        else
            c_cand_hi > 0.0 || return false
        end
        canc_hi = s_cand == 1 ? cancel_pos_hi : cancel_neg_hi
        hd_lo = s_cand == 1 ? _prevfloat_finite(h_lo - hv_hi) : _prevfloat_finite(h_lo + hv_lo)
        hd_hi = s_cand == 1 ? _nextfloat_finite(h_hi - hv_lo) : _nextfloat_finite(h_hi + hv_hi)
        hd_abs_lo = (hd_lo <= 0.0 && hd_hi >= 0.0) ? 0.0 : min(abs(hd_lo), abs(hd_hi))
        two_rad_lo = _prevfloat_finite(_prevfloat_finite(hd_abs_lo + _prevfloat_finite(rad_other_lo + rv_lo)) - _nextfloat_finite(2.0 * canc_hi))
        two_c_hi = _nextfloat_finite(2.0 * c_cand_hi)
        if isfinite(two_c_hi) && isfinite(two_rad_lo)
            strict_only ? (two_c_hi <= two_rad_lo && return false) : (two_c_hi < two_rad_lo && return false)
        end
        return true
    end
    coflip_possible = (sign === nothing && iszero(q_uv)) ?
        (_coflip_cand_possible(1) || _coflip_cand_possible(-1)) :
        _coflip_cand_possible(σ)
    lower_hi = _nextfloat_finite(center_hi - _prevfloat_finite(h_abs_lo + rad_other_lo))
    if isfinite(lower_hi) && lower_hi < 0.0
        best_u_hi = _nextfloat_finite(_nextfloat_finite(center_hi + h_abs_hi) - rad_other_lo)
        # Note: `:glk_pair` (line 960 and `_verify_relation_step` line 3172) requires
        # `center_exact > 0 && !iszero(h_u)` even when `sign` is explicitly supplied.
        glk_possible = !iszero(h_u_raw) && center_hi > 0.0 && !(isfinite(best_u_hi) && best_u_hi < 0.0)
        if glk_possible && has_summary
            h_u_pos = (direction * g_u >= 0) ? (h_u_raw > 0) : (h_u_raw < 0)
            σ_hu_pos = (σ == 1) ? h_u_pos : !h_u_pos
            m_v_req_hi = σ_hu_pos ?
                _nextfloat_finite(_nextfloat_finite(center_hi + hv_hi) - rad_v_other_lo) :
                _nextfloat_finite(_nextfloat_finite(center_hi - hv_lo) - rad_v_other_lo)
            if isfinite(m_v_req_hi) && m_v_req_hi < 0.0
                glk_possible = false
            end
        end
        (glk_possible || coflip_possible) || return (nothing, :not_strict, :interval, visits, 0, 0)
    end
    degree <= max_work - visits || return (nothing, :work_limit, :interval, visits, 0, 0)
    degree < max_exact_work || return (nothing, :verification_limit, :interval, visits, 0, 0)
    h_u = direction * g_u * h_u_raw
    rad_u_other = _Exact(0)
    center_exact = _Exact(0)
    exact_work = 1
    for (w, q) in st.adjacency[u]
        _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, 1, exact_work)
        visits += 1
        st.fixed[w] == 2 || continue
        g_w = map === nothing ? 1 : map.gauge[w]
        J_uw = direction * (g_u * g_w) * _spin_coupling(ws, q)
        if w == v
            center_exact = -σ * J_uw
        else
            rad_u_other += abs(J_uw)
        end
        exact_work += 1
    end
    _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, 1, exact_work)
    rad_exact = abs(h_u) + rad_u_other
    lower = center_exact - rad_exact
    upper = center_exact + rad_exact
    if lower > 0
        c_val = _mapped_constant(ws, map)
        step = RelationStep(u, v, σ, orig_σ, deepcopy(lower), deepcopy(upper), deepcopy(c_val),
                            predecessors, :exact, scope_length, :strong)
        return (step, :proved, :exact, visits, 1, exact_work)
    end
    weak_exact = allow_weak && lower >= 0
    deg_v = length(st.adjacency[v])
    v_budget_ok = !weak_exact || (deg_v <= max_work - visits && 1 + deg_v <= max_exact_work - exact_work)
    best_u = center_exact + abs(h_u) - rad_u_other
    glk_ok = v_budget_ok && center_exact > 0 && !iszero(h_u) && (best_u > 0 || (!weak_exact && allow_weak && best_u >= 0))
    coflip_ok = v_budget_ok && (weak_exact ?
        (center_exact > 0 && _coflip_cand_possible(σ; strict_only=true)) :
        (coflip_possible && (center_exact > 0 || (allow_weak && iszero(center_exact) && iszero(q_uv) && st.degrees[u] == st.degrees[v]))))
    err_method = :exact
    weak_glk = false
    lo_glk = _Exact(0)
    hi_glk = _Exact(0)
    weak_cf = false
    weak_cf_s = σ
    lo_cf_weak = _Exact(0)
    hi_cf_weak = _Exact(0)
    if glk_ok || coflip_ok
        err_method = glk_ok ? :glk_pair : :coflip_pair
        deg_v <= max_work - visits || return (nothing, :work_limit, err_method, visits, 1, exact_work)
        1 + deg_v <= max_exact_work - exact_work || return (nothing, :verification_limit, err_method, visits, 1, exact_work)
        h_v = direction * g_v * hv_raw
        exact_work += 1
        rad_v_other = _Exact(0)
        diff_pos = rad_u_other
        diff_neg = rad_u_other
        for (w, q) in st.adjacency[v]
            _expired(deadline_ns) && return (nothing, :deadline, err_method, visits, 1, exact_work)
            visits += 1
            st.fixed[w] == 2 || continue
            if w != u
                g_w = map === nothing ? 1 : map.gauge[w]
                J_vw = direction * (g_v * g_w) * _spin_coupling(ws, q)
                rad_v_other += abs(J_vw)
                if coflip_ok
                    pos_uw = get(st.adj_pos[u], w, 0)
                    q_uw = pos_uw == 0 ? _Exact(0) : st.adjacency[u][pos_uw].second
                    if !iszero(q_uw)
                        J_uw = direction * (g_u * g_w) * _spin_coupling(ws, q_uw)
                        diff_pos += abs(J_uw - J_vw) - abs(J_uw)
                        diff_neg += abs(J_uw + J_vw) - abs(J_uw)
                    else
                        diff_pos += abs(J_vw)
                        diff_neg += abs(J_vw)
                    end
                end
            end
            exact_work += 1
        end
        _expired(deadline_ns) && return (nothing, :deadline, err_method, visits, 1, exact_work)
        if glk_ok
            m_u_1 = center_exact - σ * h_u - rad_u_other
            m_u_2 = center_exact + σ * h_u - rad_u_other
            m_v_1 = center_exact + h_v - rad_v_other
            m_v_2 = center_exact - h_v - rad_v_other
            lo_a, hi_a = minmax(m_u_1, m_v_2)
            lo_b, hi_b = minmax(m_v_1, m_u_2)
            lo_glk, hi_glk = (lo_a > lo_b || (lo_a == lo_b && hi_a >= hi_b)) ? (lo_a, hi_a) : (lo_b, hi_b)
            if lo_glk > 0
                c_val = _mapped_constant(ws, map)
                step = RelationStep(u, v, σ, orig_σ, deepcopy(lo_glk), deepcopy(hi_glk), deepcopy(c_val),
                                    predecessors, :glk_pair, scope_length, :strong)
                return (step, :proved, :glk_pair, visits, 1, exact_work)
            elseif allow_weak && lo_glk >= 0
                weak_glk = true
            end
        end
        if coflip_ok
            cands_cf = (sign === nothing && iszero(q_uv)) ? (1, -1) : (σ,)
            for s_cf in cands_cf
                diff_cf = s_cf == 1 ? diff_pos : diff_neg
                rad_cf = (abs(h_u - s_cf * h_v) + diff_cf) // 2
                lo_cf = center_exact - rad_cf
                hi_cf = center_exact + rad_cf
                if lo_cf > 0
                    c_val = _mapped_constant(ws, map)
                    orig_s_cf = g_u * g_v * s_cf
                    step = RelationStep(u, v, s_cf, orig_s_cf, deepcopy(lo_cf), deepcopy(hi_cf), deepcopy(c_val),
                                        predecessors, :coflip_pair, scope_length, :strong)
                    return (step, :proved, :coflip_pair, visits, 1, exact_work)
                elseif allow_weak && lo_cf >= 0 && !weak_cf
                    weak_cf = true
                    weak_cf_s = s_cf
                    lo_cf_weak = lo_cf
                    hi_cf_weak = hi_cf
                end
            end
        end
    end
    if weak_exact
        c_val = _mapped_constant(ws, map)
        step = RelationStep(u, v, σ, orig_σ, deepcopy(lower), deepcopy(upper), deepcopy(c_val),
                            predecessors, :exact, scope_length, :weak)
        return (step, :proved, :exact, visits, 1, exact_work)
    elseif weak_glk
        c_val = _mapped_constant(ws, map)
        step = RelationStep(u, v, σ, orig_σ, deepcopy(lo_glk), deepcopy(hi_glk), deepcopy(c_val),
                            predecessors, :glk_pair, scope_length, :weak)
        return (step, :proved, :glk_pair, visits, 1, exact_work)
    elseif weak_cf
        c_val = _mapped_constant(ws, map)
        orig_s_cf = g_u * g_v * weak_cf_s
        step = RelationStep(u, v, weak_cf_s, orig_s_cf, deepcopy(lo_cf_weak), deepcopy(hi_cf_weak), deepcopy(c_val),
                            predecessors, :coflip_pair, scope_length, :weak)
        return (step, :proved, :coflip_pair, visits, 1, exact_work)
    end
    return (nothing, :not_strict, err_method, visits, 1, exact_work)
end

function _elimination_witness(ws::Workspace, u::Int;
                              map::Union{Nothing,DomainGaugeMap}=nothing,
                              tie_break::Symbol=:low,
                              max_degree=2,
                              max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing,
                              predecessors=0, scope_length=-1)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    max_degree isa Integer && !(max_degree isa Bool) && 0 <= max_degree <= 3 ||
        throw(ArgumentError("max_degree must be an integer between 0 and 3"))
    map === nothing || _validate_domain_map(ws, map)
    tie_break in (:low, :high) || throw(ArgumentError("tie_break must be :low or :high"))
    st, s = ws._state, ws._snapshot
    st.fixed[u] == 2 || return (nothing, :already_fixed, :none, 0, 0)
    direction = _direction(s)
    direction != 0 || return (nothing, :zero_scale, :none, 0, 0)
    adj_len = length(st.adjacency[u])
    adj_len <= max_work || return (nothing, :work_limit, :none, 0, 0)
    _expired(deadline_ns) && return (nothing, :deadline, :none, 0, 0)
    visits = 0
    free_edges = Pair{Int,_Exact}[]
    for (w, q) in st.adjacency[u]
        _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, 0)
        visits += 1
        if st.fixed[w] == 2 && !iszero(q)
            push!(free_edges, w => q)
        end
    end
    d = length(free_edges)
    d <= max_degree || return (nothing, :degree_too_high, :exact, visits, 0)
    sort!(free_edges; by=first)
    num_states = 1 << d
    num_states <= max_exact_work || return (nothing, :verification_limit, :exact, visits, 0)
    is_bool = s.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    tie_orig = if map === nothing
        tie_break === :low ? low_orig : 1
    else
        low_t = map.target_domain === :bool ? 0 : -1
        _lift_index_value(map, u, tie_break === :low ? low_t : 1)
    end
    neighbors = Tuple(p.first for p in free_edges)
    couplings = Tuple(p.second for p in free_edges)
    f_u = st.fields[u]
    phi = Vector{_Exact}(undef, num_states)
    tbl = Vector{Int}(undef, num_states)
    unique_argmin = true
    exact_work = 0
    for idx in 1:num_states
        _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, exact_work)
        exact_work += 1
        L_u = f_u
        for b in 1:d
            z_b = (((idx - 1) >> (b - 1)) & 1) == 1 ? 1 : low_orig
            L_u += couplings[b] * z_b
        end
        dir_L = direction * L_u
        if dir_L > 0
            tbl[idx] = low_orig
            phi[idx] = L_u * low_orig
        elseif dir_L < 0
            tbl[idx] = 1
            phi[idx] = L_u
        else
            unique_argmin = false
            tbl[idx] = tie_orig
            phi[idx] = _Exact(0)
        end
    end
    if d == 3
        alpha_123 = phi[8] - phi[4] - phi[6] - phi[7] + phi[2] + phi[3] + phi[5] - phi[1]
        iszero(alpha_123) || return (nothing, :nonquadratic_elimination, :exact, visits, exact_work)
    end
    alpha_0 = phi[1]
    alpha_lin = Vector{_Exact}(undef, d)
    for a in 1:d
        alpha_lin[a] = phi[1 + (1 << (a - 1))] - phi[1]
    end
    alpha_quad = fill(_Exact(0), d, d)
    for a in 1:d, b in (a + 1):d
        q_ab = phi[1 + (1 << (a - 1)) + (1 << (b - 1))] - phi[1 + (1 << (a - 1))] - phi[1 + (1 << (b - 1))] + phi[1]
        alpha_quad[a, b] = q_ab
        alpha_quad[b, a] = q_ab
    end
    if is_bool
        const_delta = alpha_0
        lin_deltas = Pair{Int,_Exact}[
            neighbors[a] => deepcopy(alpha_lin[a]) for a in 1:d if !iszero(alpha_lin[a])
        ]
        quad_deltas = Tuple{Int,Int,_Exact}[
            (neighbors[a], neighbors[b], deepcopy(alpha_quad[a, b]))
            for a in 1:d for b in (a + 1):d if !iszero(alpha_quad[a, b])
        ]
    else
        const_delta = alpha_0 + sum(alpha_lin; init=_Exact(0)) // 2 +
                      sum((alpha_quad[a, b] for a in 1:d for b in (a + 1):d); init=_Exact(0)) // 4
        lin_deltas = Pair{Int,_Exact}[]
        for a in 1:d
            df = alpha_lin[a] // 2 + sum((alpha_quad[a, b] for b in 1:d if b != a); init=_Exact(0)) // 4
            !iszero(df) && push!(lin_deltas, neighbors[a] => deepcopy(df))
        end
        quad_deltas = Tuple{Int,Int,_Exact}[
            (neighbors[a], neighbors[b], deepcopy(alpha_quad[a, b] // 4))
            for a in 1:d for b in (a + 1):d if !iszero(alpha_quad[a, b])
        ]
    end
    _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, exact_work)
    c_val = _mapped_constant(ws, map)
    step = EliminationStep(
        u,
        neighbors,
        Tuple(tbl),
        deepcopy(const_delta),
        Tuple(lin_deltas),
        Tuple(quad_deltas),
        deepcopy(c_val),
        predecessors,
        scope_length,
        unique_argmin,
    )
    return (step, :proved, :exact, visits, exact_work)
end

function _extract_witness_state(ws::Workspace, witness, map::Union{Nothing,DomainGaugeMap}=nothing)
    witness === nothing && return _coercive_field_witness_orig(ws; map)
    s, st = ws._snapshot, ws._state
    n = length(s.labels)
    is_bool = s.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    w = Vector{Int}(undef, n)
    if witness isa Reconstruction
        witness.generation == generation(ws) ||
            throw(ArgumentError("witness belongs to a different workspace generation"))
        length(witness.state) == n ||
            throw(ArgumentError("witness state must cover every original variable"))
        for idx in 1:n
            v = witness.state[idx]
            (v == low_orig || v == 1) ||
                throw(ArgumentError("witness value at index $idx is outside the original domain"))
            w[idx] = v
        end
    elseif witness isa AbstractVector
        Base.require_one_based_indexing(witness)
        length(witness) == n ||
            throw(ArgumentError("witness state must cover every original variable"))
        target_dom_sym = map === nothing ? _domain_symbol(s.domain) : map.target_domain
        for idx in 1:n
            v_mapped = _check_domain_scalar(witness[idx], target_dom_sym)
            w[idx] = map === nothing ? v_mapped : _lift_index_value(map, idx, v_mapped)
        end
    elseif witness isa AbstractDict
        length(witness) == n ||
            throw(ArgumentError("witness state must cover every original variable"))
        target_dom_sym = map === nothing ? _domain_symbol(s.domain) : map.target_domain
        for (idx, lbl) in enumerate(s.labels)
            haskey(witness, lbl) ||
                throw(ArgumentError("witness state is missing variable label $(repr(lbl))"))
            v_mapped = _check_domain_scalar(witness[lbl], target_dom_sym)
            w[idx] = map === nothing ? v_mapped : _lift_index_value(map, idx, v_mapped)
        end
    else
        throw(ArgumentError("witness must be a complete original-order vector, label dictionary, or Reconstruction"))
    end
    for pos in st.callers
        e = st.trail[pos]::_UndoFix
        w[e.index] == e.value ||
            throw(ArgumentError("witness violates current caller assumptions"))
    end
    for pos in st.fixes
        entry = st.trail[pos]
        entry.proof === nothing && continue
        pstep = entry.proof
        if pstep isa Union{DominanceStep,ProbingStep,RoofDualityStep,SubmodularCutStep}
            w[pstep.variable] == pstep.value ||
                throw(ArgumentError("witness violates committed workspace reduction"))
        elseif pstep isa MaxCutStep
            if pstep.representative == 0
                w[pstep.eliminated] == pstep.value ||
                    throw(ArgumentError("witness violates committed workspace reduction"))
            else
                s_u = is_bool ? (2 * w[pstep.eliminated] - 1) : w[pstep.eliminated]
                s_v = is_bool ? (2 * w[pstep.representative] - 1) : w[pstep.representative]
                s_u == pstep.orig_sign * s_v ||
                    throw(ArgumentError("witness violates committed workspace reduction"))
            end
        elseif pstep isa RelationStep
            s_u = is_bool ? (2 * w[pstep.eliminated] - 1) : w[pstep.eliminated]
            s_v = is_bool ? (2 * w[pstep.representative] - 1) : w[pstep.representative]
            s_u == pstep.orig_sign * s_v ||
                throw(ArgumentError("witness violates committed workspace reduction"))
        elseif pstep isa EliminationStep
            idx = 1
            for (bit_pos, nbr) in enumerate(pstep.neighbors)
                w[nbr] == 1 && (idx += 1 << (bit_pos - 1))
            end
            w[pstep.variable] == pstep.table[idx] ||
                throw(ArgumentError("witness violates committed workspace reduction"))
        end
    end
    return w
end

function _probing_witness(
    ws::Workspace,
    i::Int,
    witness;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    value=nothing,
    max_rounds=1,
    max_trial_fixes=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
    predecessors=0,
    scope_length=-1,
    _prevalidated_witness::Union{Nothing,Vector{Int}}=nothing,
    _w_energy_ref::Union{Nothing,Base.RefValue{Union{Nothing,_Exact}}}=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    _limits(max_rounds, nothing)
    _limits(max_trial_fixes, nothing)
    map === nothing || _validate_domain_map(ws, map)
    w_vec = _prevalidated_witness === nothing ? _extract_witness_state(ws, witness, map) : _prevalidated_witness
    st, s = ws._state, ws._snapshot
    req_orig = if value === nothing
        nothing
    elseif map === nothing
        _assignment(ws, value)
    else
        _lift_index_value(map, i, _check_domain_scalar(value, map.target_domain))
    end
    st.fixed[i] == 2 || return (nothing, :already_fixed, :none, 0, 0, 0)
    direction = _direction(s)
    direction != 0 || return (nothing, :zero_scale, :none, 0, 0, 0)
    _expired(deadline_ns) && return (nothing, :deadline, :none, 0, 0, 0)
    target_orig = req_orig === nothing ? w_vec[i] : req_orig
    low_orig = s.domain === QT.BoolDomain ? 0 : -1
    probed_orig = target_orig == 1 ? low_orig : 1
    n = length(s.labels)
    1 <= max_exact_work || return (nothing, :verification_limit, :none, 0, 0, 0)
    exact_work = 1
    visits = 0
    if _w_energy_ref !== nothing && _w_energy_ref[] !== nothing
        w_energy = _w_energy_ref[]::_Exact
    else
        w_energy = st.constant
        for u in 1:n
            st.fixed[u] == 2 || continue
            _expired(deadline_ns) && return (nothing, :deadline, :none, visits, 0, exact_work)
            exact_work < max_exact_work || return (nothing, :verification_limit, :none, visits, 0, exact_work)
            w_energy += st.fields[u] * w_vec[u]
            exact_work += 1
            for (v, q) in st.adjacency[u]
                _expired(deadline_ns) && return (nothing, :deadline, :none, visits, 0, exact_work)
                visits < max_work || return (nothing, :work_limit, :none, visits, 0, exact_work)
                visits += 1
                (st.fixed[v] == 2 && u < v) || continue
                exact_work < max_exact_work || return (nothing, :verification_limit, :none, visits, 0, exact_work)
                w_energy += q * (w_vec[u] * w_vec[v])
                exact_work += 1
            end
        end
        _w_energy_ref !== nothing && (_w_energy_ref[] = w_energy)
    end
    U_exact = direction * w_energy
    c_parent = deepcopy(_mapped_constant(ws, map))
    probe_cp = checkpoint(ws)
    saved_star_hint = st.star_hint
    saved_rel_hint = st.rel_hint
    fallbacks = 0
    try
        rep = _fix!(ws, i, probed_orig; proof=nothing, max_work=max_work - visits, deadline_ns=deadline_ns)
        visits += rep.edge_visits
        rep.stop_reason === :applied || return (nothing, rep.stop_reason, :none, visits, fallbacks, exact_work)
        branch_steps = DominanceStep[]
        trial_candidates = Int[j for (j, _) in st.adjacency[i] if st.fixed[j] == 2]
        for _ in 1:max_rounds
            isempty(trial_candidates) && break
            length(branch_steps) < max_trial_fixes || break
            next_candidates = Int[]
            next_seen = Set{Int}()
            for u in trial_candidates
                length(branch_steps) < max_trial_fixes || break
                st.fixed[u] == 2 || continue
                _expired(deadline_ns) && return (nothing, :deadline, :interval, visits, fallbacks, exact_work)
                if map === nothing && st.lower !== nothing && st.upper !== nothing
                    deg_u = length(st.adjacency[u])
                    if deg_u <= max_work - visits
                        lo_u, hi_u = direction > 0 ? (st.lower[u], st.upper[u]) : (-st.upper[u], -st.lower[u])
                        if !(lo_u > 0 || hi_u < 0)
                            _, lo_u_hi = _enclose(lo_u)
                            hi_u_lo, _ = _enclose(hi_u)
                            if isfinite(lo_u_hi) && isfinite(hi_u_lo) && lo_u_hi < 0.0 && hi_u_lo > 0.0
                                visits += deg_u
                                continue
                            end
                        end
                    end
                end
                b_step, b_reason, b_method, b_visits, b_fb, b_exact = _dominance_witness(
                    ws, u; map=map, allow_weak=false,
                    max_work=max_work - visits, max_exact_work=max_exact_work - exact_work,
                    deadline_ns=deadline_ns, predecessors=length(branch_steps), scope_length=scope_length,
                )
                visits += b_visits
                fallbacks += b_fb
                exact_work += b_exact
                if b_reason in (:deadline, :work_limit, :verification_limit)
                    return (nothing, b_reason, b_method === :none ? :interval : b_method, visits, fallbacks, exact_work)
                end
                if b_step !== nothing
                    f_rep = _fix!(ws, u, b_step.value; proof=b_step, max_work=max_work - visits, deadline_ns=deadline_ns)
                    visits += f_rep.edge_visits
                    f_rep.stop_reason === :applied ||
                        return (nothing, f_rep.stop_reason, b_method, visits, fallbacks, exact_work)
                    push!(branch_steps, b_step)
                    for (w_nbr, _) in st.adjacency[u]
                        if st.fixed[w_nbr] == 2 && !(w_nbr in next_seen)
                            push!(next_candidates, w_nbr)
                            push!(next_seen, w_nbr)
                        end
                    end
                end
            end
            trial_candidates = next_candidates
        end
        c_spin = _spin_constant(ws)
        c_bpos = _bool_constant(ws)
        cs_lo, cs_hi = _enclose(c_spin)
        cb_lo, cb_hi = _enclose(c_bpos)
        lo_spin, hi_spin = direction >= 0 ? (cs_lo, cs_hi) : (-cs_hi, -cs_lo)
        lo_bpos, hi_bpos = direction >= 0 ? (cb_lo, cb_hi) : (-cb_hi, -cb_lo)
        lo_bneg, hi_bneg = lo_bpos, hi_bpos
        is_spin_dom = s.domain === QT.SpinDomain
        total_active_adj = 0
        if st.lower !== nothing && st.upper !== nothing
            @inbounds for u in 1:n
                st.fixed[u] == 2 && (total_active_adj += length(st.adjacency[u]))
            end
        end
        use_vertex_sums = st.lower !== nothing && st.upper !== nothing &&
                          total_active_adj <= max_work - visits
        for u in 1:n
            st.fixed[u] == 2 || continue
            _expired(deadline_ns) && return (nothing, :deadline, :interval, visits, fallbacks, exact_work)
            h_u = _spin_field(ws, u)
            f_u = _bool_field(ws, u)
            hu_lo, hu_hi = _enclose(h_u)
            fu_lo, fu_hi = _enclose(f_u)
            h_lo, h_hi = direction >= 0 ? (hu_lo, hu_hi) : (-hu_hi, -hu_lo)
            f_lo, f_hi = direction >= 0 ? (fu_lo, fu_hi) : (-fu_hi, -fu_lo)
            m_h = _max_nan(abs(h_lo), abs(h_hi))
            m_h_lo = _max_nan(0.0, _max_nan(h_lo, -h_hi))
            lo_spin = _prevfloat_finite(lo_spin - m_h)
            hi_spin = _nextfloat_finite(hi_spin - m_h_lo)
            lo_bpos = _prevfloat_finite(lo_bpos + _min_nan(0.0, f_lo))
            hi_bpos = _nextfloat_finite(hi_bpos + _min_nan(0.0, f_hi))
            two_h_lo = _prevfloat_finite(2.0 * h_lo)
            two_h_hi = _nextfloat_finite(2.0 * h_hi)
            term_x0 = two_h_lo
            term_x1 = _prevfloat_finite(f_lo - two_h_hi)
            lo_bneg = _prevfloat_finite(lo_bneg + _min_nan(term_x0, term_x1))
            term_x0_hi = two_h_hi
            term_x1_hi = _nextfloat_finite(f_hi - two_h_lo)
            hi_bneg = _nextfloat_finite(hi_bneg + _min_nan(term_x0_hi, term_x1_hi))
            if use_vertex_sums
                visits += length(st.adjacency[u])
                if st.degrees[u] > 0
                    up_lo, up_hi = _enclose(st.upper[u])
                    lo_lo, lo_hi = _enclose(st.lower[u])
                    fld_lo, fld_hi = _enclose(st.fields[u])
                    diff_lo = _max_nan(0.0, _prevfloat_finite(up_lo - lo_hi))
                    diff_hi = _max_nan(0.0, _nextfloat_finite(up_hi - lo_lo))
                    if !is_spin_dom
                        m_j_hi = _nextfloat_finite(0.125 * diff_hi)
                        m_j_lo = _prevfloat_finite(0.125 * diff_lo)
                        neg_qb_lo = direction >= 0 ? _min_nan(0.0, _prevfloat_finite(lo_lo - fld_hi)) : _min_nan(0.0, _prevfloat_finite(fld_lo - up_hi))
                        neg_qb_hi = direction >= 0 ? _min_nan(0.0, _nextfloat_finite(lo_hi - fld_lo)) : _min_nan(0.0, _nextfloat_finite(fld_hi - up_lo))
                        add_qb = _prevfloat_finite(0.5 * neg_qb_lo)
                        add_qb_hi = _nextfloat_finite(0.5 * neg_qb_hi)
                    else
                        df_lo, df_hi = _enclose(st.dual_fields[u])
                        m_j_hi = _nextfloat_finite(0.25 * diff_hi)
                        m_j_lo = _prevfloat_finite(0.25 * diff_lo)
                        two_fld_lo = _prevfloat_finite(2.0 * fld_lo)
                        two_fld_hi = _nextfloat_finite(2.0 * fld_hi)
                        two_csum_lo = _prevfloat_finite(two_fld_lo - df_hi)
                        two_csum_hi = _nextfloat_finite(two_fld_hi - df_lo)
                        dir_two_csum_lo = direction >= 0 ? two_csum_lo : -two_csum_hi
                        dir_two_csum_hi = direction >= 0 ? two_csum_hi : -two_csum_lo
                        add_qb = _min_nan(0.0, _prevfloat_finite(0.5 * _prevfloat_finite(dir_two_csum_lo - diff_hi)))
                        add_qb_hi = _min_nan(0.0, _nextfloat_finite(0.5 * _nextfloat_finite(dir_two_csum_hi - diff_lo)))
                    end
                    lo_spin = _prevfloat_finite(lo_spin - m_j_hi)
                    hi_spin = _nextfloat_finite(hi_spin - m_j_lo)
                    lo_bpos = _prevfloat_finite(lo_bpos + add_qb)
                    hi_bpos = _nextfloat_finite(hi_bpos + add_qb_hi)
                    lo_bneg = _prevfloat_finite(lo_bneg + add_qb)
                    hi_bneg = _nextfloat_finite(hi_bneg + add_qb_hi)
                end
            else
                for (v, q) in st.adjacency[u]
                    _expired(deadline_ns) && return (nothing, :deadline, :interval, visits, fallbacks, exact_work)
                    visits < max_work || return (nothing, :work_limit, :interval, visits, fallbacks, exact_work)
                    visits += 1
                    (st.fixed[v] == 2 && u < v) || continue
                    q_lo, q_hi = _enclose(q)
                    c_lo, c_hi = direction >= 0 ? (q_lo, q_hi) : (-q_hi, -q_lo)
                    if is_spin_dom
                        j_lo, j_hi = c_lo, c_hi
                        qb_lo, qb_hi = _prevfloat_finite(4.0 * c_lo), _nextfloat_finite(4.0 * c_hi)
                    else
                        qb_lo, qb_hi = c_lo, c_hi
                        j_lo, j_hi = _prevfloat_finite(0.25 * c_lo), _nextfloat_finite(0.25 * c_hi)
                    end
                    m_j = _max_nan(abs(j_lo), abs(j_hi))
                    m_j_lo = _max_nan(0.0, _max_nan(j_lo, -j_hi))
                    lo_spin = _prevfloat_finite(lo_spin - m_j)
                    hi_spin = _nextfloat_finite(hi_spin - m_j_lo)
                    add_qb = _min_nan(0.0, qb_lo)
                    add_qb_hi = _min_nan(0.0, qb_hi)
                    lo_bpos = _prevfloat_finite(lo_bpos + add_qb)
                    hi_bpos = _nextfloat_finite(hi_bpos + add_qb_hi)
                    lo_bneg = _prevfloat_finite(lo_bneg + add_qb)
                    hi_bneg = _nextfloat_finite(hi_bneg + add_qb_hi)
                end
            end
        end
        _expired(deadline_ns) && return (nothing, :deadline, :interval, visits, fallbacks, exact_work)
        if isfinite(lo_spin) && isfinite(lo_bpos) && isfinite(lo_bneg)
            lo_float = max(lo_spin, lo_bpos, lo_bneg)
            L_int = _Exact(lo_float)
            if L_int > U_exact
                step = ProbingStep(
                    i, target_orig, probed_orig,
                    deepcopy(L_int), deepcopy(U_exact),
                    Tuple(w_vec), Tuple(branch_steps),
                    c_parent, predecessors, :interval, scope_length, :strong,
                )
                return (step, :proved, :interval, visits, fallbacks, exact_work)
            end
        end
        if isfinite(hi_spin) && isfinite(hi_bpos) && isfinite(hi_bneg)
            hi_float = max(hi_spin, hi_bpos, hi_bneg)
            if _Exact(hi_float) <= U_exact
                return (nothing, :not_strict, :interval, visits, fallbacks, exact_work)
            end
        end
        2 * st.active_edges <= max_work - visits ||
            return (nothing, :work_limit, :interval, visits, fallbacks, exact_work)
        active_verts = count(==(2), st.fixed)
        needed_exact = 1 + active_verts + st.active_edges
        needed_exact <= max_exact_work - exact_work ||
            return (nothing, :verification_limit, :interval, visits, fallbacks, exact_work)
        fallbacks += 1
        exact_work += 1
        L_spin = direction * c_spin
        L_bpos = direction * c_bpos
        L_bneg = direction * c_bpos
        if st.lower !== nothing && st.upper !== nothing && total_active_adj <= max_work - visits
            sum_diff = _Exact(0)
            sum_neg_qb2 = _Exact(0)
            edge_deg_sum = 0
            for u in 1:n
                st.fixed[u] == 2 || continue
                _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, fallbacks, exact_work + (edge_deg_sum ÷ 2))
                h_u = direction * _spin_field(ws, u)
                f_u = direction * _bool_field(ws, u)
                L_spin -= abs(h_u)
                L_bpos += min(_Exact(0), f_u)
                L_bneg += min(2 * h_u, f_u - 2 * h_u)
                diff_u = st.upper[u] - st.lower[u]
                sum_diff += diff_u
                if !is_spin_dom
                    sum_neg_qb2 += direction > 0 ? (st.lower[u] - st.fields[u]) : (st.fields[u] - st.upper[u])
                else
                    sum_neg_qb2 += direction * (2 * st.fields[u] - st.dual_fields[u]) - diff_u
                end
                visits += length(st.adjacency[u])
                exact_work += 1
                edge_deg_sum += st.degrees[u]
            end
            exact_work += st.active_edges
            L_spin -= is_spin_dom ? (sum_diff // 4) : (sum_diff // 8)
            add_qb_tot = sum_neg_qb2 // 2
            L_bpos += add_qb_tot
            L_bneg += add_qb_tot
        else
            for u in 1:n
                st.fixed[u] == 2 || continue
                _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, fallbacks, exact_work)
                h_u = direction * _spin_field(ws, u)
                f_u = direction * _bool_field(ws, u)
                L_spin -= abs(h_u)
                L_bpos += min(_Exact(0), f_u)
                L_bneg += min(2 * h_u, f_u - 2 * h_u)
                exact_work += 1
                for (v, q) in st.adjacency[u]
                    _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, fallbacks, exact_work)
                    visits += 1
                    (st.fixed[v] == 2 && u < v) || continue
                    J_uv = direction * _spin_coupling(ws, q)
                    qb_uv = direction * _bool_coupling(ws, q)
                    L_spin -= abs(J_uv)
                    add_qb = min(_Exact(0), qb_uv)
                    L_bpos += add_qb
                    L_bneg += add_qb
                    exact_work += 1
                end
            end
        end
        _expired(deadline_ns) && return (nothing, :deadline, :exact, visits, fallbacks, exact_work)
        L_exact = max(L_spin, L_bpos, L_bneg)
        if L_exact > U_exact
            step = ProbingStep(
                i, target_orig, probed_orig,
                deepcopy(L_exact), deepcopy(U_exact),
                Tuple(w_vec), Tuple(branch_steps),
                c_parent, predecessors, :exact, scope_length, :strong,
            )
            return (step, :proved, :exact, visits, fallbacks, exact_work)
        else
            return (nothing, :not_strict, :exact, visits, fallbacks, exact_work)
        end
    finally
        if length(st.trail) > probe_cp._depth
            rollback!(ws, probe_cp)
        end
        st.star_hint = saved_star_hint
        st.rel_hint = saved_rel_hint
    end
end

function _convert_step_bounds(s::_Snapshot, step::DominanceStep,
                              from_map::Union{Nothing,DomainGaugeMap},
                              to_map::Union{Nothing,DomainGaugeMap})
    i = step.variable
    from_dom = from_map === nothing ? _domain_symbol(s.domain) : from_map.target_domain
    from_g = from_map === nothing ? 1 : from_map.gauge[i]
    lo_g = from_dom === :bool ? (step.lower // 2) : step.lower
    hi_g = from_dom === :bool ? (step.upper // 2) : step.upper
    lo_spin, hi_spin = from_g == 1 ? (lo_g, hi_g) : (-hi_g, -lo_g)
    to_dom = to_map === nothing ? _domain_symbol(s.domain) : to_map.target_domain
    to_g = to_map === nothing ? 1 : to_map.gauge[i]
    lo_to_g, hi_to_g = to_g == 1 ? (lo_spin, hi_spin) : (-hi_spin, -lo_spin)
    new_lo = to_dom === :bool ? (2 * lo_to_g) : lo_to_g
    new_hi = to_dom === :bool ? (2 * hi_to_g) : hi_to_g
    return deepcopy(new_lo), deepcopy(new_hi)
end

mutable struct _PolyState
    n::Int
    domain::QT.Domain
    sense::QT.Sense
    scale::Float64
    active::BitVector
    fields::Vector{_Exact}
    adj::Vector{Vector{Pair{Int,_Exact}}}
    adj_pos::Vector{Dict{Int,Int}}
    constant::_Exact
    h_spin::Vector{_Exact}
    c_spin::_Exact
    c_gauged_bool::_Exact
    map::Union{Nothing,DomainGaugeMap}
end

function _init_poly_state(s::_Snapshot; map::Union{Nothing,DomainGaugeMap}=nothing, deadline=nothing)
    n = length(s.labels)
    fields = fill(_Exact(0), n)
    adj = [Pair{Int,_Exact}[] for _ in 1:n]
    adj_pos = [Dict{Int,Int}() for _ in 1:n]
    f = QT.Form{Float64}(n, _thaw(s.linear), _thaw(s.quadratic), s.scale, s.offset;
                         sense=s.sense, domain=s.domain)
    for (i, v) in QT.linear_terms(f)
        _expired(deadline) && return nothing
        fields[i] = _Exact(v)
    end
    quad_sum = _Exact(0)
    for ((i, j), v) in QT.quadratic_terms(f)
        _expired(deadline) && return nothing
        iszero(v) && continue
        q = _Exact(v)
        push!(adj[i], j => q)
        adj_pos[i][j] = length(adj[i])
        push!(adj[j], i => q)
        adj_pos[j][i] = length(adj[j])
        quad_sum += q
    end
    constant = _Exact(s.offset)
    is_bool = s.domain === QT.BoolDomain
    h_spin = Vector{_Exact}(undef, n)
    if is_bool
        for i in 1:n
            csum = sum((q for (_, q) in adj[i]); init=_Exact(0))
            h_spin[i] = fields[i] // 2 + csum // 4
        end
        c_spin = constant + sum(fields; init=_Exact(0)) // 2 + quad_sum // 4
    else
        copyto!(h_spin, fields)
        c_spin = constant
    end
    c_gauged_bool = c_spin
    if map !== nothing && map.target_domain === :bool
        g = map.gauge
        for i in 1:n
            c_gauged_bool -= g[i] * h_spin[i]
            for (j, q) in adj[i]
                i < j || continue
                J_ij = is_bool ? (q // 4) : q
                c_gauged_bool += (g[i] * g[j]) * J_ij
            end
        end
    end
    return _PolyState(n, s.domain, s.sense, s.scale, trues(n), fields, adj, adj_pos, constant,
                      h_spin, c_spin, c_gauged_bool, map)
end

_direction_poly(p::_PolyState) = iszero(p.scale) ? 0 :
    (p.sense === QT.Min ? 1 : -1) * (signbit(p.scale) ? -1 : 1)

function _poly_fix!(p::_PolyState, i::Int, v::Int)
    is_bool = p.domain === QT.BoolDomain
    s_i = is_bool ? (2 * v - 1) : v
    if p.map !== nothing && p.map.target_domain === :bool
        u_i = _map_index_value(p.map, i, v)
        if u_i != 0
            g = p.map.gauge
            g_i = g[i]
            csum = _Exact(0)
            for (j, q) in p.adj[i]
                p.active[j] || continue
                J_ij = is_bool ? (q // 4) : q
                csum += (g_i * g[j]) * J_ij
            end
            p.c_gauged_bool += (2 * g_i * p.h_spin[i] - 2 * csum) * u_i
        end
    end
    p.constant += p.fields[i] * v
    p.c_spin += p.h_spin[i] * s_i
    for (j, q) in p.adj[i]
        p.active[j] || continue
        p.fields[j] += q * v
        J_ij = is_bool ? (q // 4) : q
        p.h_spin[j] += J_ij * s_i
    end
    p.active[i] = false
    return nothing
end

function _poly_apply_deltas!(p::_PolyState, u::Int, const_delta::_Exact, field_deltas, quad_deltas)
    is_bool = p.domain === QT.BoolDomain
    u_active_edges = Pair{Int,_Exact}[]
    touched = Int[]
    touched_seen = Set{Int}()
    for (w, q) in p.adj[u]
        p.active[w] || continue
        push!(u_active_edges, w => q)
        _touch!(touched, touched_seen, w)
    end
    for (w, df) in field_deltas
        iszero(df) && continue
        _touch!(touched, touched_seen, w)
    end
    merged_q = Dict{Tuple{Int,Int},_Exact}()
    merged_order = Tuple{Int,Int}[]
    for (a, b, dq) in quad_deltas
        iszero(dq) && continue
        j, k = min(a, b), max(a, b)
        !haskey(merged_q, (j, k)) && push!(merged_order, (j, k))
        merged_q[(j, k)] = get(merged_q, (j, k), _Exact(0)) + dq
        _touch!(touched, touched_seen, j)
        _touch!(touched, touched_seen, k)
    end
    f_map = Dict{Int,_Exact}(w => _Exact(0) for w in touched)
    qsum_map = Dict{Int,_Exact}(w => _Exact(0) for w in touched)
    for (w, q_uw) in u_active_edges
        qsum_map[w] -= q_uw
    end
    for (w, df) in field_deltas
        iszero(df) && continue
        f_map[w] += df
    end
    for (j, k) in merged_order
        dq = merged_q[(j, k)]
        iszero(dq) && continue
        qsum_map[j] += dq
        qsum_map[k] += dq
    end
    old_f_u = p.fields[u]
    old_h_u = p.h_spin[u]
    total_f_delta = -old_f_u + sum(values(f_map); init=_Exact(0))
    total_q_delta = -sum((q for (_, q) in u_active_edges); init=_Exact(0)) +
                    sum((merged_q[jk] for jk in merged_order); init=_Exact(0))
    dc_spin = is_bool ? (const_delta + total_f_delta // 2 + total_q_delta // 4) : const_delta
    p.constant += const_delta
    p.c_spin += dc_spin
    if p.map !== nothing && p.map.target_domain === :bool
        g = p.map.gauge
        dc_gb = dc_spin + g[u] * old_h_u
        for w in touched
            dh_w = is_bool ? (f_map[w] // 2 + qsum_map[w] // 4) : f_map[w]
            dc_gb -= g[w] * dh_w
        end
        for (w, q_uw) in u_active_edges
            J_uw = is_bool ? (q_uw // 4) : q_uw
            dc_gb -= (g[u] * g[w]) * J_uw
        end
        for (j, k) in merged_order
            dq = merged_q[(j, k)]
            iszero(dq) && continue
            dJ_jk = is_bool ? (dq // 4) : dq
            dc_gb += (g[j] * g[k]) * dJ_jk
        end
        p.c_gauged_bool += dc_gb
    end
    for w in touched
        p.fields[w] += f_map[w]
        p.h_spin[w] += is_bool ? (f_map[w] // 2 + qsum_map[w] // 4) : f_map[w]
    end
    for (w, _) in u_active_edges
        pos_w = get(p.adj_pos[w], u, 0)
        if pos_w != 0
            last_pos = length(p.adj[w])
            if pos_w != last_pos
                tail_pair = p.adj[w][last_pos]
                p.adj[w][pos_w] = tail_pair
                p.adj_pos[w][tail_pair.first] = pos_w
            end
            pop!(p.adj[w])
            delete!(p.adj_pos[w], u)
        end
    end
    for (j, k) in merged_order
        dq = merged_q[(j, k)]
        iszero(dq) && continue
        for (a, b) in ((j, k), (k, j))
            pos = get(p.adj_pos[a], b, 0)
            if pos == 0
                push!(p.adj[a], b => dq)
                p.adj_pos[a][b] = length(p.adj[a])
            else
                q_new = p.adj[a][pos].second + dq
                if iszero(q_new)
                    last_pos = length(p.adj[a])
                    if pos != last_pos
                        tail_pair = p.adj[a][last_pos]
                        p.adj[a][pos] = tail_pair
                        p.adj_pos[a][tail_pair.first] = pos
                    end
                    pop!(p.adj[a])
                    delete!(p.adj_pos[a], b)
                else
                    p.adj[a][pos] = b => q_new
                end
            end
        end
    end
    p.active[u] = false
    return nothing
end

function _poly_relation_deltas(p::_PolyState, u::Int, v::Int, orig_σ::Int)
    f_u = p.fields[u]
    q_uv = _Exact(0)
    other_edges = Pair{Int,_Exact}[]
    for (w, q) in p.adj[u]
        p.active[w] || continue
        if w == v
            q_uv = q
        else
            push!(other_edges, w => q)
        end
    end
    if p.domain === QT.SpinDomain
        const_delta = orig_σ * q_uv
        field_deltas = Pair{Int,_Exact}[v => orig_σ * f_u]
        quad_deltas = Tuple{Int,Int,_Exact}[
            (min(v, w), max(v, w), orig_σ * q) for (w, q) in other_edges
        ]
        return const_delta, field_deltas, quad_deltas
    elseif orig_σ == 1
        const_delta = _Exact(0)
        field_deltas = Pair{Int,_Exact}[v => (f_u + q_uv)]
        quad_deltas = Tuple{Int,Int,_Exact}[
            (min(v, w), max(v, w), q) for (w, q) in other_edges
        ]
        return const_delta, field_deltas, quad_deltas
    else
        const_delta = f_u
        field_deltas = Pair{Int,_Exact}[v => -f_u]
        for (w, q) in other_edges
            push!(field_deltas, w => q)
        end
        quad_deltas = Tuple{Int,Int,_Exact}[
            (min(v, w), max(v, w), -q) for (w, q) in other_edges
        ]
        return const_delta, field_deltas, quad_deltas
    end
end

function _poly_mapped_constant(p::_PolyState, active_map::Union{Nothing,DomainGaugeMap})
    active_map === nothing && return p.constant
    return active_map.target_domain === :spin ? p.c_spin : p.c_gauged_bool
end

function _poly_marginal_diff(p::_PolyState, i::Int, active_map::Union{Nothing,DomainGaugeMap}, deadline=nothing)
    comp = Int[i]
    head = 1
    while head <= length(comp)
        u = comp[head]
        head += 1
        for (w, q) in p.adj[u]
            _expired(deadline) && return (false, :deadline, Int[], _Exact(0))
            (p.active[w] && !iszero(q)) || continue
            if !(w in comp)
                length(comp) < _MAX_MARGINAL_COMPONENT || return (false, :invalid_bound, comp, _Exact(0))
                push!(comp, w)
            end
        end
    end
    others = sort!(comp[2:end])
    d_c = length(others)
    all_nodes = vcat(i, others)
    sub_edges = Tuple{Int,Int,_Exact}[]
    for a in 1:length(all_nodes)
        u = all_nodes[a]
        for (w, q) in p.adj[u]
            (p.active[w] && u < w && !iszero(q)) || continue
            b = findfirst(==(w), all_nodes)
            b !== nothing && push!(sub_edges, (a, b, q))
        end
    end
    direction = _direction_poly(p)
    low_orig = p.domain === QT.BoolDomain ? 0 : -1
    best_orig = Dict{Int,_Exact}()
    vals = Vector{Int}(undef, length(all_nodes))
    for x_i in (low_orig, 1)
        vals[1] = x_i
        best_val = _Exact(0)
        has_best = false
        for mask in 0:((1 << d_c) - 1)
            _expired(deadline) && return (false, :deadline, comp, _Exact(0))
            for b in 1:d_c
                vals[b + 1] = ((mask >> (b - 1)) & 1) == 1 ? 1 : low_orig
            end
            e = _Exact(0)
            for a in 1:length(all_nodes)
                e += p.fields[all_nodes[a]] * vals[a]
            end
            for (a, b, q) in sub_edges
                e += q * vals[a] * vals[b]
            end
            de = direction * e
            if !has_best || de < best_val
                best_val = de
                has_best = true
            end
        end
        best_orig[x_i] = best_val
    end
    target_dom = active_map === nothing ? p.domain : _qt_domain(active_map.target_domain)
    low_target = target_dom === QT.BoolDomain ? 0 : -1
    orig_at_low = active_map === nothing ? low_orig : _lift_index_value(active_map, i, low_target)
    orig_at_high = active_map === nothing ? 1 : _lift_index_value(active_map, i, 1)
    return (true, :verified, comp, best_orig[orig_at_high] - best_orig[orig_at_low])
end

function _transport_one_step(
    s::_Snapshot,
    p::_PolyState,
    step::_ProofRecord,
    from_map::Union{Nothing,DomainGaugeMap},
    to_map::Union{Nothing,DomainGaugeMap};
    already_in_target::Bool=false,
)
    c_to = _poly_mapped_constant(p, to_map)
    if step isa DominanceStep
        if already_in_target
            new_lo, new_hi = step.lower, step.upper
        elseif step.method === :marginal
            from_g = from_map === nothing ? 1 : from_map.gauge[step.variable]
            to_g = to_map === nothing ? 1 : to_map.gauge[step.variable]
            delta_marg = (from_g * to_g) * step.lower
            new_lo, new_hi = deepcopy(delta_marg), deepcopy(delta_marg)
        else
            new_lo, new_hi = _convert_step_bounds(s, step, from_map, to_map)
        end
        out = DominanceStep(
            step.variable, step.value, new_lo, new_hi, deepcopy(c_to),
            step.predecessors, step.method, step.scope_length, step.persistency,
        )
        _poly_fix!(p, step.variable, step.value)
        return out
    elseif step isa RelationStep
        new_sign = already_in_target ? step.sign : (to_map === nothing ? step.orig_sign :
            (to_map.gauge[step.eliminated] * to_map.gauge[step.representative] * step.orig_sign))
        out = RelationStep(
            step.eliminated, step.representative, new_sign, step.orig_sign,
            deepcopy(step.lower), deepcopy(step.upper), deepcopy(c_to),
            step.predecessors, step.method, step.scope_length, step.persistency,
        )
        cd, fd, qd = _poly_relation_deltas(p, step.eliminated, step.representative, step.orig_sign)
        _poly_apply_deltas!(p, step.eliminated, cd, fd, qd)
        return out
    elseif step isa ProbingStep
        pstep = step::ProbingStep
        new_bsteps = if already_in_target
            _deepcopy_tuple(pstep.branch_steps, IdDict())
        else
            p_trial = deepcopy(p)
            _poly_fix!(p_trial, pstep.variable, pstep.probed_value)
            Tuple(
                _transport_one_step(s, p_trial, bstep, from_map, to_map; already_in_target=false)
                for bstep in pstep.branch_steps
            )
        end
        out = ProbingStep(
            pstep.variable, pstep.value, pstep.probed_value,
            deepcopy(pstep.branch_lower), deepcopy(pstep.witness_upper),
            pstep.witness_state, new_bsteps, deepcopy(c_to),
            pstep.predecessors, pstep.method, pstep.scope_length, pstep.persistency,
        )
        _poly_fix!(p, pstep.variable, pstep.value)
        return out
    elseif step isa RoofDualityStep
        rstep = step::RoofDualityStep
        out = RoofDualityStep(
            rstep.variable, rstep.value,
            deepcopy(rstep.roof_lower), deepcopy(rstep.max_flow),
            rstep.flow_edges, rstep.batch_fixings, rstep.batch_index,
            deepcopy(c_to), rstep.predecessors, rstep.method,
            rstep.scope_length, rstep.persistency,
        )
        _poly_fix!(p, rstep.variable, rstep.value)
        return out
    elseif step isa SubmodularCutStep
        sstep = step::SubmodularCutStep
        out = SubmodularCutStep(
            sstep.variable, sstep.value,
            sstep.component_variables, sstep.gauge,
            deepcopy(sstep.component_opt), deepcopy(sstep.max_flow),
            sstep.flow_edges, sstep.batch_fixings, sstep.batch_index,
            deepcopy(c_to), sstep.predecessors, sstep.method,
            sstep.scope_length, sstep.persistency,
        )
        _poly_fix!(p, sstep.variable, sstep.value)
        return out
    elseif step isa MaxCutStep
        mstep = step::MaxCutStep
        if mstep.representative == 0
            new_sign = already_in_target ? mstep.sign : (to_map === nothing ? mstep.orig_sign :
                (to_map.gauge[mstep.eliminated] * mstep.orig_sign))
            out = MaxCutStep(
                mstep.eliminated, 0, mstep.anchor, new_sign, mstep.orig_sign, mstep.value,
                deepcopy(mstep.margin), deepcopy(mstep.direct_weight),
                deepcopy(mstep.non_triangle_slack), _deepcopy_tuple(mstep.triangles, IdDict()),
                deepcopy(c_to), mstep.predecessors, mstep.method,
                mstep.scope_length, mstep.persistency,
            )
            _poly_fix!(p, mstep.eliminated, mstep.value)
            return out
        else
            new_sign = already_in_target ? mstep.sign : (to_map === nothing ? mstep.orig_sign :
                (to_map.gauge[mstep.eliminated] * to_map.gauge[mstep.representative] * mstep.orig_sign))
            out = MaxCutStep(
                mstep.eliminated, mstep.representative, mstep.anchor, new_sign, mstep.orig_sign, 0,
                deepcopy(mstep.margin), deepcopy(mstep.direct_weight),
                deepcopy(mstep.non_triangle_slack), _deepcopy_tuple(mstep.triangles, IdDict()),
                deepcopy(c_to), mstep.predecessors, mstep.method,
                mstep.scope_length, mstep.persistency,
            )
            cd, fd, qd = _poly_relation_deltas(p, mstep.eliminated, mstep.representative, mstep.orig_sign)
            _poly_apply_deltas!(p, mstep.eliminated, cd, fd, qd)
            return out
        end
    else
        estep = step::EliminationStep
        out = EliminationStep(
            estep.variable, estep.neighbors, estep.table,
            deepcopy(estep.constant_delta), _deepcopy_tuple(estep.linear_deltas, IdDict()), _deepcopy_tuple(estep.quadratic_deltas, IdDict()),
            deepcopy(c_to), estep.predecessors, estep.scope_length, estep.unique_argmin,
        )
        _poly_apply_deltas!(p, estep.variable, estep.constant_delta, estep.linear_deltas, estep.quadratic_deltas)
        return out
    end
end

function _transport_steps(ws::Workspace, assumptions::Tuple, steps::Tuple,
                          from_map::Union{Nothing,DomainGaugeMap},
                          to_map::Union{Nothing,DomainGaugeMap};
                          tail_step::Union{Nothing,_ProofRecord}=nothing)
    (isempty(steps) && tail_step === nothing) && return ()
    s = ws._snapshot
    p = _init_poly_state(s; map=to_map)
    introduced = 0
    total_len = length(steps) + (tail_step === nothing ? 0 : 1)
    out = Vector{_ProofRecord}(undef, total_len)
    for (k, step) in enumerate(steps)
        count = step.scope_length == -1 ? length(assumptions) : step.scope_length
        for pos in (introduced + 1):count
            idx, val = assumptions[pos]
            _poly_fix!(p, idx, val)
        end
        introduced = count
        out[k] = _transport_one_step(s, p, step, from_map, to_map; already_in_target=false)
    end
    if tail_step !== nothing
        count = tail_step.scope_length == -1 ? length(assumptions) : tail_step.scope_length
        for pos in (introduced + 1):count
            idx, val = assumptions[pos]
            _poly_fix!(p, idx, val)
        end
        out[total_len] = _transport_one_step(s, p, tail_step, to_map, to_map; already_in_target=true)
    end
    return Tuple(out)
end

function _build_proof_certificate(ws::Workspace, step::_ProofRecord,
                                  map::Union{Nothing,DomainGaugeMap}, deadline_ns)
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, source.labels)
    owned_map = map === nothing ? nothing : deepcopy(map)
    raw_vec = _ProofRecord[deepcopy(ws._state.trail[p].proof) for p in ws._state.fixes
                           if ws._state.trail[p].proof !== nothing]
    steps = if owned_map === nothing
        push!(raw_vec, step)
        Tuple(raw_vec)
    else
        _transport_steps(ws, _caller_scope(ws), Tuple(raw_vec), nothing, owned_map; tail_step=step)
    end
    _expired(deadline_ns) && return nothing
    return DominanceCertificate(generation(ws), checkpoint(ws), _caller_scope(ws), steps, source, owned_map)
end

"""
    prove_dominance(ws, label; map=nothing, allow_weak=false, value=nothing,
                    max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Prove one unary dominance restriction without changing the workspace, optionally
operating in the coordinate system of `map::DomainGaugeMap` or allowing a weak
optimum-preserving restriction (`allow_weak=true`). By default (`allow_weak=false`),
only strong strict-dominance steps are proved.
"""
function prove_dominance(ws::Workspace, label; map::Union{Nothing,DomainGaugeMap}=nothing,
                         allow_weak::Bool=false, value=nothing,
                         max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    map === nothing || _validate_domain_map(ws, map; full=true)
    i = _variable(ws,label)
    step, reason, method, visits, fallbacks, exact_work = _dominance_witness(ws,i;
        map,allow_weak,value,max_work,max_exact_work,deadline_ns,predecessors=ws._state.proof_count,
        scope_length=length(ws._state.callers))
    if step === nothing
        return DominanceAttempt(nothing,reason,method,visits,fallbacks,exact_work)
    end
    certificate = _build_proof_certificate(ws, step, map, deadline_ns)
    certificate === nothing && return DominanceAttempt(nothing,:deadline,method,visits,fallbacks,exact_work)
    return DominanceAttempt(certificate,reason,method,visits,fallbacks,exact_work)
end

"""
    prove_relation(ws, eliminated, representative; sign=nothing, map=nothing,
                   allow_weak=false, max_work=typemax(Int), max_exact_work=typemax(Int),
                   deadline_ns=nothing)

Prove a signed pair relation ``t_{\\text{eliminated}} = \\sigma t_{\\text{representative}}``
without mutating `ws`. When `sign` is omitted, the candidate sign opposing the
effective coupling between `eliminated` and `representative` is tested.
"""
function prove_relation(ws::Workspace, eliminated, representative;
                        sign::Union{Nothing,Int}=nothing,
                        map::Union{Nothing,DomainGaugeMap}=nothing,
                        allow_weak::Bool=false,
                        max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    map === nothing || _validate_domain_map(ws, map; full=true)
    u = _variable(ws, eliminated)
    v = _variable(ws, representative)
    step, reason, method, visits, fallbacks, exact_work = _relation_witness(
        ws, u, v; sign, map, allow_weak, max_work, max_exact_work, deadline_ns,
        predecessors=ws._state.proof_count, scope_length=length(ws._state.callers),
    )
    if step === nothing
        return RelationAttempt(nothing, reason, method, visits, fallbacks, exact_work)
    end
    certificate = _build_proof_certificate(ws, step, map, deadline_ns)
    certificate === nothing && return RelationAttempt(nothing, :deadline, method, visits, fallbacks, exact_work)
    return RelationAttempt(certificate, reason, method, visits, fallbacks, exact_work)
end

"""
    prove_elimination(ws, label; map=nothing, tie_break=:low, max_degree=2,
                      max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Prove an exact bounded-degree (`0 <= degree(ws, label) <= max_degree`) local
variable elimination without mutating `ws`. By default (`max_degree=2`), only
isolated, leaf and degree-two variables are eligible; higher-degree variables
are refused with `:degree_too_high`. When `max_degree=3` is explicitly requested,
guarded zero-cubic-Fourier degree-three reduction (`alpha_123 == 0`) is enabled,
covering zero-field star–triangle elimination as well as nonzero-field degree-3
vertices whose conditional minimum over the ``2^3 = 8`` neighbor states is an
exact quadratic polynomial; degree-3 variables whose exact marginal has a nonzero
cubic interaction (`alpha_123 != 0`) are refused with `:nonquadratic_elimination`.
"""
function prove_elimination(ws::Workspace, label;
                           map::Union{Nothing,DomainGaugeMap}=nothing,
                           tie_break::Symbol=:low,
                           max_degree=2,
                           max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    map === nothing || _validate_domain_map(ws, map; full=true)
    u = _variable(ws, label)
    step, reason, method, visits, exact_work = _elimination_witness(
        ws, u; map, tie_break, max_degree, max_work, max_exact_work, deadline_ns,
        predecessors=ws._state.proof_count, scope_length=length(ws._state.callers),
    )
    if step === nothing
        return EliminationAttempt(nothing, reason, method, visits, exact_work)
    end
    certificate = _build_proof_certificate(ws, step, map, deadline_ns)
    certificate === nothing && return EliminationAttempt(nothing, :deadline, method, visits, exact_work)
    return EliminationAttempt(certificate, reason, method, visits, exact_work)
end

"""
    prove_probing(ws, label, witness=nothing; map=nothing, value=nothing,
                  max_rounds=1, max_trial_fixes=typemax(Int),
                  max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Prove one certified probing restriction `label => value` without mutating `ws`
by temporarily conditioning on the opposite branch, propagating bounded trial
unary dominance (`max_rounds`, `max_trial_fixes`), and strictly refuting the
branch lower bound (`branch_lower > witness_upper`) against the verified
parent-scope feasible `witness` (an original-order vector, label dictionary,
[`Reconstruction`](@ref), or `nothing` to synthesize
[`coercive_field_witness`](@ref)). All trial mutations are rolled back before returning.
"""
function prove_probing(
    ws::Workspace,
    label,
    witness=nothing;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    value=nothing,
    max_rounds=1,
    max_trial_fixes=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    map === nothing || _validate_domain_map(ws, map; full=true)
    i = _variable(ws, label)
    step, reason, method, visits, fallbacks, exact_work = _probing_witness(
        ws, i, witness;
        map, value, max_rounds, max_trial_fixes,
        max_work, max_exact_work, deadline_ns,
        predecessors=ws._state.proof_count, scope_length=length(ws._state.callers),
    )
    if step === nothing
        return ProbingAttempt(nothing, reason, method, visits, fallbacks, exact_work)
    end
    certificate = _build_proof_certificate(ws, step, map, deadline_ns)
    certificate === nothing && return ProbingAttempt(nothing, :deadline, method, visits, fallbacks, exact_work)
    return ProbingAttempt(certificate, reason, method, visits, fallbacks, exact_work)
end

function _resolve_roof_candidates(ws::Workspace, candidates)
    n = length(ws._snapshot.labels)
    candidates === nothing && return collect(1:n)
    seen = Set{Int}()
    out = Int[]
    for label in candidates
        i = _variable(ws, label)
        if !(i in seen)
            push!(out, i)
            push!(seen, i)
        end
    end
    return out
end

function _roof_duality_pass(
    ws::Workspace,
    cand_indices::Vector{Int};
    value_filter::Union{Nothing,Int}=nothing,
    max_work::Int=typemax(Int),
    max_exact_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    s = ws._snapshot
    st = ws._state
    direction = _direction(s)
    direction != 0 ||
        return (Pair{Int,Int}[], (), nothing, nothing, nothing, :zero_scale, :none, 0, 0, 0, 0, 0)
    ok, reason, net, C_base, graph_work, exact_work = _build_implication_network(
        ws; max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    ok || return (
        Pair{Int,Int}[], (), nothing, nothing, nothing,
        reason, :exact, graph_work, 0, 0, graph_work, exact_work,
    )
    ok_flow, flow_reason, total_flow, flow_work, flow_exact = _dinic_max_flow!(
        net;
        max_work=max_work - graph_work,
        max_exact_work=max_exact_work - exact_work,
        deadline_ns=deadline_ns,
    )
    exact_work += flow_exact
    total_visits = graph_work + flow_work
    ok_flow || return (
        Pair{Int,Int}[], (), nothing, nothing, nothing,
        flow_reason, :exact, graph_work, flow_work, 0, total_visits, exact_work,
    )
    R_S, R_T, ver_work = _residual_reachability(net)
    if _expired(deadline_ns)
        return (
            Pair{Int,Int}[], (), nothing, nothing, nothing,
            :deadline, :exact, graph_work, flow_work, ver_work, total_visits + ver_work, exact_work,
        )
    end
    if total_visits + ver_work > max_work
        return (
            Pair{Int,Int}[], (), nothing, nothing, nothing,
            :work_limit, :exact, graph_work, flow_work, max_work - total_visits, max_work, exact_work,
        )
    end
    total_visits += ver_work
    flow_edges = _extract_flow_edges(net)
    L_roof = C_base + total_flow
    obj_bound = _Exact(s.scale) * direction * L_roof
    low_orig = s.domain === QT.BoolDomain ? 0 : -1
    batch_pairs = Pair{Int,Int}[]
    for u in cand_indices
        st.fixed[u] == 2 || continue
        if R_S[2 * u - 1] && R_T[2 * u]
            orig_val = 1
            (value_filter === nothing || orig_val == value_filter) && push!(batch_pairs, u => orig_val)
        elseif R_S[2 * u] && R_T[2 * u - 1]
            orig_val = low_orig
            (value_filter === nothing || orig_val == value_filter) && push!(batch_pairs, u => orig_val)
        end
    end
    stop = isempty(batch_pairs) ? (value_filter === nothing ? :no_persistency : :not_strict) : :proved
    return (
        batch_pairs, flow_edges, L_roof, obj_bound, total_flow,
        stop, :exact, graph_work, flow_work, ver_work, total_visits, exact_work,
    )
end

function _build_roof_certificate(
    ws::Workspace,
    batch_pairs::Vector{Pair{Int,Int}},
    flow_edges::Tuple{Vararg{Tuple{Int,Int,_Exact}}},
    L_roof::_Exact,
    total_flow::_Exact,
    map::Union{Nothing,DomainGaugeMap},
    max_work::Int,
    deadline_ns,
)
    st = ws._state
    scope_len = length(st.callers)
    base_preds = st.proof_count
    batch_tuple = Tuple(batch_pairs)
    raw_steps = Vector{RoofDualityStep}(undef, length(batch_pairs))
    cp = checkpoint(ws)
    saved_star_hint = st.star_hint
    saved_rel_hint = st.rel_hint
    mat_visits = 0
    try
        for (r, (u, orig_val)) in enumerate(batch_pairs)
            _expired(deadline_ns) && return (nothing, :deadline, mat_visits)
            c_before = deepcopy(st.constant)
            step_r = RoofDualityStep(
                u, orig_val,
                deepcopy(L_roof), deepcopy(total_flow),
                flow_edges, batch_tuple, r,
                c_before, base_preds + r - 1,
                :exact, scope_len, :strong,
            )
            raw_steps[r] = step_r
            rep = _fix!(ws, u, orig_val; proof=step_r, max_work=max_work - mat_visits, deadline_ns=deadline_ns)
            mat_visits += rep.edge_visits
            rep.stop_reason === :applied || return (nothing, rep.stop_reason, mat_visits)
        end
    finally
        if length(st.trail) > cp._depth
            rollback!(ws, cp)
        end
        st.star_hint = saved_star_hint
        st.rel_hint = saved_rel_hint
    end
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, source.labels)
    owned_map = map === nothing ? nothing : deepcopy(map)
    raw_vec = _ProofRecord[deepcopy(st.trail[p].proof) for p in st.fixes if st.trail[p].proof !== nothing]
    append!(raw_vec, raw_steps)
    raw_all = Tuple(raw_vec)
    steps = owned_map === nothing ? raw_all :
        _transport_steps(ws, _caller_scope(ws), raw_all, nothing, owned_map)
    _expired(deadline_ns) && return (nothing, :deadline, mat_visits)
    cert = DominanceCertificate(generation(ws), checkpoint(ws), _caller_scope(ws), steps, source, owned_map)
    return (cert, :proved, mat_visits)
end

"""
    prove_roof_duality(ws; candidates=nothing, map=nothing,
                       max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    prove_roof_duality(ws, label; map=nothing, value=nothing,
                       max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)

Compute the exact rational implication-network (posiform / roof-duality) lower
bound and extract strongly persistent variable assignments without mutating `ws`.
Returns a [`RoofDualityAttempt`](@ref) containing the exact normalized
`lower_bound`, scaled model `objective_bound`, maximum `S`-`T` flow `max_flow`,
strongly persistent `fixings`, phase-separated work counters, and (when at least
one candidate is strongly fixed) a locally verifiable [`DominanceCertificate`](@ref)
carrying [`RoofDualityStep`](@ref) witnesses.
"""
function prove_roof_duality(
    ws::Workspace;
    candidates=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map; full=true)
    s = ws._snapshot
    V = s.label_type
    S = s.state_type
    cand_indices = _resolve_roof_candidates(ws, candidates)
    batch_pairs, flow_edges, L_roof, obj_bound, total_flow,
        stop, method, graph_work, flow_work, ver_work, total_visits, exact_work = _roof_duality_pass(
        ws, cand_indices;
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    if isempty(batch_pairs)
        return RoofDualityAttempt{V,S}(
            nothing, stop, method, L_roof, obj_bound, total_flow,
            Pair{V,S}[], graph_work, flow_work, ver_work, total_visits, exact_work,
        )
    end
    cert, cert_reason, mat_visits = _build_roof_certificate(
        ws, batch_pairs, flow_edges, L_roof, total_flow,
        map, max_work - total_visits, deadline_ns,
    )
    total_visits += mat_visits
    if cert === nothing
        return RoofDualityAttempt{V,S}(
            nothing, cert_reason, method, L_roof, obj_bound, total_flow,
            Pair{V,S}[], graph_work, flow_work, ver_work, total_visits, exact_work,
        )
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in batch_pairs
    ]
    return RoofDualityAttempt{V,S}(
        cert, :proved, method, L_roof, obj_bound, total_flow,
        fixings, graph_work, flow_work, ver_work, total_visits, exact_work,
    )
end

function prove_roof_duality(
    ws::Workspace,
    label;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    value=nothing,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map; full=true)
    s = ws._snapshot
    V = s.label_type
    S = s.state_type
    i = _variable(ws, label)
    req_orig = if value === nothing
        nothing
    elseif map === nothing
        _assignment(ws, value)
    else
        _lift_index_value(map, i, _check_domain_scalar(value, map.target_domain))
    end
    if ws._state.fixed[i] != 2
        return RoofDualityAttempt{V,S}(
            nothing, :already_fixed, :none, nothing, nothing, nothing,
            Pair{V,S}[], 0, 0, 0, 0, 0,
        )
    end
    batch_pairs, flow_edges, L_roof, obj_bound, total_flow,
        stop, method, graph_work, flow_work, ver_work, total_visits, exact_work = _roof_duality_pass(
        ws, [i];
        value_filter=req_orig, max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    if isempty(batch_pairs)
        return RoofDualityAttempt{V,S}(
            nothing, stop, method, L_roof, obj_bound, total_flow,
            Pair{V,S}[], graph_work, flow_work, ver_work, total_visits, exact_work,
        )
    end
    cert, cert_reason, mat_visits = _build_roof_certificate(
        ws, batch_pairs, flow_edges, L_roof, total_flow,
        map, max_work - total_visits, deadline_ns,
    )
    total_visits += mat_visits
    if cert === nothing
        return RoofDualityAttempt{V,S}(
            nothing, cert_reason, method, L_roof, obj_bound, total_flow,
            Pair{V,S}[], graph_work, flow_work, ver_work, total_visits, exact_work,
        )
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in batch_pairs
    ]
    return RoofDualityAttempt{V,S}(
        cert, :proved, method, L_roof, obj_bound, total_flow,
        fixings, graph_work, flow_work, ver_work, total_visits, exact_work,
    )
end

function _connected_active_component(ws::Workspace, seed::Int; max_work::Int=typemax(Int), deadline_ns=nothing)
    st = ws._state
    n = length(ws._snapshot.labels)
    visited = falses(n)
    visited[seed] = true
    queue = Int[seed]
    work = 0
    head = 1
    while head <= length(queue)
        _expired(deadline_ns) && return (Int[], :deadline, work)
        u = queue[head]
        head += 1
        for (v, q) in st.adjacency[u]
            _expired(deadline_ns) && return (Int[], :deadline, work)
            work < max_work || return (Int[], :work_limit, work)
            work += 1
            (st.fixed[v] == 2 && !visited[v] && !iszero(_spin_coupling(ws, q))) || continue
            visited[v] = true
            push!(queue, v)
        end
    end
    return (sort!(queue), :ok, work)
end

function _submodular_cut_component_pass(
    ws::Workspace,
    comp_indices::Vector{Int};
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    tie_break::Symbol=:low,
    candidate_index::Union{Nothing,Int}=nothing,
    value_filter::Union{Nothing,Int}=nothing,
    pre_rec::Union{Nothing,SubmodularComponent}=nothing,
    max_work::Int=typemax(Int),
    max_exact_work::Int=typemax(Int),
    deadline_ns=nothing,
)
    s = ws._snapshot
    rec = pre_rec === nothing ?
        _recognize_component_indices(ws, comp_indices; max_work=max_work, deadline_ns=deadline_ns) :
        pre_rec
    rec_work = pre_rec === nothing ? rec.recognition_work : 0
    if !rec.is_submodular
        meth = rec.stop_reason in (:already_fixed, :zero_scale) ? :none : :exact
        return (
            Pair{Int,Int}[], Symbol[], Pair{Int,Int}[], Int[],
            (), nothing, nothing,
            rec.stop_reason, meth, rec_work, 0, 0, 0, rec_work, 0,
        )
    end
    ok, reason, net, C_comp, graph_work, exact_work = _build_submodular_cut_network(
        ws, comp_indices, rec.gauge;
        max_work=max_work - rec_work,
        max_exact_work=max_exact_work,
        deadline_ns=deadline_ns,
    )
    total_visits = rec_work + graph_work
    ok || return (
        Pair{Int,Int}[], Symbol[], Pair{Int,Int}[], rec.gauge,
        (), nothing, nothing,
        reason, :exact, rec_work, graph_work, 0, 0, total_visits, exact_work,
    )
    ok_flow, flow_reason, total_flow, flow_work, flow_exact = _dinic_max_flow!(
        net;
        max_work=max_work - total_visits,
        max_exact_work=max_exact_work - exact_work,
        deadline_ns=deadline_ns,
    )
    exact_work += flow_exact
    total_visits += flow_work
    ok_flow || return (
        Pair{Int,Int}[], Symbol[], Pair{Int,Int}[], rec.gauge,
        (), nothing, nothing,
        flow_reason, :exact, rec_work, graph_work, flow_work, 0, total_visits, exact_work,
    )
    R_S, R_T, ver_work = _residual_reachability(net)
    if _expired(deadline_ns)
        return (
            Pair{Int,Int}[], Symbol[], Pair{Int,Int}[], rec.gauge,
            (), nothing, nothing,
            :deadline, :exact, rec_work, graph_work, flow_work, ver_work, total_visits + ver_work, exact_work,
        )
    end
    if total_visits + ver_work > max_work
        return (
            Pair{Int,Int}[], Symbol[], Pair{Int,Int}[], rec.gauge,
            (), nothing, nothing,
            :work_limit, :exact, rec_work, graph_work, flow_work, max_work - total_visits, max_work, exact_work,
        )
    end
    total_visits += ver_work
    flow_edges = _extract_flow_edges(net)
    comp_opt = C_comp + total_flow
    low_orig = s.domain === QT.BoolDomain ? 0 : -1
    k = length(comp_indices)
    orig_sink = Vector{Int}(undef, k)
    orig_source = Vector{Int}(undef, k)
    mapped_sink = Vector{Int}(undef, k)
    mapped_source = Vector{Int}(undef, k)
    for a in 1:k
        u = comp_indices[a]
        g_a = rec.gauge[a]
        s_prime_sink = R_S[a] ? 1 : -1
        s_prime_source = R_T[a] ? -1 : 1
        s_u_sink = g_a * s_prime_sink
        s_u_source = g_a * s_prime_source
        v_sink = s_u_sink == 1 ? 1 : low_orig
        v_source = s_u_source == 1 ? 1 : low_orig
        orig_sink[a] = v_sink
        orig_source[a] = v_source
        mapped_sink[a] = map === nothing ? v_sink : _map_index_value(map, u, v_sink)
        mapped_source[a] = map === nothing ? v_source : _map_index_value(map, u, v_source)
    end
    use_sink = if tie_break === :sink
        true
    elseif tie_break === :source
        false
    elseif tie_break === :low
        mapped_sink <= mapped_source
    else
        mapped_sink >= mapped_source
    end
    chosen_orig = use_sink ? orig_sink : orig_source
    assignment_pairs = Pair{Int,Int}[comp_indices[a] => chosen_orig[a] for a in 1:k]
    batch_pairs = Pair{Int,Int}[]
    batch_pers = Symbol[]
    for a in 1:k
        u = comp_indices[a]
        (candidate_index === nothing || u == candidate_index) || continue
        is_strong = R_S[a] || R_T[a]
        (is_strong || allow_weak) || continue
        orig_val = chosen_orig[a]
        (value_filter === nothing || orig_val == value_filter) || continue
        push!(batch_pairs, u => orig_val)
        push!(batch_pers, is_strong ? :strong : :weak)
    end
    stop = if !isempty(batch_pairs)
        :proved
    elseif value_filter !== nothing
        :not_strict
    else
        :no_persistency
    end
    return (
        batch_pairs, batch_pers, assignment_pairs, rec.gauge,
        flow_edges, comp_opt, total_flow,
        stop, :exact, rec_work, graph_work, flow_work, ver_work, total_visits, exact_work,
    )
end

function _build_submodular_cut_certificate(
    ws::Workspace,
    component_batches::Vector{Tuple{
        Vector{Int},
        Vector{Int},
        _Exact,
        _Exact,
        Tuple{Vararg{Tuple{Int,Int,_Exact}}},
        Vector{Pair{Int,Int}},
        Vector{Symbol},
    }},
    map::Union{Nothing,DomainGaugeMap},
    max_work::Int,
    deadline_ns,
)
    st = ws._state
    scope_len = length(st.callers)
    base_preds = st.proof_count
    raw_steps = SubmodularCutStep[]
    cp = checkpoint(ws)
    saved_star_hint = st.star_hint
    saved_rel_hint = st.rel_hint
    mat_visits = 0
    try
        for (comp_indices, gauge_vec, comp_opt, total_flow, flow_edges, batch_pairs, batch_pers) in component_batches
            comp_tuple = Tuple(comp_indices)
            gauge_tuple = Tuple(gauge_vec)
            batch_tuple = Tuple(batch_pairs)
            for (r, (u, orig_val)) in enumerate(batch_pairs)
                _expired(deadline_ns) && return (nothing, :deadline, mat_visits)
                c_before = deepcopy(st.constant)
                step_r = SubmodularCutStep(
                    u, orig_val,
                    comp_tuple, gauge_tuple,
                    deepcopy(comp_opt), deepcopy(total_flow),
                    flow_edges, batch_tuple, r,
                    c_before, base_preds + length(raw_steps),
                    :exact, scope_len, batch_pers[r],
                )
                push!(raw_steps, step_r)
                rep = _fix!(ws, u, orig_val; proof=step_r, max_work=max_work - mat_visits, deadline_ns=deadline_ns)
                mat_visits += rep.edge_visits
                rep.stop_reason === :applied || return (nothing, rep.stop_reason, mat_visits)
            end
        end
    finally
        if length(st.trail) > cp._depth
            rollback!(ws, cp)
        end
        st.star_hint = saved_star_hint
        st.rel_hint = saved_rel_hint
    end
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, source.labels)
    owned_map = map === nothing ? nothing : deepcopy(map)
    raw_vec = _ProofRecord[deepcopy(st.trail[p].proof) for p in st.fixes if st.trail[p].proof !== nothing]
    append!(raw_vec, raw_steps)
    raw_all = Tuple(raw_vec)
    steps = owned_map === nothing ? raw_all :
        _transport_steps(ws, _caller_scope(ws), raw_all, nothing, owned_map)
    _expired(deadline_ns) && return (nothing, :deadline, mat_visits)
    cert = DominanceCertificate(generation(ws), checkpoint(ws), _caller_scope(ws), steps, source, owned_map)
    return (cert, :proved, mat_visits)
end

"""
    prove_submodular_cut(ws; component=nothing, map=nothing, allow_weak=false,
                         tie_break=:low, max_work=typemax(Int),
                         max_exact_work=typemax(Int), deadline_ns=nothing)
    prove_submodular_cut(ws, component_or_label; map=nothing, allow_weak=false,
                         tie_break=:low, value=nothing, max_work=typemax(Int),
                         max_exact_work=typemax(Int), deadline_ns=nothing)

Recognize one or all gauge-submodular residual components in `ws` and solve them
via a direct ``(|C| + 2)``-vertex exact ``s``-``t`` min-cut without mutating `ws`.
By default (`allow_weak=false`), only strongly persistent assignments (optimal in
every minimum cut of the component) are certified. When `allow_weak=true`, a
complete jointly optimal component assignment is selected via `tie_break`
(`:low`, `:high`, `:source`, or `:sink`), tagging tied vertices with `:weak`
persistency. Returns a [`SubmodularCutAttempt`](@ref).
"""
function prove_submodular_cut(
    ws::Workspace;
    component=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    tie_break::Symbol=:low,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    component !== nothing && return prove_submodular_cut(
        ws, component;
        map=map, allow_weak=allow_weak, tie_break=tie_break,
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map; full=true)
    tie_break in (:low, :high, :source, :sink) ||
        throw(ArgumentError("tie_break must be :low, :high, :source, or :sink"))
    s = ws._snapshot
    V = s.label_type
    S = s.state_type
    direction = _direction(s)
    if direction == 0
        return SubmodularCutAttempt{V,S}(
            nothing, :zero_scale, :none, nothing, nothing,
            Pair{V,Int}[], Pair{V,S}[], Pair{V,S}[],
            0, 0, 0, 0, 0, 0,
        )
    end
    comps, rec_stop, rec_work = recognize_submodular_components(
        ws; max_work=max_work, deadline_ns=deadline_ns,
    )
    if rec_stop in (:deadline, :work_limit)
        return SubmodularCutAttempt{V,S}(
            nothing, rec_stop, :exact, nothing, nothing,
            Pair{V,Int}[], Pair{V,S}[], Pair{V,S}[],
            rec_work, 0, 0, 0, rec_work, 0,
        )
    end
    submod_comps = SubmodularComponent{V}[c for c in comps if c.is_submodular]
    if isempty(submod_comps)
        stop = isempty(comps) ? :no_persistency : :frustrated_cycle
        return SubmodularCutAttempt{V,S}(
            nothing, stop, :exact, nothing, nothing,
            Pair{V,Int}[], Pair{V,S}[], Pair{V,S}[],
            rec_work, 0, 0, 0, rec_work, 0,
        )
    end
    total_graph_work = 0
    total_flow_work = 0
    total_ver_work = 0
    total_visits = rec_work
    total_exact_work = 0
    total_comp_opt = _Exact(0)
    total_max_flow = _Exact(0)
    all_gauge = Pair{V,Int}[]
    all_assignment = Pair{V,S}[]
    all_batch_pairs = Pair{Int,Int}[]
    component_batches = Tuple{
        Vector{Int},Vector{Int},_Exact,_Exact,
        Tuple{Vararg{Tuple{Int,Int,_Exact}}},Vector{Pair{Int,Int}},Vector{Symbol},
    }[]
    for c in submod_comps
        batch_pairs, batch_pers, assign_pairs, gauge_vec,
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
            return SubmodularCutAttempt{V,S}(
                nothing, stop, :exact, nothing, nothing,
                all_gauge, all_assignment, Pair{V,S}[],
                rec_work, total_graph_work, total_flow_work, total_ver_work, total_visits, total_exact_work,
            )
        end
        total_comp_opt += comp_opt
        total_max_flow += c_flow
        for (a, u) in enumerate(c.indices)
            push!(all_gauge, deepcopy(s.labels[u]) => gauge_vec[a])
        end
        for (u, orig_val) in assign_pairs
            push!(
                all_assignment,
                deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val)),
            )
        end
        if !isempty(batch_pairs)
            append!(all_batch_pairs, batch_pairs)
            push!(
                component_batches,
                (c.indices, gauge_vec, comp_opt, c_flow, flow_edges, batch_pairs, batch_pers),
            )
        end
    end
    if isempty(all_batch_pairs)
        return SubmodularCutAttempt{V,S}(
            nothing, :no_persistency, :exact, total_comp_opt, total_max_flow,
            all_gauge, all_assignment, Pair{V,S}[],
            rec_work, total_graph_work, total_flow_work, total_ver_work, total_visits, total_exact_work,
        )
    end
    cert, cert_reason, mat_visits = _build_submodular_cut_certificate(
        ws, component_batches, map, max_work - total_visits, deadline_ns,
    )
    total_visits += mat_visits
    if cert === nothing
        return SubmodularCutAttempt{V,S}(
            nothing, cert_reason, :exact, total_comp_opt, total_max_flow,
            all_gauge, all_assignment, Pair{V,S}[],
            rec_work, total_graph_work, total_flow_work, total_ver_work, total_visits, total_exact_work,
        )
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in all_batch_pairs
    ]
    return SubmodularCutAttempt{V,S}(
        cert, :proved, :exact, total_comp_opt, total_max_flow,
        all_gauge, all_assignment, fixings,
        rec_work, total_graph_work, total_flow_work, total_ver_work, total_visits, total_exact_work,
    )
end

function prove_submodular_cut(
    ws::Workspace,
    component_or_label;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    tie_break::Symbol=:low,
    value=nothing,
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    _limits(max_work, deadline_ns)
    _limits(max_exact_work, deadline_ns)
    map === nothing || _validate_domain_map(ws, map; full=true)
    tie_break in (:low, :high, :source, :sink) ||
        throw(ArgumentError("tie_break must be :low, :high, :source, or :sink"))
    s = ws._snapshot
    st = ws._state
    V = s.label_type
    S = s.state_type
    comp_indices = Int[]
    candidate_index = nothing
    req_orig = nothing
    init_rec_work = 0
    if component_or_label isa SubmodularComponent
        value === nothing || throw(ArgumentError("value keyword is only supported when proving a single variable label"))
        seen = Set{Int}()
        for lbl in component_or_label.variables
            u = _variable(ws, lbl)
            if !(u in seen)
                push!(comp_indices, u)
                push!(seen, u)
            end
        end
        isempty(comp_indices) && throw(ArgumentError("component must contain at least one variable"))
        sort!(comp_indices)
    elseif !(component_or_label isa Union{AbstractVector,AbstractSet}) && haskey(st.labels, component_or_label)
        i = _variable(ws, component_or_label)
        candidate_index = i
        if value !== nothing
            req_orig = map === nothing ? _assignment(ws, value) :
                _lift_index_value(map, i, _check_domain_scalar(value, map.target_domain))
        end
        if st.fixed[i] != 2
            return SubmodularCutAttempt{V,S}(
                nothing, :already_fixed, :none, nothing, nothing,
                Pair{V,Int}[], Pair{V,S}[], Pair{V,S}[],
                0, 0, 0, 0, 0, 0,
            )
        end
        if _direction(s) == 0
            return SubmodularCutAttempt{V,S}(
                nothing, :zero_scale, :none, nothing, nothing,
                Pair{V,Int}[], Pair{V,S}[], Pair{V,S}[],
                0, 0, 0, 0, 0, 0,
            )
        end
        comp_indices, conn_reason, conn_work = _connected_active_component(
            ws, i; max_work=max_work, deadline_ns=deadline_ns,
        )
        init_rec_work = conn_work
        if conn_reason !== :ok
            return SubmodularCutAttempt{V,S}(
                nothing, conn_reason, :exact, nothing, nothing,
                Pair{V,Int}[], Pair{V,S}[], Pair{V,S}[],
                init_rec_work, 0, 0, 0, init_rec_work, 0,
            )
        end
    else
        value === nothing || throw(ArgumentError("value keyword is only supported when proving a single variable label"))
        seen = Set{Int}()
        for lbl in component_or_label
            u = _variable(ws, lbl)
            if !(u in seen)
                push!(comp_indices, u)
                push!(seen, u)
            end
        end
        isempty(comp_indices) && throw(ArgumentError("component must contain at least one variable"))
        sort!(comp_indices)
    end
    batch_pairs, batch_pers, assign_pairs, gauge_vec,
        flow_edges, comp_opt, total_flow,
        stop, method, rec_work, graph_work, flow_work, ver_work, total_visits, exact_work = _submodular_cut_component_pass(
        ws, comp_indices;
        map=map, allow_weak=allow_weak, tie_break=tie_break,
        candidate_index=candidate_index, value_filter=req_orig,
        max_work=max_work - init_rec_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
    )
    rec_work += init_rec_work
    total_visits += init_rec_work
    gauge_out = isempty(gauge_vec) ? Pair{V,Int}[] :
        Pair{V,Int}[deepcopy(s.labels[comp_indices[a]]) => gauge_vec[a] for a in 1:length(comp_indices)]
    assign_out = isempty(assign_pairs) ? Pair{V,S}[] :
        Pair{V,S}[
            deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
            for (u, orig_val) in assign_pairs
        ]
    if isempty(batch_pairs)
        return SubmodularCutAttempt{V,S}(
            nothing, stop, method, comp_opt, total_flow,
            gauge_out, assign_out, Pair{V,S}[],
            rec_work, graph_work, flow_work, ver_work, total_visits, exact_work,
        )
    end
    component_batches = Tuple{
        Vector{Int},Vector{Int},_Exact,_Exact,
        Tuple{Vararg{Tuple{Int,Int,_Exact}}},Vector{Pair{Int,Int}},Vector{Symbol},
    }[(comp_indices, gauge_vec, comp_opt, total_flow, flow_edges, batch_pairs, batch_pers)]
    cert, cert_reason, mat_visits = _build_submodular_cut_certificate(
        ws, component_batches, map, max_work - total_visits, deadline_ns,
    )
    total_visits += mat_visits
    if cert === nothing
        return SubmodularCutAttempt{V,S}(
            nothing, cert_reason, method, comp_opt, total_flow,
            gauge_out, assign_out, Pair{V,S}[],
            rec_work, graph_work, flow_work, ver_work, total_visits, exact_work,
        )
    end
    fixings = Pair{V,S}[
        deepcopy(s.labels[u]) => S(map === nothing ? orig_val : _map_index_value(map, u, orig_val))
        for (u, orig_val) in batch_pairs
    ]
    return SubmodularCutAttempt{V,S}(
        cert, :proved, method, comp_opt, total_flow,
        gauge_out, assign_out, fixings,
        rec_work, graph_work, flow_work, ver_work, total_visits, exact_work,
    )
end

"""
    prove_maxcut(ws, label; map=nothing, allow_weak=false, value=nothing,
                 max_triangles=typemax(Int), max_work=typemax(Int),
                 max_exact_work=typemax(Int), deadline_ns=nothing)
    prove_maxcut(ws, eliminated, representative; sign=nothing, map=nothing,
                 allow_weak=false, max_triangles=typemax(Int),
                 max_work=typemax(Int), max_exact_work=typemax(Int),
                 deadline_ns=nothing)

Prove a certified weighted Max-Cut edge or triangle preprocessing restriction
on the active residual Max-Cut graph ``G_{\\text{MC}} = (\\{0\\} \\cup F, E_{\\text{cut}}, w)``
without mutating `ws`. With `(ws, label)`, tests a unary variable fixing
(`representative == 0`) using the reference edge ``(u, 0)`` and bounded
field-coupling triangles ``\\{u, 0, c\\}``. With `(ws, eliminated, representative)`,
tests a signed pair contraction ``t_{\\text{eliminated}} = \\sigma t_{\\text{representative}}``
using the internal edge ``(u, v)`` and bounded triangles ``\\{u, v, c\\}``
(including ``c = 0`` and ``c \\in F \\setminus \\{u, v\\}``). Returns a
[`MaxCutAttempt`](@ref).
"""
function prove_maxcut(
    ws::Workspace,
    label;
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    value=nothing,
    max_triangles=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    map === nothing || _validate_domain_map(ws, map; full=true)
    u = _variable(ws, label)
    step, reason, method, margin, tris_used, g_work, t_work, ex_work = _maxcut_witness(
        ws, u, 0;
        value=value, map=map, allow_weak=allow_weak, max_triangles=max_triangles,
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
        predecessors=ws._state.proof_count, scope_length=length(ws._state.callers),
    )
    visits = g_work + t_work
    if step === nothing
        return MaxCutAttempt(nothing, reason, method, margin, tris_used, g_work, t_work, visits, ex_work)
    end
    cert = _build_proof_certificate(ws, step, map, deadline_ns)
    cert === nothing &&
        return MaxCutAttempt(nothing, :deadline, method, margin, tris_used, g_work, t_work, visits, ex_work)
    return MaxCutAttempt(cert, reason, method, margin, tris_used, g_work, t_work, visits, ex_work)
end

function prove_maxcut(
    ws::Workspace,
    eliminated,
    representative;
    sign::Union{Nothing,Int}=nothing,
    map::Union{Nothing,DomainGaugeMap}=nothing,
    allow_weak::Bool=false,
    max_triangles=typemax(Int),
    max_work=typemax(Int),
    max_exact_work=typemax(Int),
    deadline_ns=nothing,
)
    map === nothing || _validate_domain_map(ws, map; full=true)
    u = _variable(ws, eliminated)
    v = _variable(ws, representative)
    step, reason, method, margin, tris_used, g_work, t_work, ex_work = _maxcut_witness(
        ws, u, v;
        sign=sign, map=map, allow_weak=allow_weak, max_triangles=max_triangles,
        max_work=max_work, max_exact_work=max_exact_work, deadline_ns=deadline_ns,
        predecessors=ws._state.proof_count, scope_length=length(ws._state.callers),
    )
    visits = g_work + t_work
    if step === nothing
        return MaxCutAttempt(nothing, reason, method, margin, tris_used, g_work, t_work, visits, ex_work)
    end
    cert = _build_proof_certificate(ws, step, map, deadline_ns)
    cert === nothing &&
        return MaxCutAttempt(nothing, :deadline, method, margin, tris_used, g_work, t_work, visits, ex_work)
    return MaxCutAttempt(cert, reason, method, margin, tris_used, g_work, t_work, visits, ex_work)
end

"""
    transport_certificate(ws::Workspace, cert::DominanceCertificate, map::DomainGaugeMap)

Transport a valid [`DominanceCertificate`](@ref) for `ws` into the coordinate
representation of `map` while preserving its `generation`, branch checkpoint,
explicit caller `assumptions` and lifted original-domain deductions/reductions.
Rejects stale generations, mismatched source/variable ordering, invalid gauges
or stale branch scopes with `ArgumentError`.
"""
function transport_certificate(ws::Workspace, cert::DominanceCertificate, map::DomainGaugeMap)
    _validate_domain_map(ws, map; full=true)
    generation(ws) == generation(cert) || throw(ArgumentError("certificate belongs to a stale generation"))
    _same_source(ws._snapshot, cert._source) || throw(ArgumentError("certificate source does not match workspace"))
    cert.assumptions == _caller_scope(ws) && cert._scope_checkpoint._depth == length(ws._state.trail) ||
        throw(ArgumentError("certificate scope does not match current workspace trail"))
    _validate_checkpoint(ws, cert._scope_checkpoint)
    cert._map === nothing || _validate_domain_map(ws, cert._map; full=true)
    isempty(cert.steps) && throw(ArgumentError("certificate contains no proof steps"))
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, source.labels)
    owned_map = deepcopy(map)
    steps = _transport_steps(ws, cert.assumptions, cert.steps, cert._map, owned_map)
    return DominanceCertificate(generation(ws), checkpoint(ws), cert.assumptions, steps, source, owned_map)
end

function _verify_dominance_step(
    p::_PolyState,
    step::DominanceStep,
    active_map::Union{Nothing,DomainGaugeMap},
    later_assumptions,
    cost::Int,
    deadline,
)
    u = step.variable
    1 <= u <= p.n && p.active[u] || return (false, :invalid_step, 0)
    low_orig = p.domain === QT.BoolDomain ? 0 : -1
    step.value in (low_orig, 1) || return (false, :invalid_value, 0)
    step.method in (:interval, :exact, :marginal) && step.persistency in (:strong, :weak) ||
        return (false, :invalid_method, 0)
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    target_dom = active_map === nothing ? p.domain : _qt_domain(active_map.target_domain)
    low_target = target_dom === QT.BoolDomain ? 0 : -1
    mapped_val = active_map === nothing ? step.value : _map_index_value(active_map, u, step.value)
    if step.method === :marginal
        ok, m_reason, comp, delta_marg = _poly_marginal_diff(p, u, active_map, deadline)
        ok || return (false, m_reason, cost)
        all(a -> !(a.first in comp), later_assumptions) || return (false, :invalid_scope, cost)
        step.lower == delta_marg && step.upper == delta_marg || return (false, :invalid_bound, cost)
        val_ok = if step.persistency === :strong
            mapped_val == low_target ? (delta_marg > 0) : (delta_marg < 0)
        else
            mapped_val == low_target ? (delta_marg >= 0) : (delta_marg <= 0)
        end
        val_ok || return (false, :invalid_bound, cost)
        _poly_fix!(p, u, step.value)
        return (true, :verified, cost)
    end
    if active_map === nothing
        lower = direction * p.fields[u]
        upper = lower
        for (nbr, q) in p.adj[u]
            _expired(deadline) && return (false, :deadline, cost)
            p.active[nbr] || continue
            coeff = direction * q
            if p.domain === QT.BoolDomain
                lower += min(0, coeff)
                upper += max(0, coeff)
            else
                lower -= abs(coeff)
                upper += abs(coeff)
            end
        end
    else
        is_bool = p.domain === QT.BoolDomain
        g = active_map.gauge
        g_u = g[u]
        h_gauged_u = g_u * p.h_spin[u]
        if active_map.target_domain === :spin
            lower = direction * h_gauged_u
            upper = lower
            for (nbr, q) in p.adj[u]
                _expired(deadline) && return (false, :deadline, cost)
                p.active[nbr] || continue
                J_uw = (g_u * g[nbr]) * (is_bool ? (q // 4) : q)
                c = abs(direction * J_uw)
                lower -= c
                upper += c
            end
        else
            a_bool = 2 * h_gauged_u
            for (nbr, q) in p.adj[u]
                p.active[nbr] || continue
                J_uw = (g_u * g[nbr]) * (is_bool ? (q // 4) : q)
                a_bool -= 2 * J_uw
            end
            lower = direction * a_bool
            upper = lower
            for (nbr, q) in p.adj[u]
                _expired(deadline) && return (false, :deadline, cost)
                p.active[nbr] || continue
                J_uw = (g_u * g[nbr]) * (is_bool ? (q // 4) : q)
                b_uw = direction * (4 * J_uw)
                lower += min(0, b_uw)
                upper += max(0, b_uw)
            end
        end
    end
    _expired(deadline) && return (false, :deadline, cost)
    enclosure = step.method === :exact ? (step.lower == lower && step.upper == upper) :
                                         (step.lower <= lower <= upper <= step.upper)
    if step.persistency === :strong
        s_val = _strict_value(step.lower, step.upper, target_dom)
        lifted = s_val === nothing ? nothing : (active_map === nothing ? s_val : _lift_index_value(active_map, u, s_val))
        enclosure && lifted == step.value || return (false, :invalid_bound, cost)
    else
        weak_ok = mapped_val == low_target ? (step.lower >= 0) : (step.upper <= 0)
        enclosure && weak_ok || return (false, :invalid_bound, cost)
    end
    _poly_fix!(p, u, step.value)
    return (true, :verified, cost)
end

function _verify_relation_step(
    p::_PolyState,
    step::RelationStep,
    active_map::Union{Nothing,DomainGaugeMap},
    cost::Int,
    deadline,
)
    u, v = step.eliminated, step.representative
    1 <= u <= p.n && 1 <= v <= p.n && u != v && p.active[u] && p.active[v] ||
        return (false, :invalid_step, 0)
    step.sign in (-1, 1) && step.orig_sign in (-1, 1) || return (false, :invalid_value, 0)
    expected_sign = active_map === nothing ? step.orig_sign :
        (active_map.gauge[u] * active_map.gauge[v] * step.orig_sign)
    step.sign == expected_sign || return (false, :invalid_value, 0)
    step.method in (:interval, :exact, :glk_pair, :coflip_pair) && step.persistency in (:strong, :weak) ||
        return (false, :invalid_method, 0)
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    is_bool = p.domain === QT.BoolDomain
    g_u = active_map === nothing ? 1 : active_map.gauge[u]
    h_u = direction * g_u * p.h_spin[u]
    rad_u_other = _Exact(0)
    center = _Exact(0)
    for (nbr, q) in p.adj[u]
        _expired(deadline) && return (false, :deadline, cost)
        p.active[nbr] || continue
        g_nbr = active_map === nothing ? 1 : active_map.gauge[nbr]
        J_uw = (g_u * g_nbr) * (is_bool ? (q // 4) : q)
        if nbr == v
            center = -step.sign * (direction * J_uw)
        else
            rad_u_other += abs(direction * J_uw)
        end
    end
    if step.method === :glk_pair
        (center > 0 && !iszero(h_u)) || return (false, :invalid_bound, cost)
        g_v = active_map === nothing ? 1 : active_map.gauge[v]
        h_v = direction * g_v * p.h_spin[v]
        rad_v_other = _Exact(0)
        for (nbr, q) in p.adj[v]
            _expired(deadline) && return (false, :deadline, cost)
            p.active[nbr] || continue
            if nbr != u
                g_nbr = active_map === nothing ? 1 : active_map.gauge[nbr]
                J_vw = (g_v * g_nbr) * (is_bool ? (q // 4) : q)
                rad_v_other += abs(direction * J_vw)
            end
        end
        _expired(deadline) && return (false, :deadline, cost)
        m_u_1 = center - step.sign * h_u - rad_u_other
        m_u_2 = center + step.sign * h_u - rad_u_other
        m_v_1 = center + h_v - rad_v_other
        m_v_2 = center - h_v - rad_v_other
        lo_a, hi_a = minmax(m_u_1, m_v_2)
        lo_b, hi_b = minmax(m_v_1, m_u_2)
        lower, upper = (lo_a > lo_b || (lo_a == lo_b && hi_a >= hi_b)) ? (lo_a, hi_a) : (lo_b, hi_b)
        enclosure = (step.lower == lower && step.upper == upper)
    elseif step.method === :coflip_pair
        center >= 0 || return (false, :invalid_bound, cost)
        g_v = active_map === nothing ? 1 : active_map.gauge[v]
        h_v = direction * g_v * p.h_spin[v]
        diff_sum = rad_u_other
        for (nbr, q) in p.adj[v]
            _expired(deadline) && return (false, :deadline, cost)
            p.active[nbr] || continue
            if nbr != u
                g_nbr = active_map === nothing ? 1 : active_map.gauge[nbr]
                J_vw = direction * (g_v * g_nbr) * (is_bool ? (q // 4) : q)
                pos_uw = get(p.adj_pos[u], nbr, 0)
                q_uw = (pos_uw != 0 && p.active[nbr]) ? p.adj[u][pos_uw].second : _Exact(0)
                if !iszero(q_uw)
                    J_uw = direction * (g_u * g_nbr) * (is_bool ? (q_uw // 4) : q_uw)
                    diff_sum += abs(J_uw - step.sign * J_vw) - abs(J_uw)
                else
                    diff_sum += abs(J_vw)
                end
            end
        end
        _expired(deadline) && return (false, :deadline, cost)
        rad_cf = (abs(h_u - step.sign * h_v) + diff_sum) // 2
        lower = center - rad_cf
        upper = center + rad_cf
        enclosure = (step.lower == lower && step.upper == upper)
    else
        rad = abs(h_u) + rad_u_other
        lower = center - rad
        upper = center + rad
        _expired(deadline) && return (false, :deadline, cost)
        enclosure = step.method === :exact ? (step.lower == lower && step.upper == upper) :
                                             (step.lower <= lower <= upper <= step.upper)
    end
    bound_ok = step.persistency === :strong ? (step.lower > 0) : (step.lower >= 0)
    enclosure && bound_ok || return (false, :invalid_bound, cost)
    cd, fd, qd = _poly_relation_deltas(p, u, v, step.orig_sign)
    _poly_apply_deltas!(p, u, cd, fd, qd)
    return (true, :verified, cost)
end

function _verify_elimination_step(
    p::_PolyState,
    step::EliminationStep,
    active_map::Union{Nothing,DomainGaugeMap},
    cost::Int,
    deadline,
)
    u = step.variable
    1 <= u <= p.n && p.active[u] || return (false, :invalid_step, 0)
    d = length(step.neighbors)
    0 <= d <= 3 || return (false, :invalid_step, 0)
    for idx in 1:d
        nbr = step.neighbors[idx]
        1 <= nbr <= p.n && nbr != u && p.active[nbr] || return (false, :invalid_step, 0)
        idx > 1 && step.neighbors[idx - 1] >= nbr && return (false, :invalid_step, 0)
    end
    for (w, q) in p.adj[u]
        (p.active[w] && !iszero(q)) || continue
        w in step.neighbors || return (false, :invalid_step, 0)
    end
    num_states = 1 << d
    low_orig = p.domain === QT.BoolDomain ? 0 : -1
    length(step.table) == num_states && all(v -> v in (low_orig, 1), step.table) ||
        return (false, :invalid_value, 0)
    seen_lin = Set{Int}()
    for (w, df) in step.linear_deltas
        (!iszero(df) && (w in step.neighbors) && !(w in seen_lin)) || return (false, :invalid_step, 0)
        push!(seen_lin, w)
    end
    seen_quad = Set{Tuple{Int,Int}}()
    for (a, b, dq) in step.quadratic_deltas
        (!iszero(dq) && a < b && (a in step.neighbors) && (b in step.neighbors) && !((a, b) in seen_quad)) ||
            return (false, :invalid_step, 0)
        push!(seen_quad, (a, b))
    end
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    couplings = Vector{_Exact}(undef, d)
    for b in 1:d
        nbr = step.neighbors[b]
        pos = findfirst(pair -> pair.first == nbr, p.adj[u])
        pos !== nothing && !iszero(p.adj[u][pos].second) || return (false, :invalid_step, 0)
        couplings[b] = p.adj[u][pos].second
    end
    f_u = p.fields[u]
    all_strict = true
    z_map = Dict{Int,Int}()
    for idx in 1:num_states
        _expired(deadline) && return (false, :deadline, cost)
        L_u = f_u
        for b in 1:d
            z_b = (((idx - 1) >> (b - 1)) & 1) == 1 ? 1 : low_orig
            z_map[step.neighbors[b]] = z_b
            L_u += couplings[b] * z_b
        end
        iszero(L_u) && (all_strict = false)
        chosen = step.table[idx]
        phi_chosen = L_u * chosen
        (direction * phi_chosen <= direction * (L_u * low_orig) &&
         direction * phi_chosen <= direction * L_u) ||
            return (false, :invalid_bound, cost)
        delta_val = step.constant_delta
        for (w, df) in step.linear_deltas
            delta_val += df * z_map[w]
        end
        for (a, b, dq) in step.quadratic_deltas
            delta_val += dq * z_map[a] * z_map[b]
        end
        delta_val == phi_chosen || return (false, :invalid_bound, cost)
    end
    step.unique_argmin == all_strict || return (false, :invalid_bound, cost)
    _poly_apply_deltas!(p, u, step.constant_delta, step.linear_deltas, step.quadratic_deltas)
    return (true, :verified, cost)
end

function _poly_branch_lower_bound(p::_PolyState, deadline=nothing)
    direction = _direction_poly(p)
    is_bool = p.domain === QT.BoolDomain
    H_sum = _Exact(0)
    Q_sum = _Exact(0)
    for u in 1:p.n
        _expired(deadline) && return nothing
        p.active[u] || continue
        H_sum += p.h_spin[u]
        for (v, q) in p.adj[u]
            (p.active[v] && u < v) || continue
            Q_sum += is_bool ? (q // 4) : q
        end
    end
    c_spin = p.c_spin
    c_bpos = c_spin - H_sum + Q_sum
    L_spin = direction * c_spin
    L_bpos = direction * c_bpos
    L_bneg = direction * c_bpos
    for u in 1:p.n
        _expired(deadline) && return nothing
        p.active[u] || continue
        h_u_raw = p.h_spin[u]
        csum_u = _Exact(0)
        for (v, q) in p.adj[u]
            p.active[v] || continue
            J_uv_raw = is_bool ? (q // 4) : q
            csum_u += J_uv_raw
            if u < v
                dJ = direction * J_uv_raw
                dqb = 4 * dJ
                L_spin -= abs(dJ)
                add_qb = min(_Exact(0), dqb)
                L_bpos += add_qb
                L_bneg += add_qb
            end
        end
        f_bpos_raw = 2 * h_u_raw - 2 * csum_u
        h_u = direction * h_u_raw
        f_u = direction * f_bpos_raw
        L_spin -= abs(h_u)
        L_bpos += min(_Exact(0), f_u)
        L_bneg += min(2 * h_u, f_u - 2 * h_u)
    end
    return max(L_spin, L_bpos, L_bneg)
end

function _verify_probing_step(
    p::_PolyState,
    step::ProbingStep,
    active_map::Union{Nothing,DomainGaugeMap},
    assumptions_prefix,
    prefix_steps,
    later_assumptions,
    cost::Int,
    deadline,
)
    u = step.variable
    1 <= u <= p.n && p.active[u] || return (false, :invalid_step, 0)
    is_bool = p.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    step.value in (low_orig, 1) && step.probed_value in (low_orig, 1) && step.value != step.probed_value ||
        return (false, :invalid_value, 0)
    step.method in (:interval, :exact) && step.persistency === :strong ||
        return (false, :invalid_method, 0)
    isempty(later_assumptions) || return (false, :invalid_scope, cost)
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    w = step.witness_state
    length(w) == p.n && all(v -> v in (low_orig, 1), w) ||
        return (false, :invalid_witness, cost)
    w[u] == step.value || return (false, :invalid_witness, cost)
    for (idx, val) in assumptions_prefix
        w[idx] == val || return (false, :invalid_witness, cost)
    end
    for pstep in prefix_steps
        if pstep isa Union{DominanceStep,ProbingStep,RoofDualityStep,SubmodularCutStep}
            w[pstep.variable] == pstep.value || return (false, :invalid_witness, cost)
        elseif pstep isa MaxCutStep
            if pstep.representative == 0
                w[pstep.eliminated] == pstep.value || return (false, :invalid_witness, cost)
            else
                s_elim = is_bool ? (2 * w[pstep.eliminated] - 1) : w[pstep.eliminated]
                s_rep = is_bool ? (2 * w[pstep.representative] - 1) : w[pstep.representative]
                s_elim == pstep.orig_sign * s_rep || return (false, :invalid_witness, cost)
            end
        elseif pstep isa RelationStep
            s_elim = is_bool ? (2 * w[pstep.eliminated] - 1) : w[pstep.eliminated]
            s_rep = is_bool ? (2 * w[pstep.representative] - 1) : w[pstep.representative]
            s_elim == pstep.orig_sign * s_rep || return (false, :invalid_witness, cost)
        elseif pstep isa EliminationStep
            idx = 1
            for (bit_pos, nbr) in enumerate(pstep.neighbors)
                w[nbr] == 1 && (idx += 1 << (bit_pos - 1))
            end
            w[pstep.variable] == pstep.table[idx] || return (false, :invalid_witness, cost)
        end
    end
    w_energy = p.constant
    for v_idx in 1:p.n
        _expired(deadline) && return (false, :deadline, cost)
        p.active[v_idx] || continue
        w_energy += p.fields[v_idx] * w[v_idx]
        for (nbr, q) in p.adj[v_idx]
            (p.active[nbr] && v_idx < nbr) || continue
            w_energy += q * w[v_idx] * w[nbr]
        end
    end
    U_exact = direction * w_energy
    step.witness_upper == U_exact || return (false, :invalid_witness, cost)
    p_trial = deepcopy(p)
    _poly_fix!(p_trial, u, step.probed_value)
    for (b_idx, bstep) in enumerate(step.branch_steps)
        bstep isa DominanceStep && bstep.predecessors == b_idx - 1 &&
            bstep.method in (:interval, :exact) && bstep.persistency === :strong ||
            return (false, :invalid_step, cost)
        b_ok, b_reason, _ = _verify_dominance_step(p_trial, bstep, active_map, (), 0, deadline)
        b_ok || return (false, b_reason, cost)
    end
    L_exact = _poly_branch_lower_bound(p_trial, deadline)
    L_exact === nothing && return (false, :deadline, cost)
    enclosure = step.method === :exact ? (step.branch_lower == L_exact) :
                                         (step.branch_lower <= L_exact)
    refuted = step.branch_lower > step.witness_upper
    enclosure && refuted || return (false, :invalid_bound, cost)
    _poly_fix!(p, u, step.value)
    return (true, :verified, cost)
end

function _verify_roof_duality_step(
    p::_PolyState,
    step::RoofDualityStep,
    active_map::Union{Nothing,DomainGaugeMap},
    prefix_steps,
    all_steps,
    step_idx::Int,
    later_assumptions,
    cost::Int,
    deadline,
)
    u = step.variable
    1 <= u <= p.n && p.active[u] || return (false, :invalid_step, 0)
    is_bool = p.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    step.value in (low_orig, 1) || return (false, :invalid_value, 0)
    step.method === :exact && step.persistency === :strong ||
        return (false, :invalid_method, 0)
    isempty(later_assumptions) || return (false, :invalid_scope, cost)
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    m = length(step.batch_fixings)
    (1 <= step.batch_index <= m && step.batch_fixings[step.batch_index] == (u => step.value)) ||
        return (false, :invalid_step, cost)
    if step.batch_index == 1
        step_idx + m - 1 <= length(all_steps) || return (false, :invalid_step, cost)
        for r in 1:m
            s_r = all_steps[step_idx + r - 1]
            (s_r isa RoofDualityStep &&
             s_r.batch_index == r &&
             s_r.batch_fixings == step.batch_fixings &&
             s_r.roof_lower == step.roof_lower &&
             s_r.max_flow == step.max_flow &&
             s_r.flow_edges == step.flow_edges &&
             s_r.scope_length == step.scope_length) ||
                return (false, :invalid_step, cost)
        end
        seen_batch = Set{Int}()
        for (v_idx, v_val) in step.batch_fixings
            (1 <= v_idx <= p.n && p.active[v_idx] && !(v_idx in seen_batch) && v_val in (low_orig, 1)) ||
                return (false, :invalid_step, cost)
            push!(seen_batch, v_idx)
        end
        built = _build_poly_implication_network(p, deadline)
        built === nothing && return (false, :deadline, cost)
        net, C_base, _ = built
        ok_flow, flow_reason, _, R_S, R_T = _verify_flow_and_reachability!(
            net, step.flow_edges, step.max_flow, deadline,
        )
        ok_flow || return (false, flow_reason, cost)
        step.roof_lower == C_base + step.max_flow || return (false, :invalid_bound, cost)
        for (v_idx, v_val) in step.batch_fixings
            s_val = is_bool ? (2 * v_val - 1) : v_val
            pers_ok = s_val == 1 ? (R_S[2 * v_idx - 1] && R_T[2 * v_idx]) :
                                   (R_S[2 * v_idx] && R_T[2 * v_idx - 1])
            pers_ok || return (false, :invalid_bound, cost)
        end
    else
        !isempty(prefix_steps) || return (false, :invalid_step, cost)
        prev = prefix_steps[end]
        (prev isa RoofDualityStep &&
         prev.batch_index == step.batch_index - 1 &&
         prev.batch_fixings == step.batch_fixings &&
         prev.roof_lower == step.roof_lower &&
         prev.max_flow == step.max_flow &&
         prev.flow_edges == step.flow_edges &&
         prev.scope_length == step.scope_length) ||
            return (false, :invalid_step, cost)
    end
    _poly_fix!(p, u, step.value)
    return (true, :verified, cost)
end

function _verify_submodular_cut_step(
    p::_PolyState,
    step::SubmodularCutStep,
    active_map::Union{Nothing,DomainGaugeMap},
    prefix_steps,
    all_steps,
    step_idx::Int,
    later_assumptions,
    cost::Int,
    deadline,
)
    u = step.variable
    1 <= u <= p.n && p.active[u] || return (false, :invalid_step, 0)
    is_bool = p.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    step.value in (low_orig, 1) || return (false, :invalid_value, 0)
    step.method === :exact && step.persistency in (:strong, :weak) ||
        return (false, :invalid_method, 0)
    isempty(later_assumptions) || return (false, :invalid_scope, cost)
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    m = length(step.batch_fixings)
    (1 <= step.batch_index <= m && step.batch_fixings[step.batch_index] == (u => step.value)) ||
        return (false, :invalid_step, cost)
    if step.batch_index == 1
        step_idx + m - 1 <= length(all_steps) || return (false, :invalid_step, cost)
        for r in 1:m
            s_r = all_steps[step_idx + r - 1]
            (s_r isa SubmodularCutStep &&
             s_r.batch_index == r &&
             s_r.component_variables == step.component_variables &&
             s_r.gauge == step.gauge &&
             s_r.component_opt == step.component_opt &&
             s_r.max_flow == step.max_flow &&
             s_r.flow_edges == step.flow_edges &&
             s_r.batch_fixings == step.batch_fixings &&
             s_r.scope_length == step.scope_length &&
             s_r.method === :exact &&
             s_r.persistency in (:strong, :weak) &&
             step.batch_fixings[r] == (s_r.variable => s_r.value)) ||
                return (false, :invalid_step, cost)
        end
        ok_net, net_reason, net, C_comp, _ = _build_poly_submodular_cut_network(
            p, step.component_variables, step.gauge, deadline,
        )
        ok_net || return (false, net_reason, cost)
        k = length(step.component_variables)
        local_idx = Dict{Int,Int}(step.component_variables[a] => a for a in 1:k)
        seen_batch = Set{Int}()
        for (v_idx, v_val) in step.batch_fixings
            (haskey(local_idx, v_idx) && !(v_idx in seen_batch) && v_val in (low_orig, 1)) ||
                return (false, :invalid_step, cost)
            push!(seen_batch, v_idx)
        end
        ok_flow, flow_reason, _, R_S, R_T = _verify_flow_and_reachability!(
            net, step.flow_edges, step.max_flow, deadline,
        )
        ok_flow || return (false, flow_reason, cost)
        step.component_opt == C_comp + step.max_flow || return (false, :invalid_bound, cost)
        matches_sink = true
        matches_source = true
        has_weak = false
        for r in 1:m
            s_r = all_steps[step_idx + r - 1]::SubmodularCutStep
            v_idx, v_val = step.batch_fixings[r]
            a = local_idx[v_idx]
            s_val = is_bool ? (2 * v_val - 1) : v_val
            s_prime = step.gauge[a] * s_val
            if R_S[a]
                (s_prime == 1 && s_r.persistency === :strong) || return (false, :invalid_bound, cost)
            elseif R_T[a]
                (s_prime == -1 && s_r.persistency === :strong) || return (false, :invalid_bound, cost)
            else
                s_r.persistency === :weak || return (false, :invalid_bound, cost)
                has_weak = true
                s_prime == -1 || (matches_sink = false)
                s_prime == 1 || (matches_source = false)
            end
        end
        if has_weak
            if m == k
                in_S = falses(k + 2)
                in_S[k + 1] = true
                for r in 1:m
                    v_idx, v_val = step.batch_fixings[r]
                    a = local_idx[v_idx]
                    s_val = is_bool ? (2 * v_val - 1) : v_val
                    step.gauge[a] * s_val == 1 && (in_S[a] = true)
                end
                _cut_capacity(net, in_S) == step.max_flow || return (false, :invalid_bound, cost)
            else
                (matches_sink || matches_source) || return (false, :invalid_bound, cost)
                in_S = matches_sink ? R_S : BitVector([!R_T[idx] for idx in 1:(k + 2)])
                _cut_capacity(net, in_S) == step.max_flow || return (false, :invalid_bound, cost)
            end
        end
    else
        !isempty(prefix_steps) || return (false, :invalid_step, cost)
        prev = prefix_steps[end]
        (prev isa SubmodularCutStep &&
         prev.batch_index == step.batch_index - 1 &&
         prev.component_variables == step.component_variables &&
         prev.gauge == step.gauge &&
         prev.component_opt == step.component_opt &&
         prev.max_flow == step.max_flow &&
         prev.flow_edges == step.flow_edges &&
         prev.batch_fixings == step.batch_fixings &&
         prev.scope_length == step.scope_length) ||
            return (false, :invalid_step, cost)
    end
    _poly_fix!(p, u, step.value)
    return (true, :verified, cost)
end

function _verify_maxcut_step(
    p::_PolyState,
    step::MaxCutStep,
    active_map::Union{Nothing,DomainGaugeMap},
    later_assumptions,
    cost::Int,
    deadline,
)
    u = step.eliminated
    v = step.representative
    a = step.anchor
    1 <= u <= p.n && p.active[u] || return (false, :invalid_step, 0)
    (v == 0 || (1 <= v <= p.n && v != u && p.active[v])) ||
        return (false, :invalid_step, 0)
    is_bool = p.domain === QT.BoolDomain
    low_orig = is_bool ? 0 : -1
    step.sign in (-1, 1) && step.orig_sign in (-1, 1) ||
        return (false, :invalid_value, 0)
    if v == 0
        a == u || return (false, :invalid_step, 0)
        step.value in (low_orig, 1) || return (false, :invalid_value, 0)
        s_val = is_bool ? (2 * step.value - 1) : step.value
        step.orig_sign == s_val || return (false, :invalid_value, 0)
        expected_sign = active_map === nothing ? step.orig_sign :
            (active_map.gauge[u] * step.orig_sign)
        step.sign == expected_sign || return (false, :invalid_value, 0)
    else
        a in (u, v) || return (false, :invalid_step, 0)
        step.value == 0 || return (false, :invalid_value, 0)
        expected_sign = active_map === nothing ? step.orig_sign :
            (active_map.gauge[u] * active_map.gauge[v] * step.orig_sign)
        step.sign == expected_sign || return (false, :invalid_value, 0)
    end
    step.method in (:maxcut_edge, :maxcut_triangle) && step.persistency in (:strong, :weak) ||
        return (false, :invalid_method, 0)
    (step.method === :maxcut_edge) == isempty(step.triangles) ||
        return (false, :invalid_method, 0)
    direction = _direction_poly(p)
    direction != 0 || return (false, :zero_scale, 0)
    c_expected = _poly_mapped_constant(p, active_map)
    _expired(deadline) && return (false, :deadline, cost)
    c_expected == step.constant || return (false, :invalid_constant, cost)
    b = a == u ? v : u
    J_ab = _poly_mc_J(p, a, b, direction)
    direct_expected = -step.orig_sign * J_ab
    step.direct_weight == direct_expected || return (false, :invalid_bound, cost)
    prev_c = -1
    sum_abs_ac = _Exact(0)
    sum_gamma = _Exact(0)
    for (c, J_ac_rec, J_bc_rec, R_c_rec, gamma_rec) in step.triangles
        _expired(deadline) && return (false, :deadline, cost)
        (c == 0 || (1 <= c <= p.n && p.active[c])) && c != a && c != b && c > prev_c ||
            return (false, :invalid_step, cost)
        prev_c = c
        if c == 0 || b == 0
            isempty(later_assumptions) || return (false, :invalid_scope, cost)
        else
            all(assump -> !(assump.first in (a, b, c)), later_assumptions) ||
                return (false, :invalid_scope, cost)
        end
        J_ac = _poly_mc_J(p, a, c, direction)
        J_bc = _poly_mc_J(p, b, c, direction)
        (!iszero(J_ac) && !iszero(J_bc)) || return (false, :invalid_step, cost)
        (J_ac_rec == J_ac && J_bc_rec == J_bc) || return (false, :invalid_bound, cost)
        W_c = _poly_mc_total_abs_weight(p, c, direction, deadline)
        W_c === nothing && return (false, :deadline, cost)
        R_c = W_c - abs(J_ac) - abs(J_bc)
        R_c_rec == R_c || return (false, :invalid_bound, cost)
        sgn_ac = step.orig_sign * J_ac > 0 ? 1 : -1
        gamma_expected = max(-abs(J_ac), min(abs(J_ac), sgn_ac * J_bc - R_c))
        (gamma_rec == gamma_expected && gamma_expected > -abs(J_ac)) ||
            return (false, :invalid_bound, cost)
        sum_abs_ac += abs(J_ac)
        sum_gamma += gamma_expected
    end
    W_a = _poly_mc_total_abs_weight(p, a, direction, deadline)
    W_a === nothing && return (false, :deadline, cost)
    non_tri_expected = W_a - abs(J_ab) - sum_abs_ac
    step.non_triangle_slack == non_tri_expected || return (false, :invalid_bound, cost)
    margin_expected = direct_expected + sum_gamma - non_tri_expected
    step.margin == margin_expected || return (false, :invalid_bound, cost)
    bound_ok = step.persistency === :strong ? (margin_expected > 0) : (margin_expected >= 0)
    bound_ok || return (false, :invalid_bound, cost)
    if v == 0
        _poly_fix!(p, u, step.value)
    else
        cd, fd, qd = _poly_relation_deltas(p, u, v, step.orig_sign)
        _poly_apply_deltas!(p, u, cd, fd, qd)
    end
    return (true, :verified, cost)
end

"""
    verify_certificate(ws, certificate; map=nothing, max_work=typemax(Int), deadline_ns=nothing)

Independently recheck source identity, current caller scope, optional
[`DomainGaugeMap`](@ref) provenance and the complete ordered reduction chain
([`DominanceStep`](@ref), [`RelationStep`](@ref), [`EliminationStep`](@ref),
[`ProbingStep`](@ref), [`RoofDualityStep`](@ref), [`SubmodularCutStep`](@ref),
[`MaxCutStep`](@ref))
using exact original-coefficient evolution and domain/gauge conversion. Never
trust cached workspace fields or an authenticated identifier alone.
"""
function verify_certificate(ws::Workspace, cert::DominanceCertificate;
                            map::Union{Nothing,DomainGaugeMap}=nothing,
                            max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work,deadline_ns)
    generation(ws) == generation(cert) || return VerificationResult(false,:stale_generation,0)
    _expired(deadline_ns) && return VerificationResult(false,:deadline,0)
    s = ws._snapshot
    cost = length(s.labels) + length(s.linear.values) + length(s.quadratic.values)
    cost <= max_work || return VerificationResult(false,:work_limit,0)
    _same_source(s,cert._source) || return VerificationResult(false,:different_source,cost)
    if cert._map !== nothing
        ok, reason = _check_domain_map(ws, cert._map)
        ok || return VerificationResult(false, reason, cost)
    end
    if map !== nothing
        ok, reason = _check_domain_map(ws, map)
        ok || return VerificationResult(false, reason, cost)
        if cert._map === nothing
            map.target_domain === _domain_symbol(s.domain) ||
                return VerificationResult(false, :invalid_map, cost)
            all(==(1), map.gauge) ||
                return VerificationResult(false, :invalid_gauge, cost)
        else
            map.target_domain === cert._map.target_domain ||
                return VerificationResult(false, :invalid_map, cost)
            map.gauge == cert._map.gauge ||
                return VerificationResult(false, :invalid_gauge, cost)
        end
    end
    active_map = cert._map !== nothing ? cert._map : map
    cert.assumptions == _caller_scope(ws) || return VerificationResult(false,:stale_scope,cost)
    cert._scope_checkpoint._depth == length(ws._state.trail) ||
        return VerificationResult(false,:stale_scope,cost)
    try
        _validate_checkpoint(ws,cert._scope_checkpoint)
    catch error
        error isa ArgumentError || rethrow()
        return VerificationResult(false,:stale_scope,cost)
    end
    _expired(deadline_ns) && return VerificationResult(false,:deadline,cost)
    isempty(cert.steps) && return VerificationResult(false,:empty_proof,cost)
    seen = Set{Int}()
    low = s.domain === QT.BoolDomain ? 0 : -1
    for assumption in cert.assumptions
        assumption isa Pair{Int,Int} || return VerificationResult(false,:invalid_scope,cost)
        i,v = assumption
        1 <= i <= length(s.labels) && !(i in seen) && v in (low,1) ||
            return VerificationResult(false,:invalid_scope,cost)
        push!(seen,i)
    end
    p = _init_poly_state(s; map=active_map, deadline=deadline_ns)
    p === nothing && return VerificationResult(false,:deadline,cost)
    base_step_cost = length(s.linear.values) + length(s.quadratic.values)
    introduced = 0
    for (k,step) in enumerate(cert.steps)
        step isa Union{DominanceStep,RelationStep,EliminationStep,ProbingStep,RoofDualityStep,SubmodularCutStep,MaxCutStep} && step.predecessors == k-1 ||
            return VerificationResult(false,:invalid_predecessors,cost)
        count = step.scope_length == -1 ? length(cert.assumptions) : step.scope_length
        introduced <= count <= length(cert.assumptions) ||
            return VerificationResult(false,:invalid_scope,cost)
        for pos in introduced+1:count
            i,v = cert.assumptions[pos]
            p.active[i] || return VerificationResult(false,:invalid_scope,cost)
            _poly_fix!(p, i, v)
        end
        introduced = count
        step_cost = step isa ProbingStep ? base_step_cost * (1 + length(step.branch_steps)) : base_step_cost
        step_cost <= max_work - cost || return VerificationResult(false,:work_limit,cost)
        _expired(deadline_ns) && return VerificationResult(false,:deadline,cost)
        valid, reason, visits = if step isa DominanceStep
            later = cert.assumptions[(count + 1):end]
            _verify_dominance_step(p, step, active_map, later, step_cost, deadline_ns)
        elseif step isa RelationStep
            _verify_relation_step(p, step, active_map, step_cost, deadline_ns)
        elseif step isa ProbingStep
            later = cert.assumptions[(count + 1):end]
            _verify_probing_step(
                p, step, active_map,
                cert.assumptions[1:count], cert.steps[1:(k - 1)], later,
                step_cost, deadline_ns,
            )
        elseif step isa RoofDualityStep
            later = cert.assumptions[(count + 1):end]
            _verify_roof_duality_step(
                p, step, active_map,
                cert.steps[1:(k - 1)], cert.steps, k, later,
                step_cost, deadline_ns,
            )
        elseif step isa SubmodularCutStep
            later = cert.assumptions[(count + 1):end]
            _verify_submodular_cut_step(
                p, step, active_map,
                cert.steps[1:(k - 1)], cert.steps, k, later,
                step_cost, deadline_ns,
            )
        elseif step isa MaxCutStep
            later = cert.assumptions[(count + 1):end]
            _verify_maxcut_step(p, step, active_map, later, step_cost, deadline_ns)
        else
            _verify_elimination_step(p, step::EliminationStep, active_map, step_cost, deadline_ns)
        end
        cost += visits
        valid || return VerificationResult(false,reason,cost)
    end
    for pos in introduced+1:length(cert.assumptions)
        i,v = cert.assumptions[pos]
        p.active[i] || return VerificationResult(false,:invalid_scope,cost)
        _poly_fix!(p, i, v)
    end
    return _expired(deadline_ns) ? VerificationResult(false,:deadline,cost) :
                                   VerificationResult(true,:verified,cost)
end
