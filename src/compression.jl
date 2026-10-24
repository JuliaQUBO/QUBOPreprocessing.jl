# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    CompressionCandidate{V}

Bounded local coefficient-compression candidate audited under Issue `#21`
(Mücke, Gerlach & Piatkowski 2023, *Optimum-Preserving QUBO Parameter Compression*,
Definition 3 and Theorem 2, `arXiv:2307.02195`; audited against `qubolite`
`reduce_dynamic_range` at commit `cbe57e0bea68e9f751f8591e3ba0254030ac5965`).

Fields:
- `kind::Symbol`: `:linear` (diagonal ``L_i \\mapsto L_i'``) or `:quadratic`
  (off-diagonal ``Q_{ij} \\mapsto Q_{ij}'``)
- `variables::Tuple{V,Union{Nothing,V}}`: `(u, nothing)` for `:linear`, `(u, v)` for `:quadratic`
- `indices::Tuple{Int,Int}`: `(i, 0)` for `:linear`, `(i, j)` (`i < j`) for `:quadratic`
- `rule::Symbol`: `:qubolite_linear_closed`, `:qubolite_linear_open`,
  `:qubolite_quadratic_pos_closed`, `:qubolite_quadratic_pos_open`,
  `:qubolite_quadratic_neg_closed`, `:qubolite_quadratic_neg_open`, or `:custom`
- `endpoint::Symbol`: `:closed` (`\\epsilon = 0`) or `:open` (`\\epsilon > 0`)
- `original_coeff::Rational{BigInt}`: exact normalized Boolean minimization coefficient before update
- `compressed_coeff::Rational{BigInt}`: exact normalized Boolean minimization coefficient after update
- `delta::Rational{BigInt}`: `compressed_coeff - original_coeff`
- `lower_bound::Rational{BigInt}`: local 1-hop derivative lower bound (`c_i^-` or `c_{a,-b}^-`)
- `upper_bound::Rational{BigInt}`: local 1-hop derivative upper bound (`c_i^+` or `c_{a,-b}^+`)
- `strict_local_dominance::Bool`: whether strict 1-hop local dominance (`L_i + c_i^- > 0`,
  `L_i + c_i^+ < 0`, or pair implication `x_i x_j = 0`) already holds in the original model
- `subsuming_rule::Symbol`: `:none`, `:unary_dominance` (`#14`), or `:pair_dominance` (`#15`)
"""
struct CompressionCandidate{V}
    kind::Symbol
    variables::Tuple{V,Union{Nothing,V}}
    indices::Tuple{Int,Int}
    rule::Symbol
    endpoint::Symbol
    original_coeff::Rational{BigInt}
    compressed_coeff::Rational{BigInt}
    delta::Rational{BigInt}
    lower_bound::Rational{BigInt}
    upper_bound::Rational{BigInt}
    strict_local_dominance::Bool
    subsuming_rule::Symbol
end

"""
    CompressionMetrics

Exact sparsity and dynamic-range comparison between an original QUBO/Ising model and a
coefficient-transformed model in normalized Boolean minimization form.

`dynamic_range` is defined as `max_abs_coeff // min_abs_nonzero` when at least one
nonzero linear or quadratic coefficient exists, and `0 // 1` when all coefficients are zero.
"""
struct CompressionMetrics
    initial_nnz_linear::Int
    transformed_nnz_linear::Int
    initial_nnz_quadratic::Int
    transformed_nnz_quadratic::Int
    initial_min_abs_nonzero::Rational{BigInt}
    transformed_min_abs_nonzero::Rational{BigInt}
    initial_max_abs_coeff::Rational{BigInt}
    transformed_max_abs_coeff::Rational{BigInt}
    initial_dynamic_range::Rational{BigInt}
    transformed_dynamic_range::Rational{BigInt}
end

"""
    CompressionAuditReport{V}

Bounded exact audit report comparing an original model ``F`` against a coefficient-compressed
or sparsified model ``F'`` under `QUBOPreprocessing.jl`'s residual-to-original guarantee
``\\operatorname{lift}(\\operatorname{opt}(F')) \\subseteq \\operatorname{opt}(F)``.

Fields:
- `stop_reason::Symbol`: `:audited`, `:variable_limit_exceeded`, or `:work_limit_exceeded`
- `relation::Symbol`:
  - `:exact_optimum_set` (``\\operatorname{opt}(F') = \\operatorname{opt}(F)``)
  - `:optimum_preserving_subset` (``\\emptyset \\ne \\operatorname{opt}(F') \\subsetneq \\operatorname{opt}(F)``)
  - `:introduced_suboptimal_tie` (``\\operatorname{opt}(F) \\subsetneq \\operatorname{opt}(F')``;
    violates residual-to-original reconstruction because ``\\operatorname{opt}(F') \\setminus \\operatorname{opt}(F) \\ne \\emptyset``)
  - `:partial_overlap_with_suboptimal` (``\\operatorname{opt}(F) \\cap \\operatorname{opt}(F') \\ne \\emptyset``,
    but neither set contains the other; violates residual-to-original reconstruction)
  - `:disjoint_optimum_sets` (``\\operatorname{opt}(F) \\cap \\operatorname{opt}(F') = \\emptyset``;
    all original global optima are lost)
  - `:unverified` (audit budget or variable cap exceeded before exhaustive check)
- `residual_to_original_valid::Bool`: `true` iff `stop_reason === :audited` and every optimal
  state of ``F'`` is also globally optimal in ``F`` (``\\emptyset \\ne \\operatorname{opt}(F') \\subseteq \\operatorname{opt}(F)``)
- `constant_energy_shift::Bool`: `true` iff ``F(x) - F'(x)`` is constant across all ``2^n`` feasible states
- `optimal_energy_shift::Union{Nothing,Rational{BigInt}}`: exact shift ``F(x^*) - F'(x^*)`` when constant across ``x^* \\in \\operatorname{opt}(F')``, else `nothing`
- `valid_lower_bound_shift::Rational{BigInt}`: exact worst-case bound shift ``\\min_{x} (F(x) - F'(x))`` on normalized minimization energy
- `original_optimal_value::Rational{BigInt}`: exact optimal objective value of ``F`` (in user sense/scale/offset)
- `transformed_optimal_value::Rational{BigInt}`: exact optimal objective value of ``F'`` (in user sense/scale/offset)
- `worst_lifted_original_value::Rational{BigInt}`: worst original objective value ``F(x')`` among ``x' \\in \\operatorname{opt}(F')``
- `original_optima_count::Int`, `transformed_optima_count::Int`, `shared_optima_count::Int`
- `introduced_suboptimal_witness::Union{Nothing,Vector{Int}}`: state ``x' \\in \\operatorname{opt}(F') \\setminus \\operatorname{opt}(F)`` if any
- `lost_optimum_witness::Union{Nothing,Vector{Int}}`: state ``x^* \\in \\operatorname{opt}(F) \\setminus \\operatorname{opt}(F')`` if any
- `subsumed_by_dominance::Bool`: whether all sound candidates in this transformation are already
  subsumed by exact unary fixing (`#14`) or pair contraction (`#15`)
- `subsuming_rule::Symbol`: `:none`, `:zero_noop`, `:unary_dominance`, or `:pair_dominance`
- `decision::Symbol`: `:defer`, `:adopt_via_exact_elimination`, or `:noop`
- `missing_proof::Symbol`: explicit mathematical reason why in-place coefficient compression is deferred
- `candidates::Vector{CompressionCandidate{V}}`
- `metrics::CompressionMetrics`
- `states_evaluated::Int`, `bound_work::Int`, `verification_work::Int`, `reconstruction_work::Int`, `total_work::Int`
"""
struct CompressionAuditReport{V}
    stop_reason::Symbol
    relation::Symbol
    residual_to_original_valid::Bool
    constant_energy_shift::Bool
    optimal_energy_shift::Union{Nothing,Rational{BigInt}}
    valid_lower_bound_shift::Rational{BigInt}
    original_optimal_value::Rational{BigInt}
    transformed_optimal_value::Rational{BigInt}
    worst_lifted_original_value::Rational{BigInt}
    original_optima_count::Int
    transformed_optima_count::Int
    shared_optima_count::Int
    introduced_suboptimal_witness::Union{Nothing,Vector{Int}}
    lost_optimum_witness::Union{Nothing,Vector{Int}}
    subsumed_by_dominance::Bool
    subsuming_rule::Symbol
    decision::Symbol
    missing_proof::Symbol
    candidates::Vector{CompressionCandidate{V}}
    metrics::CompressionMetrics
    states_evaluated::Int
    bound_work::Int
    verification_work::Int
    reconstruction_work::Int
    total_work::Int
end

function _exact_rational_coeff(x::Real)
    if x isa Rational
        return Rational{BigInt}(numerator(x), denominator(x))
    elseif x isa Integer
        return Rational{BigInt}(BigInt(x), 1)
    elseif x isa AbstractFloat
        isfinite(x) || throw(ArgumentError("non-finite float coefficient $x is not supported"))
        return Rational{BigInt}(x)
    else
        throw(ArgumentError("unsupported coefficient type $(typeof(x))"))
    end
end

struct _NormalizedBoolModel{V}
    variables::Vector{V}
    domain::Symbol
    sense::Symbol
    scale::Rational{BigInt}
    offset::Rational{BigInt}
    constant::Rational{BigInt}
    linear::Vector{Rational{BigInt}}
    quadratic::Dict{Tuple{Int,Int},Rational{BigInt}}
end

function _extract_normalized_bool_model(model::QT.AbstractModel)
    vars = collect(QT.variables(model))
    n = length(vars)
    vmap = Dict{eltype(vars),Int}(v => i for (i, v) in enumerate(vars))
    dom = Symbol(QT.domain(model))
    sense = Symbol(QT.sense(model))
    scale = _exact_rational_coeff(QT.scale(model))
    offset = _exact_rational_coeff(QT.offset(model))
    sgn = sense === :max ? (-1 // 1) : (1 // 1)

    raw_L = zeros(Rational{BigInt}, n)
    for (i, c) in QT.linear_terms(model)
        idx = i isa Int && 1 <= i <= n && !(eltype(vars) === Int && haskey(vmap, i)) ? i : get(vmap, i, i)
        raw_L[idx] += sgn * _exact_rational_coeff(c)
    end
    raw_Q = Dict{Tuple{Int,Int},Rational{BigInt}}()
    for ((i, j), c) in QT.quadratic_terms(model)
        u = i isa Int && 1 <= i <= n && !(eltype(vars) === Int && haskey(vmap, i)) ? i : get(vmap, i, i)
        v = j isa Int && 1 <= j <= n && !(eltype(vars) === Int && haskey(vmap, j)) ? j : get(vmap, j, j)
        if u == v
            if dom === :bool
                raw_L[u] += sgn * _exact_rational_coeff(c)
            end
            continue
        end
        a, b = minmax(u, v)
        val = raw_Q[(a, b)] = get(raw_Q, (a, b), 0 // 1) + sgn * _exact_rational_coeff(c)
        iszero(val) && delete!(raw_Q, (a, b))
    end

    if dom === :bool
        return _NormalizedBoolModel{eltype(vars)}(vars, dom, sense, scale, offset, 0 // 1, raw_L, raw_Q)
    elseif dom === :spin
        # s_i = 2 x_i - 1 with x_i in {0, 1}:
        # sum h_i (2 x_i - 1) + sum J_ij (4 x_i x_j - 2 x_i - 2 x_j + 1)
        const_term = -sum(raw_L; init=0 // 1)
        L_bool = [2 * raw_L[i] for i in 1:n]
        Q_bool = Dict{Tuple{Int,Int},Rational{BigInt}}()
        for ((i, j), Jij) in raw_Q
            iszero(Jij) && continue
            const_term += Jij
            L_bool[i] -= 2 * Jij
            L_bool[j] -= 2 * Jij
            Q_bool[(i, j)] = 4 * Jij
        end
        return _NormalizedBoolModel{eltype(vars)}(vars, dom, sense, scale, offset, const_term, L_bool, Q_bool)
    else
        throw(ArgumentError("unsupported domain $dom"))
    end
end

function _extract_normalized_bool_model(ws::Workspace)
    m = ws._state === nothing ? export_model(materialize(ws)) : export_model(_conditioned_export(ws, _Exact))
    return _extract_normalized_bool_model(m)
end

function _to_qubotools_model(nm::_NormalizedBoolModel{V}) where {V}
    n = length(nm.variables)
    sgn = nm.sense === :max ? (-1 // 1) : (1 // 1)
    L_idx = Dict{Int,Rational{BigInt}}()
    Q_idx = Dict{Tuple{Int,Int},Rational{BigInt}}()
    if nm.domain === :bool
        for i in 1:n
            !iszero(nm.linear[i]) && (L_idx[i] = sgn * nm.linear[i])
        end
        for ((i, j), q) in nm.quadratic
            !iszero(q) && (Q_idx[(i, j)] = sgn * q)
        end
        new_offset = nm.offset + sgn * nm.constant
    else
        # x_i = (s_i + 1) / 2:
        # c + sum L_i (s_i + 1)/2 + sum Q_ij (s_i + 1)(s_j + 1)/4
        const_spin = nm.constant + sum(nm.linear; init=0 // 1) // 2
        h_spin = [nm.linear[i] // 2 for i in 1:n]
        for ((i, j), q) in nm.quadratic
            iszero(q) && continue
            const_spin += q // 4
            h_spin[i] += q // 4
            h_spin[j] += q // 4
            Q_idx[(i, j)] = sgn * (q // 4)
        end
        for i in 1:n
            !iszero(h_spin[i]) && (L_idx[i] = sgn * h_spin[i])
        end
        new_offset = nm.offset + sgn * const_spin
    end
    vm = QT.VariableMap{V}(Dict{V,Int}(v => i for (i, v) in enumerate(nm.variables)), copy(nm.variables))
    lf = QT.DictLinearForm{Rational{BigInt}}(L_idx)
    qf = QT.DictQuadraticForm{Rational{BigInt}}(Q_idx)
    qt_sense = nm.sense === :max ? QT.Max : QT.Min
    qt_dom = nm.domain === :bool ? QT.BoolDomain : QT.SpinDomain
    f = QT.Form{Rational{BigInt}}(n, lf, qf, nm.scale, new_offset; sense=qt_sense, domain=qt_dom)
    return QT.Model{V,Rational{BigInt},Int}(vm, f)
end

function _coeff_stats(nm::_NormalizedBoolModel)
    nnz_lin = count(!iszero, nm.linear)
    nnz_quad = count(kv -> !iszero(kv[2]), nm.quadratic)
    min_abs = 0 // 1
    max_abs = 0 // 1
    have_nz = false
    for c in nm.linear
        iszero(c) && continue
        ac = abs(c)
        if !have_nz
            min_abs = ac
            max_abs = ac
            have_nz = true
        else
            ac < min_abs && (min_abs = ac)
            ac > max_abs && (max_abs = ac)
        end
    end
    for (_, c) in nm.quadratic
        iszero(c) && continue
        ac = abs(c)
        if !have_nz
            min_abs = ac
            max_abs = ac
            have_nz = true
        else
            ac < min_abs && (min_abs = ac)
            ac > max_abs && (max_abs = ac)
        end
    end
    dyn = have_nz ? (max_abs // min_abs) : (0 // 1)
    return nnz_lin, nnz_quad, min_abs, max_abs, dyn
end

"""
    compression_metrics(original, transformed) -> CompressionMetrics

Compute exact sparsity (`nnz_linear`, `nnz_quadratic`) and dynamic-range
(`max_abs_coeff // min_abs_nonzero`) metrics in normalized Boolean minimization form.
"""
function compression_metrics(original, transformed)
    nm0 = _extract_normalized_bool_model(original)
    nm1 = _extract_normalized_bool_model(transformed)
    l0, q0, min0, max0, dyn0 = _coeff_stats(nm0)
    l1, q1, min1, max1, dyn1 = _coeff_stats(nm1)
    return CompressionMetrics(l0, l1, q0, q1, min0, min1, max0, max1, dyn0, dyn1)
end

function _local_bounds(n::Int, Q::Dict{Tuple{Int,Int},Rational{BigInt}})
    c_neg = zeros(Rational{BigInt}, n)
    c_pos = zeros(Rational{BigInt}, n)
    work = 0
    for ((i, j), q) in Q
        work += 1
        if q < 0
            c_neg[i] += q
            c_neg[j] += q
        elseif q > 0
            c_pos[i] += q
            c_pos[j] += q
        end
    end
    return c_neg, c_pos, work
end

"""
    qubolite_compression_candidates(
        model_or_ws;
        endpoint::Symbol=:closed,
        epsilon::Real=1 // 10,
        include_quadratic::Bool=true,
        include_negative_quadratic::Bool=false,
        chain::Bool=false,
        max_work::Int=10_000,
    )

Evaluate the Mücke–Gerlach–Piatkowski (2023) Theorem 2 / `qubolite` dynamic-range
compression rule on exact rationalized coefficients without performing any global solve.

Arguments:
- `endpoint`: `:closed` (``\\tau = 0``, setting coefficients to the exact equality threshold
  where ``\\Delta_i = 0``, which proves only ``\\operatorname{opt}(F) \\subseteq \\operatorname{opt}(F')``
  and can introduce suboptimal ties) or `:open` (``\\tau = \\epsilon > 0``, retaining strict sign).
- `epsilon`: positive interior margin ``\\epsilon > 0`` used when `endpoint === :open`.
- `include_quadratic`: whether to evaluate off-diagonal ``Q_{ij}`` updates in addition to
  diagonal ``L_i`` updates.
- `include_negative_quadratic`: whether to include negative coupling compression
  (``Q_{ij} < 0 \\mapsto Q_{ij}' > Q_{ij}`` when ``L_a + c_{a,-b}^+ + Q_{ij} \\le -\\tau``),
  which can lose all original global optima even when `endpoint === :open`.
- `chain`: if `true`, apply each candidate immediately to `L`/`Q` before evaluating later
  entries; if `false`, compute all candidates against the initial polynomial and apply them as a batch.
- `max_work`: strict work cap on coefficient/incidence inspections (`stop_reason === :work_limit_exceeded` if exceeded).

Returns a named tuple `(candidates, transformed_model, bound_work, stop_reason)`.
"""
function qubolite_compression_candidates(
    model_or_ws;
    endpoint::Symbol=:closed,
    epsilon::Real=1 // 10,
    include_quadratic::Bool=true,
    include_negative_quadratic::Bool=false,
    chain::Bool=false,
    max_work::Int=10_000,
)
    endpoint in (:closed, :open) || throw(ArgumentError("endpoint must be :closed or :open, got $endpoint"))
    max_work >= 0 || throw(ArgumentError("max_work must be non-negative, got $max_work"))
    eps_rat = _exact_rational_coeff(epsilon)
    endpoint === :open && eps_rat <= 0 && throw(ArgumentError("epsilon must be > 0 when endpoint === :open"))
    tau = endpoint === :closed ? (0 // 1) : eps_rat

    nm = _extract_normalized_bool_model(model_or_ws)
    V = eltype(nm.variables)
    n = length(nm.variables)
    L_orig = copy(nm.linear)
    Q_orig = copy(nm.quadratic)
    L_cur = copy(nm.linear)
    Q_cur = copy(nm.quadratic)

    c_neg, c_pos, work = _local_bounds(n, Q_cur)
    candidates = CompressionCandidate{V}[]
    if work > max_work
        return (
            candidates=candidates,
            transformed_model=_to_qubotools_model(nm),
            bound_work=work,
            stop_reason=:work_limit_exceeded,
        )
    end

    # 1. Diagonal (linear) parameter compression (Theorem 2 diagonal case):
    for i in 1:n
        work += 1
        if work > max_work
            nm_out = _NormalizedBoolModel{V}(nm.variables, nm.domain, nm.sense, nm.scale, nm.offset, nm.constant, L_cur, Q_cur)
            return (candidates=candidates, transformed_model=_to_qubotools_model(nm_out), bound_work=work, stop_reason=:work_limit_exceeded)
        end
        Li = L_cur[i]
        cn = c_neg[i]
        cp = c_pos[i]
        strict_dom = (L_orig[i] + cn > 0) || (L_orig[i] + cp < 0)
        sub_rule = strict_dom ? :unary_dominance : :none
        rule_sym = endpoint === :closed ? :qubolite_linear_closed : :qubolite_linear_open

        if Li + cn >= tau
            target = -cn + tau
            if target < Li && abs(target) <= abs(Li)
                cand = CompressionCandidate{V}(
                    :linear, (nm.variables[i], nothing), (i, 0), rule_sym, endpoint,
                    Li, target, target - Li, cn, cp, strict_dom, sub_rule,
                )
                push!(candidates, cand)
                L_cur[i] = target
            end
        elseif Li + cp <= -tau
            target = -cp - tau
            if target > Li && abs(target) <= abs(Li)
                cand = CompressionCandidate{V}(
                    :linear, (nm.variables[i], nothing), (i, 0), rule_sym, endpoint,
                    Li, target, target - Li, cn, cp, strict_dom, sub_rule,
                )
                push!(candidates, cand)
                L_cur[i] = target
            end
        end
    end

    # 2. Off-diagonal (quadratic) parameter compression (Theorem 2 off-diagonal case):
    if include_quadratic
        pairs = sort!(collect(keys(Q_cur)))
        for (i, j) in pairs
            work += 1
            if work > max_work
                nm_out = _NormalizedBoolModel{V}(nm.variables, nm.domain, nm.sense, nm.scale, nm.offset, nm.constant, L_cur, Q_cur)
                return (candidates=candidates, transformed_model=_to_qubotools_model(nm_out), bound_work=work, stop_reason=:work_limit_exceeded)
            end
            Qij = get(Q_cur, (i, j), 0 // 1)
            iszero(Qij) && continue
            Li = chain ? L_cur[i] : L_orig[i]
            Lj = chain ? L_cur[j] : L_orig[j]
            c_i_neg_excl = c_neg[i] - min(0 // 1, Qij)
            c_i_pos_excl = c_pos[i] - max(0 // 1, Qij)
            c_j_neg_excl = c_neg[j] - min(0 // 1, Qij)
            c_j_pos_excl = c_pos[j] - max(0 // 1, Qij)

            if Qij > 0
                best_target = Qij
                best_lb = c_i_neg_excl
                best_ub = c_i_pos_excl
                if Li + c_i_neg_excl + Qij >= tau
                    t_i = max(0 // 1, -Li - c_i_neg_excl + tau)
                    if t_i < best_target
                        best_target = t_i
                        best_lb = c_i_neg_excl
                        best_ub = c_i_pos_excl
                    end
                end
                if Lj + c_j_neg_excl + Qij >= tau
                    t_j = max(0 // 1, -Lj - c_j_neg_excl + tau)
                    if t_j < best_target
                        best_target = t_j
                        best_lb = c_j_neg_excl
                        best_ub = c_j_pos_excl
                    end
                end
                if best_target < Qij
                    unary_dom = (L_orig[i] + c_neg[i] > 0) || (L_orig[j] + c_neg[j] > 0)
                    pair_dom = (L_orig[i] + c_i_neg_excl + Qij > 0) || (L_orig[j] + c_j_neg_excl + Qij > 0)
                    sub_rule = unary_dom ? :unary_dominance : (pair_dom ? :pair_dominance : :none)
                    rule_sym = endpoint === :closed ? :qubolite_quadratic_pos_closed : :qubolite_quadratic_pos_open
                    cand = CompressionCandidate{V}(
                        :quadratic, (nm.variables[i], nm.variables[j]), (i, j), rule_sym, endpoint,
                        Qij, best_target, best_target - Qij, best_lb, best_ub,
                        unary_dom || pair_dom, sub_rule,
                    )
                    push!(candidates, cand)
                    if iszero(best_target)
                        delete!(Q_cur, (i, j))
                    else
                        Q_cur[(i, j)] = best_target
                    end
                    if chain
                        c_pos[i] += best_target - Qij
                        c_pos[j] += best_target - Qij
                    end
                end
            elseif include_negative_quadratic && Qij < 0
                best_target = Qij
                best_lb = c_i_neg_excl
                best_ub = c_i_pos_excl
                if Li + c_i_pos_excl + Qij <= -tau
                    t_i = min(0 // 1, -Li - c_i_pos_excl - tau)
                    if t_i > best_target
                        best_target = t_i
                        best_lb = c_i_neg_excl
                        best_ub = c_i_pos_excl
                    end
                end
                if Lj + c_j_pos_excl + Qij <= -tau
                    t_j = min(0 // 1, -Lj - c_j_pos_excl - tau)
                    if t_j > best_target
                        best_target = t_j
                        best_lb = c_j_neg_excl
                        best_ub = c_j_pos_excl
                    end
                end
                if best_target > Qij
                    unary_dom = (L_orig[i] + c_pos[i] < 0) || (L_orig[j] + c_pos[j] < 0)
                    sub_rule = unary_dom ? :unary_dominance : :none
                    rule_sym = endpoint === :closed ? :qubolite_quadratic_neg_closed : :qubolite_quadratic_neg_open
                    cand = CompressionCandidate{V}(
                        :quadratic, (nm.variables[i], nm.variables[j]), (i, j), rule_sym, endpoint,
                        Qij, best_target, best_target - Qij, best_lb, best_ub,
                        unary_dom, sub_rule,
                    )
                    push!(candidates, cand)
                    if iszero(best_target)
                        delete!(Q_cur, (i, j))
                    else
                        Q_cur[(i, j)] = best_target
                    end
                    if chain
                        c_neg[i] += best_target - Qij
                        c_neg[j] += best_target - Qij
                    end
                end
            end
        end
    end

    nm_out = _NormalizedBoolModel{V}(nm.variables, nm.domain, nm.sense, nm.scale, nm.offset, nm.constant, L_cur, Q_cur)
    return (
        candidates=candidates,
        transformed_model=_to_qubotools_model(nm_out),
        bound_work=work,
        stop_reason=:audited,
    )
end

function _eval_norm_bool(nm::_NormalizedBoolModel, x_bits::Vector{Int})
    val = nm.constant
    for i in eachindex(x_bits)
        x_bits[i] == 1 && (val += nm.linear[i])
    end
    for ((i, j), q) in nm.quadratic
        (x_bits[i] == 1 && x_bits[j] == 1) && (val += q)
    end
    return val
end

function _norm_to_user_objective(nm::_NormalizedBoolModel, norm_val::Rational{BigInt})
    sgn = nm.sense === :max ? (-1 // 1) : (1 // 1)
    return nm.scale * (nm.offset + sgn * norm_val)
end

function _bits_to_domain_state(domain::Symbol, x_bits::Vector{Int})
    return domain === :spin ? [2 * b - 1 for b in x_bits] : copy(x_bits)
end

function _infer_diff_candidates(nm0::_NormalizedBoolModel{V}, nm1::_NormalizedBoolModel{V}) where {V}
    n = length(nm0.variables)
    c_neg, c_pos, work = _local_bounds(n, nm0.quadratic)
    cands = CompressionCandidate{V}[]
    for i in 1:n
        work += 1
        L0 = nm0.linear[i]
        L1 = nm1.linear[i]
        L0 == L1 && continue
        strict_dom = (L0 + c_neg[i] > 0) || (L0 + c_pos[i] < 0)
        ep = (L1 == -c_neg[i] || L1 == -c_pos[i]) ? :closed : :open
        push!(cands, CompressionCandidate{V}(
            :linear, (nm0.variables[i], nothing), (i, 0), :custom, ep,
            L0, L1, L1 - L0, c_neg[i], c_pos[i], strict_dom,
            strict_dom ? :unary_dominance : :none,
        ))
    end
    all_pairs = sort!(collect(union(keys(nm0.quadratic), keys(nm1.quadratic))))
    for (i, j) in all_pairs
        work += 1
        q0 = get(nm0.quadratic, (i, j), 0 // 1)
        q1 = get(nm1.quadratic, (i, j), 0 // 1)
        q0 == q1 && continue
        c_i_neg_excl = c_neg[i] - min(0 // 1, q0)
        c_i_pos_excl = c_pos[i] - max(0 // 1, q0)
        c_j_neg_excl = c_neg[j] - min(0 // 1, q0)
        unary_dom = (nm0.linear[i] + c_neg[i] > 0) || (nm0.linear[i] + c_pos[i] < 0) ||
                    (nm0.linear[j] + c_neg[j] > 0) || (nm0.linear[j] + c_pos[j] < 0)
        pair_dom = q0 > 0 && ((nm0.linear[i] + c_i_neg_excl + q0 > 0) || (nm0.linear[j] + c_j_neg_excl + q0 > 0))
        sub_rule = unary_dom ? :unary_dominance : (pair_dom ? :pair_dominance : :none)
        ep = (q1 == max(0 // 1, -nm0.linear[i] - c_i_neg_excl) || q1 == max(0 // 1, -nm0.linear[j] - c_j_neg_excl)) ? :closed : :open
        push!(cands, CompressionCandidate{V}(
            :quadratic, (nm0.variables[i], nm0.variables[j]), (i, j), :custom, ep,
            q0, q1, q1 - q0, c_i_neg_excl, c_i_pos_excl, unary_dom || pair_dom, sub_rule,
        ))
    end
    return cands, work
end

"""
    audit_compression(
        original,
        transformed=nothing;
        endpoint::Symbol=:closed,
        epsilon::Real=1 // 10,
        include_quadratic::Bool=true,
        include_negative_quadratic::Bool=false,
        chain::Bool=false,
        max_vars::Int=12,
        max_work::Int=100_000,
    ) -> CompressionAuditReport

Execute a bounded exact coefficient-compression audit comparing `original` against
`transformed` (or against the candidate model produced by [`qubolite_compression_candidates`](@ref)
when `transformed === nothing`).

All computations are strictly bounded by `max_vars` (capped at `16`) and `max_work`; no
unbounded exact global solve is ever performed.
"""
function audit_compression(
    original,
    transformed=nothing;
    endpoint::Symbol=:closed,
    epsilon::Real=1 // 10,
    include_quadratic::Bool=true,
    include_negative_quadratic::Bool=false,
    chain::Bool=false,
    max_vars::Int=12,
    max_work::Int=100_000,
)
    0 <= max_vars <= 16 || throw(ArgumentError("max_vars must be in 0..16, got $max_vars"))
    max_work >= 0 || throw(ArgumentError("max_work must be non-negative, got $max_work"))

    nm0 = _extract_normalized_bool_model(original)
    V = eltype(nm0.variables)
    n = length(nm0.variables)

    if transformed === nothing
        cand_res = qubolite_compression_candidates(
            original;
            endpoint=endpoint,
            epsilon=epsilon,
            include_quadratic=include_quadratic,
            include_negative_quadratic=include_negative_quadratic,
            chain=chain,
            max_work=max_work,
        )
        cands = cand_res.candidates
        nm1 = _extract_normalized_bool_model(cand_res.transformed_model)
        bound_work = cand_res.bound_work
        if cand_res.stop_reason !== :audited
            metrics = compression_metrics(original, cand_res.transformed_model)
            return CompressionAuditReport{V}(
                :work_limit_exceeded, :unverified, false, false, nothing, 0 // 1,
                0 // 1, 0 // 1, 0 // 1, 0, 0, 0, nothing, nothing,
                false, :none, :defer, :audit_budget_exceeded, cands, metrics,
                0, bound_work, 0, 0, bound_work,
            )
        end
    else
        nm1 = _extract_normalized_bool_model(transformed)
        nm0.variables == nm1.variables || throw(ArgumentError("original and transformed models must have the same variables"))
        cands, bound_work = _infer_diff_candidates(nm0, nm1)
    end

    metrics = compression_metrics(original, _to_qubotools_model(nm1))

    # Exact worst-case lower bound shift min_x (F(x) - F'(x)) on normalized minimization polynomial:
    lb_shift = nm0.constant - nm1.constant
    for i in 1:n
        delta_i = nm1.linear[i] - nm0.linear[i]
        delta_i > 0 && (lb_shift -= delta_i)
    end
    for (edge, q1) in nm1.quadratic
        q0 = get(nm0.quadratic, edge, 0 // 1)
        delta_q = q1 - q0
        delta_q > 0 && (lb_shift -= delta_q)
    end
    for (edge, q0) in nm0.quadratic
        haskey(nm1.quadratic, edge) && continue
        delta_q = -q0
        delta_q > 0 && (lb_shift -= delta_q)
    end

    if n > max_vars
        return CompressionAuditReport{V}(
            :variable_limit_exceeded, :unverified, false, false, nothing, lb_shift,
            0 // 1, 0 // 1, 0 // 1, 0, 0, 0, nothing, nothing,
            false, :none, :defer, :audit_budget_exceeded, cands, metrics,
            0, bound_work, 0, 0, bound_work,
        )
    end

    num_states = 1 << n
    terms_per_eval = max(1, n + length(nm0.quadratic) + length(nm1.quadratic))
    if bound_work + num_states * terms_per_eval > max_work
        return CompressionAuditReport{V}(
            :work_limit_exceeded, :unverified, false, false, nothing, lb_shift,
            0 // 1, 0 // 1, 0 // 1, 0, 0, 0, nothing, nothing,
            false, :none, :defer, :audit_budget_exceeded, cands, metrics,
            0, bound_work, 0, 0, bound_work,
        )
    end

    x_bits = zeros(Int, n)
    orig_vals = Vector{Rational{BigInt}}(undef, num_states)
    trans_vals = Vector{Rational{BigInt}}(undef, num_states)
    min_orig = 0 // 1
    min_trans = 0 // 1
    first_shift = 0 // 1
    const_shift = true
    ver_work = 0

    for mask in 0:(num_states - 1)
        for i in 1:n
            x_bits[i] = (mask >> (i - 1)) & 1
        end
        v0 = _eval_norm_bool(nm0, x_bits)
        v1 = _eval_norm_bool(nm1, x_bits)
        ver_work += terms_per_eval
        orig_vals[mask + 1] = v0
        trans_vals[mask + 1] = v1
        shift = v0 - v1
        if mask == 0
            min_orig = v0
            min_trans = v1
            first_shift = shift
        else
            v0 < min_orig && (min_orig = v0)
            v1 < min_trans && (min_trans = v1)
            shift != first_shift && (const_shift = false)
        end
    end

    orig_opt_masks = Int[]
    trans_opt_masks = Int[]
    shared_count = 0
    introduced_mask = -1
    lost_mask = -1
    worst_lifted_norm = min_orig
    opt_shift_val = nothing
    opt_shift_const = true
    rec_work = 0

    for mask in 0:(num_states - 1)
        is_o = orig_vals[mask + 1] == min_orig
        is_t = trans_vals[mask + 1] == min_trans
        is_o && push!(orig_opt_masks, mask)
        if is_t
            push!(trans_opt_masks, mask)
            rec_work += max(1, n)
            v0 = orig_vals[mask + 1]
            v0 > worst_lifted_norm && (worst_lifted_norm = v0)
            s = v0 - trans_vals[mask + 1]
            if opt_shift_val === nothing
                opt_shift_val = s
            elseif s != opt_shift_val
                opt_shift_const = false
            end
        end
        if is_o && is_t
            shared_count += 1
        elseif is_t && !is_o && introduced_mask == -1
            introduced_mask = mask
        elseif is_o && !is_t && lost_mask == -1
            lost_mask = mask
        end
    end

    orig_count = length(orig_opt_masks)
    trans_count = length(trans_opt_masks)
    if shared_count == 0
        relation = :disjoint_optimum_sets
    elseif shared_count == orig_count && shared_count == trans_count
        relation = :exact_optimum_set
    elseif shared_count == trans_count && trans_count < orig_count
        relation = :optimum_preserving_subset
    elseif shared_count == orig_count && trans_count > orig_count
        relation = :introduced_suboptimal_tie
    else
        relation = :partial_overlap_with_suboptimal
    end

    valid_lift = relation in (:exact_optimum_set, :optimum_preserving_subset)
    intro_witness = if introduced_mask == -1
        nothing
    else
        _bits_to_domain_state(nm0.domain, [((introduced_mask >> (i - 1)) & 1) for i in 1:n])
    end
    lost_witness = if lost_mask == -1
        nothing
    else
        _bits_to_domain_state(nm0.domain, [((lost_mask >> (i - 1)) & 1) for i in 1:n])
    end

    all_subsumed = !isempty(cands) && all(c -> c.strict_local_dominance, cands)
    sub_rule = if isempty(cands)
        :zero_noop
    elseif all(c -> c.subsuming_rule === :unary_dominance, cands)
        :unary_dominance
    elseif all(c -> c.subsuming_rule in (:unary_dominance, :pair_dominance), cands)
        :pair_dominance
    else
        :none
    end

    decision, missing_proof = if isempty(cands) && const_shift
        (:noop, :none)
    elseif !valid_lift
        mp = if relation === :introduced_suboptimal_tie
            :endpoint_introduces_suboptimal_ties
        elseif relation === :disjoint_optimum_sets
            :lost_all_original_optima
        else
            :partial_overlap_introduces_suboptimal_optima
        end
        (:defer, mp)
    elseif all_subsumed && sub_rule === :unary_dominance
        (:adopt_via_exact_elimination, :subsumed_by_exact_unary_elimination)
    elseif all_subsumed && sub_rule === :pair_dominance
        (:adopt_via_exact_elimination, :subsumed_by_exact_pair_contraction)
    else
        (:defer, :state_dependent_energy_shift_without_branch_exclusion)
    end

    orig_user_opt = _norm_to_user_objective(nm0, min_orig)
    trans_user_opt = _norm_to_user_objective(nm1, min_trans)
    worst_lifted_user = _norm_to_user_objective(nm0, worst_lifted_norm)
    tot_work = bound_work + ver_work + rec_work

    return CompressionAuditReport{V}(
        :audited,
        relation,
        valid_lift,
        const_shift,
        opt_shift_const ? opt_shift_val : nothing,
        lb_shift,
        orig_user_opt,
        trans_user_opt,
        worst_lifted_user,
        orig_count,
        trans_count,
        shared_count,
        intro_witness,
        lost_witness,
        all_subsumed,
        sub_rule,
        decision,
        missing_proof,
        cands,
        metrics,
        num_states,
        bound_work,
        ver_work,
        rec_work,
        tot_work,
    )
end

"""
    compression_counterexamples()

Return a named tuple of canonical exact counterexamples and comparison fixtures
for Issue `#21`:
- `endpoint_tie`: 1-variable Boolean model ``F(x_1) = x_1 \\to F'(x_1) = 0`` at Mücke et al.
  closed endpoint (`endpoint = :closed`), where ``\\operatorname{argmin} F = \\{[0]\\}``
  is retained but ``[1] \\in \\operatorname{argmin} F'`` is introduced as a suboptimal tie.
- `quadratic_endpoint_tie`: 2-variable Boolean model ``F(x_1, x_2) = -x_1 - x_2 + 3 x_1 x_2``
  compressed at `:closed` to ``Q_{12}' = 1``, introducing ``[1, 1]`` (original energy ``+1 > -1``)
  into ``\\operatorname{argmin} F'``.
- `negative_quadratic_lost_optimum`: 2-variable Boolean model ``F(x_1, x_2) = 2 x_1 + 2 x_2 - 5 x_1 x_2``
  where open-interval negative coupling compression (`endpoint = :open`, ``\\epsilon = 1//10``,
  ``Q_{12}' = -21//10``) preserves 1-bit flip dominance at ``(1, 1)`` but raises ``F'(1, 1) = +19//10 > F'(0, 0) = 0``,
  losing the unique global optimum ``[1, 1]`` (`relation === :disjoint_optimum_sets`).
- `strict_interior_subsumed`: 3-variable Boolean model where open-interval compression
  (`endpoint = :open`, ``\\epsilon = 1//2``) preserves ``\\operatorname{argmin} F' = \\operatorname{argmin} F``,
  but every compressed coefficient belongs to a variable already strictly fixable by unary dominance
  (`#14`, `prove_dominance`), which achieves strictly greater sparsification with an exact constant-shift certificate.
- `max_sense_float_exact`: `:max`-sense `:spin`-domain model with exact binary float coefficients
  (`0.5`, `1.25`, `-3.75`) audited under exact rational conversion.
"""
function compression_counterexamples()
    # 1. 1-variable closed-endpoint tie: F(x1) = x1 -> F'(x1) = 0
    m_tie = QT.Model(Dict(:x1 => 1.0), Dict{Tuple{Symbol,Symbol},Float64}(); sense=:min, domain=:bool)
    rep_tie = audit_compression(m_tie; endpoint=:closed)

    # 2. 2-variable quadratic closed-endpoint tie: F(x1, x2) = -x1 - x2 + 3 x1 x2 -> Q12' = 1
    m_qtie = QT.Model(
        Dict(:x1 => -1.0, :x2 => -1.0),
        Dict((:x1, :x2) => 3.0);
        sense=:min,
        domain=:bool,
    )
    rep_qtie = audit_compression(m_qtie; endpoint=:closed)

    # 3. 2-variable negative-quadratic open-endpoint lost optimum: F(x1, x2) = 2 x1 + 2 x2 - 5 x1 x2 -> Q12' = -21//10
    m_lost = QT.Model(
        Dict(:x1 => 2.0, :x2 => 2.0),
        Dict((:x1, :x2) => -5.0);
        sense=:min,
        domain=:bool,
    )
    rep_lost = audit_compression(
        m_lost;
        endpoint=:open,
        epsilon=1 // 10,
        include_negative_quadratic=true,
    )

    # 4. 3-variable strict interior case subsumed by #14 unary dominance:
    #    F(x1, x2, x3) = 5 x1 - x2 + 2 x3 - x1 x2 + 2 x1 x3 - 2 x2 x3
    #    Here c_1^- = -1, so L_1 + c_1^- = 5 - 1 = +4 > 0 (x1 = 0 by #14 unary dominance!).
    m_sub = QT.Model(
        Dict(:x1 => 5.0, :x2 => -1.0, :x3 => 2.0),
        Dict((:x1, :x2) => -1.0, (:x1, :x3) => 2.0, (:x2, :x3) => -2.0);
        sense=:min,
        domain=:bool,
    )
    rep_sub = audit_compression(m_sub; endpoint=:open, epsilon=1 // 2)

    # 5. Maximization + spin domain + finite Float64 exact rationalization:
    m_max = QT.Model(
        Dict(:s1 => -3.75, :s2 => 1.5),
        Dict((:s1, :s2) => 1.25);
        scale=1.5,
        offset=-0.25,
        sense=:max,
        domain=:spin,
    )
    rep_max_closed = audit_compression(m_max; endpoint=:closed)
    rep_max_open = audit_compression(m_max; endpoint=:open, epsilon=0.25)

    return (
        endpoint_tie=(model=m_tie, report=rep_tie),
        quadratic_endpoint_tie=(model=m_qtie, report=rep_qtie),
        negative_quadratic_lost_optimum=(model=m_lost, report=rep_lost),
        strict_interior_subsumed=(model=m_sub, report=rep_sub),
        max_sense_float_exact=(model=m_max, closed_report=rep_max_closed, open_report=rep_max_open),
    )
end
