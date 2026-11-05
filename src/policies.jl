# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    PolicyScheduleReport

Versioned report from [`schedule!`](@ref). `policy`/`policy_version` identify the
algorithm, `settings` retain its effective options and dispatch dimensions,
and `families` aggregate calls, seconds, variables removed (`freed`) and last
stop reasons. `deductions` counts removed variables. `skipped_families` are
disabled by the selected policy, not claimed to be at a fixpoint. Timing covers
scheduling only; import, materialization and independent replay are separate.
For legacy policies, `passes` counts entered expensive-family outer rounds;
the initial reductions call is present in `families` even when `passes == 0`.
"""
struct PolicyScheduleReport
    generation::Generation
    policy::Symbol
    policy_version::Int
    settings::NamedTuple
    stop_reason::Symbol
    passes::Int
    elapsed_s::Float64
    initial_variables::Int
    residual_variables::Int
    deductions::Int
    families::Vector{BudgetedFamilyRun}
    skipped_families::Vector{Symbol}
end
generation(r::PolicyScheduleReport) = r.generation

# Frozen gates from benchmark 52940e96 and QUBOLib 971d449c. Dimensions are
# sampled once, never recomputed after productive passes.
function _legacy_policy_settings(policy, n, m)
    ungated = policy === :legacy_middle
    return (initial_variables=n, initial_edges=m,
            tie_break=:low, probe_order=:coercive, double_probe=false, contract_relations=false,
            relation_work_budget=(ungated || n <= 500) ? typemax(Int) :
                (m > 15_000 ? 25_000 : (m > 5_000 ? 75_000 : typemax(Int))),
            enable_blocks=ungated || (n <= 1_500 && m <= 10_000),
            enable_flow=ungated || !(m > 10_000 && n > 500),
            enable_probing=m <= 5_000 && n <= 500,
            max_candidates=min(n, 100), probe_rounds=n <= 100 ? 8 : 1,
            max_trial_fixes=n <= 100 ? 512 : 64,
            probe_work=n <= 100 ? 2_000_000 : 100_000,
            outer_rounds=policy === :legacy_census && m <= 5_000 && n <= 500 ? 8 : 1)
end

# The callback seam permits independent call-order tests without constructing
# large models. run(family) returns the number of variables removed.
function _run_legacy_policy!(run, alive, policy, settings)
    run(:reductions)
    rounds = 0
    post_probe_ded = 0
    for iter in 1:settings.outer_rounds
        alive() && settings.enable_flow || break
        rounds += 1
        round_ded = run(:roof_duality)
        alive() && (round_ded += run(:submodular_cut))
        alive() && (round_ded += run(:maxcut))
        if alive() && (policy !== :legacy_census || round_ded > 0)
            run(:reductions)
        end
        if policy === :legacy_census && iter > 1 && round_ded == 0 && post_probe_ded == 0
            break
        end
        pr_new = 0
        post_probe_ded = 0
        if alive() && settings.enable_probing
            pr_new = run(:probing)
            round_ded += pr_new
            if alive() && (policy !== :legacy_census || pr_new > 0)
                post_probe_ded = run(:reductions)
                round_ded += post_probe_ded
            end
        end
        round_ded > 0 || break
    end
    return rounds
end

"""
    schedule!(ws; policy=:legacy_benchmark, allow_weak=false, time_limit=nothing,
              input_edges=nothing, kwargs...)

Package-owned explicit policy dispatch. `:legacy_benchmark` preserves the single
historical benchmark sequence, `:legacy_middle` lifts its flow/block/relation
gates but retains the probing gate, and `:legacy_census` preserves the separate
historical census loop of up to eight rounds. These return `:policy_complete`,
not an all-family fixpoint claim. Dimensions are the workspace's original graph;
`input_edges` can retain a source representation's edge count including explicit
zero terms (the historical benchmark used `length(raw.Q)`).

`:cheap` runs dominance and low-degree elimination only and returns
`:cheap_quiescent` on completion. Relations, star-triangle, blocks, flow,
Max-Cut and probing are explicitly skipped. This makes no expensive-family
quiescence or performance claim.

`:budgeted` requires `time_limit` and forwards its other options to
[`schedule_budgeted!`](@ref), whose defaults are unchanged. Time limits are
rejected for the untimed legacy/cheap policies instead of silently ignored.
No policy implies a recommended default replacement for a measured workload.
"""
function schedule!(ws::Workspace; policy::Symbol=:legacy_benchmark,
                   allow_weak::Bool=false, time_limit=nothing, input_edges=nothing,
                   on_family=nothing, kwargs...)
    policy in (:legacy_benchmark, :legacy_middle, :legacy_census, :cheap, :budgeted) ||
        throw(ArgumentError("unknown preprocessing policy: $policy"))
    free_count() = count(==(Int8(2)), ws._state.fixed)
    n0 = free_count()
    t0 = time_ns()
    if policy === :budgeted
        input_edges === nothing || throw(ArgumentError("input_edges is only for legacy policies"))
        time_limit === nothing && throw(ArgumentError("budgeted policy requires time_limit"))
        defaults = (enable_probing=true, max_block_size=12, probe_rounds=8,
                    guaranteed_relation_work=75_000, tie_break=:low,
                    double_probe=false, contract_relations=false)
        all(k in keys(defaults) for k in keys(kwargs)) || throw(ArgumentError("unknown budgeted option"))
        options = merge(defaults, (; kwargs...))
        report = schedule_budgeted!(ws; time_limit, allow_weak, on_family, options...)
        settings = (; allow_weak, time_limit=Float64(time_limit), observed=on_family !== nothing, options...)
        skipped = options.enable_probing ? Symbol[] : [:probing]
        return PolicyScheduleReport(generation(ws), policy, 1, settings, report.stop_reason,
            report.passes, report.elapsed_s, n0, free_count(), n0-free_count(), report.families, skipped)
    end
    time_limit === nothing || throw(ArgumentError("$policy has no time limit"))
    on_family === nothing || throw(ArgumentError("on_family is supported only by the budgeted policy"))
    isempty(kwargs) || throw(ArgumentError("unexpected options for $policy"))
    input_edges === nothing || (input_edges isa Integer && !(input_edges isa Bool) && 0 <= input_edges <= typemax(Int)) ||
        throw(ArgumentError("input_edges must be a nonnegative machine-sized integer"))
    if policy === :cheap
        input_edges === nothing || throw(ArgumentError("input_edges is only for legacy policies"))
        report = schedule_reductions!(ws; allow_weak_dominance=allow_weak,
            enable_relations=false, enable_star_triangle=false, enable_blocks=false)
        elapsed = (time_ns()-t0)/1e9
        stop = report.stop_reason === :quiescent ? :cheap_quiescent : report.stop_reason
        return PolicyScheduleReport(generation(ws), policy, 1, (; allow_weak), stop, 1,
            elapsed, n0, free_count(), n0-free_count(),
            [BudgetedFamilyRun(:cheap, 1, elapsed, n0-free_count(), report.stop_reason)],
            [:relations, :star_triangle, :blocks, :roof_duality, :submodular_cut, :maxcut, :roof_scc, :probing])
    end
    gates = _legacy_policy_settings(policy, length(original_variables(ws)),
                                    input_edges === nothing ? ws._state.initial_edges : Int(input_edges))
    families = BudgetedFamilyRun[]
    function run(family)
        before = free_count()
        start = time_ns()
        rep = if family === :reductions
            schedule_reductions!(ws; allow_weak_dominance=allow_weak, allow_weak_relations=allow_weak,
                enable_star_triangle=true, enable_blocks=gates.enable_blocks,
                relation_work_budget=gates.relation_work_budget)
        elseif family === :roof_duality
            apply_roof_duality!(ws)
        elseif family === :submodular_cut
            apply_submodular_cut!(ws; allow_weak)
        elseif family === :maxcut
            apply_maxcut!(ws; allow_weak)
        else
            probe_variables!(ws; max_candidates=gates.max_candidates, max_rounds=gates.probe_rounds,
                max_trial_fixes=gates.max_trial_fixes, max_work=gates.probe_work,
                max_exact_work=gates.probe_work, order=:coercive)
        end
        freed = before-free_count()
        elapsed = (time_ns()-start)/1e9
        index = findfirst(f -> f.family === family, families)
        if index === nothing
            push!(families, BudgetedFamilyRun(family, 1, elapsed, freed, rep.stop_reason))
        else
            old = families[index]
            families[index] = BudgetedFamilyRun(family, old.calls+1, old.time_s+elapsed, old.freed+freed, rep.stop_reason)
        end
        return freed
    end
    passes = _run_legacy_policy!(run, () -> free_count() > 0, policy, gates)
    skipped = Symbol[:roof_scc]
    gates.enable_blocks || push!(skipped, :blocks)
    gates.enable_flow || append!(skipped, [:roof_duality, :submodular_cut, :maxcut])
    gates.enable_probing || push!(skipped, :probing)
    return PolicyScheduleReport(generation(ws), policy, 1, (; allow_weak, gates...),
        free_count() == 0 ? :solved : :policy_complete, passes, (time_ns()-t0)/1e9,
        n0, free_count(), n0-free_count(), families, skipped)
end
