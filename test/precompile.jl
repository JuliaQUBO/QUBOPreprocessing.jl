@testset "bounded productive precompile workload (#100)" begin
    QP = QUBOPreprocessing
    models = QP._precompile_models()
    @test length(models) == 9
    @test maximum(QT.dimension(m) for m in models) == 20
    @test QT.dimension(models.block) == 5
    @test all(QT.dimension(m) <= 20 for m in models)

    run = QP._precompile_budgeted_workload(models)
    @test run.default_report.stop_reason === :solved
    @test run.default_report.residual_variables == 0
    @test length(run.schedules) == 6
    glass_reports = filter(r -> r.initial_variables == 20, run.schedules)
    @test length(glass_reports) == 2
    for report in glass_reports
        @test report.stop_reason === :fixpoint
        @test report.residual_variables == 18
        @test Set(f.family for f in report.families) ==
            Set((:cheap, :roof_duality, :submodular_cut, :maxcut, :blocks, :roof_scc, :probing))
        @test all(f.calls >= 1 for f in report.families)
    end
    @test all(r -> r.stop_reason === :solved, filter(r -> r.initial_variables == 7, run.schedules))
    @test any(r -> any(f -> f.family === :roof_scc && f.freed > 0, r.families), run.schedules)
    @test run.roof.fixed_count == 3
    @test all(r -> r.fixed_count == 6, run.submodular)
    @test all(r -> r.deductions == 1 && r.triangle_deductions > 0, run.maxcut)
    @test run.block.stop_reason === :applied && run.block.changed == 5
    @test run.probing.deductions == 3

    # These independent path guards prevent a fixture edit from silently warming
    # two Float64 paths while leaving the exact witness methods cold.
    for (idx, m) in enumerate((models.probing, models.exact_witness))
        ws = Workspace(m; rules=:mixed, integerize_scale=false)
        float_problem = QP._try_build_float_spin_subproblem(ws, collect(1:QT.dimension(m)))
        @test (float_problem !== nothing) == (idx == 1)
        plain, limited = run.witnesses[idx]
        @test plain == limited == [-1, 1, 1]
    end

    # Independently enumerate only the <=6-variable productive fixtures. Proofs
    # must replay and any residual optimizer must lift to an original optimizer.
    function tiny_optimum(model)
        n = QT.dimension(model)
        n <= 6 || throw(ArgumentError("precompile test oracle is limited to six variables"))
        R = Rational{BigInt}
        _, linear, quadratic, scale, offset = QT.form(model, :dict; sense=:min, domain=QT.domain(model))
        low = QT.domain(model) === QT.BoolDomain ? 0 : -1
        best = nothing
        states = Vector{Int}[]
        for mask in 0:((1 << n) - 1)
            state = [iszero(mask & (1 << (i-1))) ? low : 1 for i in 1:n]
            value = R(scale) * (R(offset) +
                sum((R(v) * state[i] for (i,v) in linear); init=zero(R)) +
                sum((R(v) * state[i] * state[j] for ((i,j),v) in quadratic); init=zero(R)))
            if best === nothing || value < best
                best = value
                empty!(states)
                push!(states, state)
            elseif value == best
                push!(states, state)
            end
        end
        return best, states
    end
    for (m, reduce!) in ((models.roof, ws -> apply_roof_duality!(ws)),
                        (models.submodular, ws -> apply_submodular_cut!(ws)),
                        (models.maxcut, ws -> apply_maxcut!(ws, 1, 2)),
                        (models.block, ws -> eliminate_block!(ws, collect(1:5))),
                        (models.probing, ws -> probe_variables!(ws; order=:coercive, max_rounds=2)))
        ws = Workspace(m; rules=:mixed)
        reduce!(ws)
        cert = export_certificate(ws)
        @test cert !== nothing && !isempty(cert.steps)
        @test verify_certificate(ws, cert).valid
        optimum, _ = tiny_optimum(m)
        result = materialize(ws; coefficient_type=Rational{BigInt})
        residual = export_model(result)
        # Enumerate the residual's stored domain; do not silently cast its states.
        _, minimizers = tiny_optimum(residual)
        @test all(y -> Rational{BigInt}(reconstruct(result, y).energy.value) == optimum, minimizers)
    end
end
