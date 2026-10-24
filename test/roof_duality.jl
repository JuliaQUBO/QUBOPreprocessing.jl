@testset "optional certified roof-duality pass with strong persistency (#12)" begin
    function exact_brute_force_roof(model::QT.Model; fixed_scope=Dict{Int,Int}())
        n = length(QT.variables(model))
        dom = QT.domain(model)
        sense = QT.sense(model)
        form = QT.form(model)
        vals = dom === QT.BoolDomain ? (0, 1) : (-1, 1)
        best_e = sense === QT.Min ? Inf : -Inf
        opt_states = Vector{Vector{Int}}()
        for mask in 0:((1 << n) - 1)
            x = [((mask >> (j - 1)) & 1) == 1 ? vals[2] : vals[1] for j in 1:n]
            ok = true
            for (k, v) in fixed_scope
                if x[k] != v
                    ok = false
                    break
                end
            end
            ok || continue
            e = QT.value(x, form)
            if (sense === QT.Min && e < best_e - 1e-12) || (sense === QT.Max && e > best_e + 1e-12)
                best_e = e
                empty!(opt_states)
                push!(opt_states, x)
            elseif abs(e - best_e) <= 1e-12
                push!(opt_states, x)
            end
        end
        return best_e, opt_states
    end

    @testset "strong persistency beyond unary dominance and hybrid submodular + frustrated fixtures" begin
        # 1. 3-variable attractive spin cluster where unary dominance fixes 0 variables
        #    E(s) = 2*s1 - 2*s1*s2 - 2*s1*s3 - 2*s2*s3
        #    |h1| = 2 < |J12| + |J13| = 4, |h2| = |h3| = 0 < 4 => unary dominance fixes nothing.
        #    Roof duality strongly fixes s1 = s2 = s3 = -1 (unique optimum with energy -8).
        L3 = Dict(1 => 2.0, 2 => 0.0, 3 => 0.0)
        Q3 = Dict((1, 2) => -2.0, (1, 3) => -2.0, (2, 3) => -2.0)
        m3 = QT.Model{Int,Float64,Int}(L3, Q3; domain=:spin, sense=:min)

        ws3_dom = Workspace(m3; rules=:dominance)
        rep3_dom = propagate!(ws3_dom)
        @test rep3_dom.deductions == 0
        @test isempty(deductions(ws3_dom))

        ws3 = Workspace(m3; rules=:dominance)
        cp3 = checkpoint(ws3)
        att3 = prove_roof_duality(ws3)
        @test checkpoint(ws3) == cp3
        @test isempty(deductions(ws3))
        @test att3.stop_reason === :proved
        @test att3.method === :exact
        @test att3.max_flow == 0 // 1
        @test att3.lower_bound == -8 // 1
        @test att3.objective_bound == -8 // 1
        @test att3.fixings == [1 => -1, 2 => -1, 3 => -1]
        @test att3.certificate !== nothing
        @test verify_certificate(ws3, att3.certificate).valid
        @test certificate_guarantee(att3.certificate) === :optimum_preserving_restriction
        @test persistency(att3.certificate) === :strong
        for step in att3.certificate.steps
            @test step isa RoofDualityStep
            @test step_guarantee(step) === :optimum_preserving_restriction
            @test persistency(step) === :strong
        end

        # Single-variable prove_roof_duality overload
        att3_v1 = prove_roof_duality(ws3, 1)
        @test att3_v1.stop_reason === :proved
        @test att3_v1.fixings == [1 => -1]
        @test verify_certificate(ws3, att3_v1.certificate).valid
        @test prove_roof_duality(ws3, 1; value=1).stop_reason === :not_strict

        # Commit with apply_roof_duality!
        rep3 = apply_roof_duality!(ws3)
        @test rep3.stop_reason === :applied
        @test rep3.fixed_count == 3
        @test rep3.fixings == [1 => -1, 2 => -1, 3 => -1]
        @test verify_certificate(ws3, export_certificate(ws3)).valid

        # 2. 6-variable hybrid fixture: {1, 2, 3} attractive cluster coupled via J34 = +0.5
        #    to a frustrated antiferromagnetic triangle {4, 5, 6} (J45 = J56 = J46 = +1.0).
        #    Whole-graph is NOT gauge-submodular (triangle {4,5,6} is frustrated), and unary
        #    dominance fixes 0 variables. Roof duality pushes flow 0.5 across (3,4) and
        #    strongly fixes s1 = s2 = s3 = -1 while leaving {4, 5, 6} unfixed.
        L6 = Dict(1 => 2.0, 2 => 0.0, 3 => 0.0, 4 => 0.0, 5 => 0.0, 6 => 0.0)
        Q6 = Dict(
            (1, 2) => -2.0, (1, 3) => -2.0, (2, 3) => -2.0,
            (3, 4) => 0.5,
            (4, 5) => 1.0, (5, 6) => 1.0, (4, 6) => 1.0,
        )
        m6 = QT.Model{Int,Float64,Int}(L6, Q6; domain=:spin, sense=:min)
        best6, opts6 = exact_brute_force_roof(m6)
        @test all(x[1] == -1 && x[2] == -1 && x[3] == -1 for x in opts6)
        # Frustrated triangle variables 5, 6 each take both -1 and +1 across optima
        for u in 5:6
            @test any(x[u] == -1 for x in opts6)
            @test any(x[u] == 1 for x in opts6)
        end

        ws6 = Workspace(m6; rules=:dominance)
        @test propagate!(ws6).deductions == 0
        rep6 = apply_roof_duality!(ws6)
        @test rep6.stop_reason === :applied
        @test rep6.fixed_count == 3
        @test rep6.fixings == [1 => -1, 2 => -1, 3 => -1]
        @test rep6.max_flow == 1 // 2
        @test rep6.objective_bound <= Rational{BigInt}(best6)
        @test verify_certificate(ws6, export_certificate(ws6)).valid

        # Export conditioned model on remaining variables {4, 5, 6} and reconstruct all optima
        exp6 = materialize(ws6)
        sub6 = export_model(exp6)
        @test QT.variables(sub6) == [4, 5, 6]
        best_sub6, opts_sub6 = exact_brute_force_roof(sub6)
        @test best_sub6 == best6
        for y in opts_sub6
            rec = reconstruct(exp6, y)
            @test rec.state in opts6
            @test QT.value(rec.state, QT.form(m6)) == best6
        end
    end

    @testset "multiple-optimum ties leave variables unfixed in strong mode" begin
        # 1. Symmetric attractive pair: E(s1, s2) = -2*s1*s2 -> optima (-1,-1) and (+1,+1)
        m_sym = QT.Model{Int,Float64,Int}(Dict(1 => 0.0, 2 => 0.0), Dict((1, 2) => -2.0); domain=:spin, sense=:min)
        ws_sym = Workspace(m_sym)
        att_sym = prove_roof_duality(ws_sym)
        @test att_sym.stop_reason === :no_persistency
        @test att_sym.certificate === nothing
        @test isempty(att_sym.fixings)
        @test att_sym.lower_bound == -2 // 1

        # 2. Non-zero-field 3-optimum tie: E(s1, s2) = s1 + s2 + s1*s2
        #    C_base = -3, max_flow = 2 -> exact optimum lower_bound = -1,
        #    optima are (-1,-1), (-1,+1), (+1,-1); strong mode fixes neither variable.
        m_tie = QT.Model{Int,Float64,Int}(Dict(1 => 1.0, 2 => 1.0), Dict((1, 2) => 1.0); domain=:spin, sense=:min)
        ws_tie = Workspace(m_tie)
        att_tie = prove_roof_duality(ws_tie)
        @test att_tie.stop_reason === :no_persistency
        @test att_tie.certificate === nothing
        @test att_tie.max_flow == 2 // 1
        @test att_tie.lower_bound == -1 // 1
        @test att_tie.objective_bound == -1 // 1
        @test isempty(att_tie.fixings)
        rep_tie = apply_roof_duality!(ws_tie)
        @test rep_tie.stop_reason === :no_persistency
        @test rep_tie.fixed_count == 0
    end

    @testset "domains, senses, scales, offsets, near-cancelling capacities, and large magnitudes" begin
        L_base = Dict(:a => 2.0, :b => 0.0, :c => 0.0)
        Q_base = Dict((:a, :b) => -2.0, (:a, :c) => -2.0, (:b, :c) => -2.0)
        for dom in (:spin, :bool), sense in (:min, :max), scale in (1.0, 2.5, -3.0), offset in (0.0, -3.5)
            dir = (sense === :min ? 1.0 : -1.0) * (scale > 0 ? 1.0 : -1.0)
            L_s = Dict(k => dir * v for (k, v) in L_base)
            Q_s = Dict(k => dir * v for (k, v) in Q_base)
            m_spin = QT.Model{Symbol,Float64,Int}(L_s, Q_s; scale=scale, offset=offset, domain=:spin, sense=sense)
            m = if dom === :spin
                m_spin
            else
                ws_tmp = Workspace(m_spin)
                export_model(materialize(ws_tmp, domain_map(ws_tmp; domain=:bool)))
            end
            ws = Workspace(m; rules=:dominance)
            expected_val = dom === :spin ? -1 : 0
            best_e, _ = exact_brute_force_roof(m)

            att = prove_roof_duality(ws)
            @test att.stop_reason === :proved
            @test Dict(att.fixings)[:a] == expected_val
            @test Dict(att.fixings)[:b] == expected_val
            @test Dict(att.fixings)[:c] == expected_val
            if sense === :min
                @test att.objective_bound <= Rational{BigInt}(best_e)
            else
                @test att.objective_bound >= Rational{BigInt}(best_e)
            end
            @test verify_certificate(ws, att.certificate).valid

            rep = apply_roof_duality!(ws)
            @test rep.stop_reason === :applied
            @test rep.fixed_count == 3
            @test verify_certificate(ws, export_certificate(ws)).valid
        end

        # Zero scale abstains cleanly with :zero_scale
        m_zero = QT.Model{Int,Float64,Int}(Dict(1 => 2.0, 2 => 0.0), Dict((1, 2) => -2.0); scale=0.0, domain=:spin, sense=:min)
        ws_zero = Workspace(m_zero)
        @test prove_roof_duality(ws_zero).stop_reason === :zero_scale
        @test prove_roof_duality(ws_zero, 1).stop_reason === :zero_scale
        @test apply_roof_duality!(ws_zero).stop_reason === :zero_scale

        # Near-cancelling capacities: h1 = 1.0, J12 = -0.5, J13 = -prevfloat(0.5),
        # h2 = -0.5, h3 = -prevfloat(0.5) (or J23 = -2.0 so unary dominance on 1 has |h1|=1 == 0.5+prevfloat(0.5) + ...).
        # Let's construct: h1 = 1.0, h2 = -0.5, h3 = -prevfloat(0.5), J12 = 0.5, J13 = prevfloat(0.5), J23 = -2.0.
        # On 1: |h1| = 1.0, |J12| + |J13| = 0.5 + prevfloat(0.5), and add J14 = -0.25, J24 = -1.0, J34 = -1.0
        # wait: simplest near-cancelling flow saturation:
        # S -> bar_x1 has cap h1 = 1.0; bar_x1 -> x2 -> T has cap 0.5 (h2 = +0.5, J12 = +0.5);
        # bar_x1 -> x3 -> T has cap prevfloat(0.5) (h3 = +prevfloat(0.5), J13 = +prevfloat(0.5)).
        # After pushing 0.5 along S -> bar_x1 -> x2 -> T and prevfloat(0.5) along S -> bar_x1 -> x3 -> T,
        # the remaining residual capacity on S -> bar_x1 is exactly 1.0 - 0.5 - prevfloat(0.5) = 2^-53 > 0!
        # Meanwhile add J14 = -0.25, J24 = -0.25 (with h4 = 0) so |h1| = 1.0 < 0.5 + prevfloat(0.5) + 0.25 (unary dominance fails!),
        # and J14 = -0.25 goes from bar_x1 -> bar_x4 with no path from bar_x4 to T!
        # Thus residual capacity 2^-53 > 0 reaches bar_x1 and bar_x4 from S (and x1, x4 reach T), strongly fixing s1 = s4 = -1!
        L_near = Dict(1 => 1.0, 2 => 0.5, 3 => prevfloat(0.5), 4 => 0.0)
        Q_near = Dict((1, 2) => 0.5, (1, 3) => prevfloat(0.5), (1, 4) => -0.25)
        m_near = QT.Model{Int,Float64,Int}(L_near, Q_near; domain=:spin, sense=:min)
        ws_near = Workspace(m_near; rules=:dominance)
        @test propagate!(ws_near).deductions == 0
        att_near = prove_roof_duality(ws_near)
        @test att_near.stop_reason === :proved
        @test att_near.max_flow == 2 * (Rational{BigInt}(0.5) + Rational{BigInt}(prevfloat(0.5)))
        @test 2 * Rational{BigInt}(1.0) - att_near.max_flow == Rational{BigInt}(1) // (BigInt(2)^53)
        @test Dict(att_near.fixings)[1] == -1
        @test Dict(att_near.fixings)[4] == -1
        @test verify_certificate(ws_near, att_near.certificate).valid

        # Large magnitude floatmax(Float64) capacities without Float64 Inf overflow
        big_v = floatmax(Float64)
        L_big = Dict(1 => big_v, 2 => 0.0, 3 => 0.0)
        Q_big = Dict((1, 2) => -big_v, (1, 3) => -big_v, (2, 3) => -big_v)
        m_big = QT.Model{Int,Float64,Int}(L_big, Q_big; domain=:spin, sense=:min)
        ws_big = Workspace(m_big)
        att_big = prove_roof_duality(ws_big)
        @test att_big.stop_reason === :proved
        @test att_big.fixings == [1 => -1, 2 => -1, 3 => -1]
        @test verify_certificate(ws_big, att_big.certificate).valid
    end

    @testset "DomainGaugeMap transport, scope invalidation, and tamper detection" begin
        L3 = Dict(1 => 2.0, 2 => 0.0, 3 => 0.0)
        Q3 = Dict((1, 2) => -2.0, (1, 3) => -2.0, (2, 3) => -2.0)
        m3 = QT.Model{Int,Float64,Int}(L3, Q3; offset=1.25, scale=2.0, domain=:spin, sense=:min)
        ws = Workspace(m3; rules=:dominance)
        dmap = domain_map(ws; domain=:bool, gauge=[-1, 1, -1])

        att_map = prove_roof_duality(ws; map=dmap)
        @test att_map.stop_reason === :proved
        # s = (-1, -1, -1) -> gauged spin t = (1, -1, 1) -> bool y = (1, 0, 1)
        @test att_map.fixings == [1 => 1, 2 => 0, 3 => 1]
        @test verify_certificate(ws, att_map.certificate; map=dmap).valid

        # Unmapped certificate transported into dmap
        att_raw = prove_roof_duality(ws)
        cert_tr = transport_certificate(ws, att_raw.certificate, dmap)
        @test verify_certificate(ws, cert_tr; map=dmap).valid

        # Tamper checks on RoofDualityStep
        s1 = att_raw.certificate.steps[1]::RoofDualityStep
        s2 = att_raw.certificate.steps[2]::RoofDualityStep
        s3 = att_raw.certificate.steps[3]::RoofDualityStep

        # 1. Tamper roof_lower
        bad_rlo = RoofDualityStep(s1.variable, s1.value, s1.roof_lower + 1, s1.max_flow, s1.flow_edges, s1.batch_fixings, s1.batch_index, s1.constant, s1.predecessors, s1.method, s1.scope_length, s1.persistency)
        cert_bad_rlo = DominanceCertificate(att_raw.certificate.generation, att_raw.certificate._scope_checkpoint, att_raw.certificate.assumptions, (bad_rlo, s2, s3), att_raw.certificate._source, nothing)
        @test !verify_certificate(ws, cert_bad_rlo).valid

        # 2. Tamper max_flow (violates flow conservation at source/sink)
        bad_mf1 = RoofDualityStep(s1.variable, s1.value, s1.roof_lower + 1, s1.max_flow + 1, s1.flow_edges, s1.batch_fixings, s1.batch_index, s1.constant, s1.predecessors, s1.method, s1.scope_length, s1.persistency)
        bad_mf2 = RoofDualityStep(s2.variable, s2.value, s2.roof_lower + 1, s2.max_flow + 1, s2.flow_edges, s2.batch_fixings, s2.batch_index, s2.constant, s2.predecessors, s2.method, s2.scope_length, s2.persistency)
        bad_mf3 = RoofDualityStep(s3.variable, s3.value, s3.roof_lower + 1, s3.max_flow + 1, s3.flow_edges, s3.batch_fixings, s3.batch_index, s3.constant, s3.predecessors, s3.method, s3.scope_length, s3.persistency)
        cert_bad_mf = DominanceCertificate(att_raw.certificate.generation, att_raw.certificate._scope_checkpoint, att_raw.certificate.assumptions, (bad_mf1, bad_mf2, bad_mf3), att_raw.certificate._source, nothing)
        @test verify_certificate(ws, cert_bad_mf).stop_reason === :invalid_flow

        # 3. Tamper constant on step 2
        bad_c2 = RoofDualityStep(s2.variable, s2.value, s2.roof_lower, s2.max_flow, s2.flow_edges, s2.batch_fixings, s2.batch_index, s2.constant + 1, s2.predecessors, s2.method, s2.scope_length, s2.persistency)
        cert_bad_c2 = DominanceCertificate(att_raw.certificate.generation, att_raw.certificate._scope_checkpoint, att_raw.certificate.assumptions, (s1, bad_c2, s3), att_raw.certificate._source, nothing)
        @test verify_certificate(ws, cert_bad_c2).stop_reason === :invalid_constant

        # 4. Tamper value on single-step certificate (claiming s1 = +1 instead of -1)
        att_single = prove_roof_duality(ws, 1)
        ss = att_single.certificate.steps[1]::RoofDualityStep
        bad_val = RoofDualityStep(ss.variable, 1, ss.roof_lower, ss.max_flow, ss.flow_edges, (1 => 1,), 1, ss.constant, ss.predecessors, ss.method, ss.scope_length, ss.persistency)
        cert_bad_val = DominanceCertificate(att_single.certificate.generation, att_single.certificate._scope_checkpoint, att_single.certificate.assumptions, (bad_val,), att_single.certificate._source, nothing)
        @test verify_certificate(ws, cert_bad_val).stop_reason === :invalid_bound

        # Scope sensitivity: adding an assumption after apply_roof_duality! rolls back the roof-duality deductions
        ws_sc = Workspace(m3; rules=:dominance)
        rep_sc = apply_roof_duality!(ws_sc; candidates=[1, 2])
        @test rep_sc.fixed_count == 2
        cert_sc = export_certificate(ws_sc)
        @test verify_certificate(ws_sc, cert_sc).valid
        # Now assume variable 3 = +1: since RoofDualityStep is scope-sensitive, assume! rolls back prior roof-duality deductions
        assume!(ws_sc, 3, 1)
        @test verify_certificate(ws_sc, cert_sc).stop_reason === :stale_scope
        @test assumptions(ws_sc) == [3 => 1]
        @test isempty(deductions(ws_sc))

        # Stale generation rejected after reset!
        reset!(ws_sc, m3)
        @test verify_certificate(ws_sc, cert_sc).stop_reason === :stale_generation
    end

    @testset "budgets, rollback on interrupted commit, and cost comparison vs dominance" begin
        L6 = Dict(1 => 2.0, 2 => 0.0, 3 => 0.0, 4 => 0.0, 5 => 0.0, 6 => 0.0)
        Q6 = Dict(
            (1, 2) => -2.0, (1, 3) => -2.0, (2, 3) => -2.0,
            (3, 4) => 0.5,
            (4, 5) => 1.0, (5, 6) => 1.0, (4, 6) => 1.0,
        )
        m6 = QT.Model{Int,Float64,Int}(L6, Q6; domain=:spin, sense=:min)
        ws6 = Workspace(m6; rules=:dominance)
        cp0 = checkpoint(ws6)

        # Tight max_work during graph construction or flow rolls back cleanly
        rep_w = apply_roof_duality!(ws6; max_work=3)
        @test rep_w.stop_reason === :work_limit
        @test rep_w.fixed_count == 0
        @test checkpoint(ws6) == cp0

        # Tight max_exact_work rolls back cleanly
        rep_e = apply_roof_duality!(ws6; max_exact_work=2)
        @test rep_e.stop_reason === :verification_limit
        @test rep_e.fixed_count == 0
        @test checkpoint(ws6) == cp0

        # Tight max_work that allows graph + flow + reachability (38 visits) but interrupts _fix! commit rolls back partial fixes
        att6 = prove_roof_duality(ws6)
        pre_commit_visits = att6.graph_work + att6.flow_work + att6.verification_work
        rep_mid = apply_roof_duality!(ws6; max_work=pre_commit_visits + 2)
        @test rep_mid.stop_reason === :work_limit
        @test rep_mid.fixed_count == 0
        @test checkpoint(ws6) == cp0
        @test isempty(deductions(ws6))

        # Phase-separated cost accounting and memory comparison vs simple dominance
        # across sparse hybrid, dense attractive, and frustrated no-benefit fixtures
        ws_dom = Workspace(m6; rules=:dominance)
        r_dom = propagate!(ws_dom)
        r_roof = apply_roof_duality!(ws6)
        @test r_dom.deductions == 0
        @test r_roof.fixed_count == 3
        @test r_roof.graph_work > 0
        @test r_roof.flow_work > 0
        @test r_roof.verification_work > 0
        @test r_roof.materialization_work > 0
        @test r_roof.edge_visits == r_roof.graph_work + r_roof.flow_work + r_roof.verification_work + r_roof.materialization_work
        @test r_roof.edge_visits > r_dom.edge_visits

        # Dense attractive K_8 with field on vertex 1 vs frustrated zero-field K_8 (no-benefit)
        L_dense = Dict(i => (i == 1 ? 3.0 : 0.0) for i in 1:8)
        Q_dense_attr = Dict((i, j) => -1.0 for i in 1:8 for j in (i + 1):8)
        Q_dense_frust = Dict((i, j) => 1.0 for i in 1:8 for j in (i + 1):8)
        m_dense_attr = QT.Model{Int,Float64,Int}(L_dense, Q_dense_attr; domain=:spin, sense=:min)
        m_dense_frust = QT.Model{Int,Float64,Int}(Dict(i => 0.0 for i in 1:8), Q_dense_frust; domain=:spin, sense=:min)

        ws_da_dom = Workspace(m_dense_attr; rules=:dominance)
        r_da_dom = propagate!(ws_da_dom)
        @test r_da_dom.deductions == 0

        ws_da_roof = Workspace(m_dense_attr; rules=:dominance)
        bytes_roof_da = @allocated r_da_roof = apply_roof_duality!(ws_da_roof)
        @test r_da_roof.stop_reason === :applied
        @test r_da_roof.fixed_count == 8
        @test bytes_roof_da > 0

        ws_df_roof = Workspace(m_dense_frust; rules=:dominance)
        r_df_roof = apply_roof_duality!(ws_df_roof)
        @test r_df_roof.stop_reason === :no_persistency
        @test r_df_roof.fixed_count == 0
        @test r_df_roof.graph_work > 0
    end
end
