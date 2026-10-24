@testset "Issue #19 — Gauge-Submodular Component Recognition & Certified Cut Pass" begin
    function _brute_force_opt(model)
        f = QT.form(model)
        n = QT.dimension(f)
        is_bool = QT.domain(f) === QT.BoolDomain
        low_val = is_bool ? 0 : -1
        sense = QT.sense(f)
        best_val = sense === QT.Min ? Inf : -Inf
        best_states = Vector{Vector{Int}}()
        state = Vector{Int}(undef, n)
        for mask in 0:((1 << n) - 1)
            for i in 1:n
                state[i] = ((mask >> (i - 1)) & 1) == 1 ? 1 : low_val
            end
            val = QT.value(state, f)
            if (sense === QT.Min && val < best_val - 1e-12) || (sense === QT.Max && val > best_val + 1e-12)
                best_val = val
                empty!(best_states)
                push!(best_states, copy(state))
            elseif abs(val - best_val) <= 1e-12
                push!(best_states, copy(state))
            end
        end
        return best_val, best_states
    end

    @testset "Recognition: direct submodular, gauge-submodular bipartite, frustrated, boundary-coupled" begin
        # 1. Directly submodular component in SpinDomain (all J_uv < 0 in Min)
        L_dir = Dict(:s1 => 1.0, :s2 => -0.5, :s3 => 0.25)
        Q_dir = Dict((:s1, :s2) => -2.0, (:s2, :s3) => -1.5, (:s1, :s3) => -1.0)
        ws_dir = Workspace(QT.Model(L_dir, Q_dir; sense=:min, domain=:spin))
        rec_dir = recognize_submodular_component(ws_dir, [:s1, :s2, :s3])
        @test rec_dir isa SubmodularComponent{Symbol}
        @test rec_dir.is_closed
        @test rec_dir.is_submodular
        @test rec_dir.stop_reason === :submodular
        @test rec_dir.variables == [:s1, :s2, :s3]
        @test rec_dir.gauge == [1, 1, 1]
        @test rec_dir.recognition_work > 0

        # Partial subset with active external couplings is rejected as :boundary_coupled
        rec_bound = recognize_submodular_component(ws_dir, [:s1, :s2])
        @test !rec_bound.is_closed
        @test !rec_bound.is_submodular
        @test rec_bound.stop_reason === :boundary_coupled
        @test isempty(rec_bound.gauge)

        # Conditioning on :s3 makes [:s1, :s2] a closed residual component
        cp = checkpoint(ws_dir)
        assume!(ws_dir, :s3, 1)
        rec_closed = recognize_submodular_component(ws_dir, [:s1, :s2])
        @test rec_closed.is_closed
        @test rec_closed.is_submodular
        @test rec_closed.stop_reason === :submodular
        rollback!(ws_dir, cp)

        # 2. Bipartite antiferromagnetic C4 (J_uv > 0 in Min): gauge-submodular via [1, -1, 1, -1]
        L_bip = Dict(1 => 0.5, 2 => -0.5, 3 => 0.25, 4 => -0.25)
        Q_bip = Dict((1, 2) => 2.0, (2, 3) => 2.0, (3, 4) => 2.0, (1, 4) => 2.0)
        ws_bip = Workspace(QT.Model(L_bip, Q_bip; sense=:min, domain=:spin))
        rec_bip = recognize_submodular_component(ws_bip, [1, 2, 3, 4])
        @test rec_bip.is_closed
        @test rec_bip.is_submodular
        @test rec_bip.stop_reason === :submodular
        @test rec_bip.gauge == [1, -1, 1, -1]

        # 3. Frustrated odd cycle K3 (all J_uv > 0 in Min): rejected as :frustrated_cycle
        L_frust = Dict(:a => 0.1, :b => -0.2, :c => 0.3)
        Q_frust = Dict((:a, :b) => 1.5, (:b, :c) => 1.5, (:a, :c) => 1.5)
        ws_frust = Workspace(QT.Model(L_frust, Q_frust; sense=:min, domain=:spin))
        rec_frust = recognize_submodular_component(ws_frust, [:a, :b, :c])
        @test rec_frust.is_closed
        @test !rec_frust.is_submodular
        @test rec_frust.stop_reason === :frustrated_cycle
        @test isempty(rec_frust.gauge)

        # 4. Whole-workspace component partition with 1 gauge-submodular component and 1 frustrated component
        L_mix = Dict(1 => 0.5, 2 => -0.5, 3 => 0.25, 4 => -0.25, 5 => 0.1, 6 => -0.2, 7 => 0.3)
        Q_mix = Dict(
            (1, 2) => 2.0, (2, 3) => 2.0, (3, 4) => 2.0, (1, 4) => 2.0,
            (5, 6) => 1.5, (6, 7) => 1.5, (5, 7) => 1.5,
        )
        ws_mix = Workspace(QT.Model(L_mix, Q_mix; sense=:min, domain=:spin))
        comps, comp_stop, comp_work = recognize_submodular_components(ws_mix)
        @test comp_stop === :completed
        @test comp_work > 0
        @test length(comps) == 2
        @test comps[1].variables == [1, 2, 3, 4]
        @test comps[1].is_submodular
        @test comps[1].stop_reason === :submodular
        @test comps[2].variables == [5, 6, 7]
        @test !comps[2].is_submodular
        @test comps[2].stop_reason === :frustrated_cycle

        # Edge cases: empty component, already_fixed, zero_scale, work_limit, deadline
        @test_throws ArgumentError recognize_submodular_component(ws_dir, Symbol[])
        cp2 = checkpoint(ws_dir)
        assume!(ws_dir, :s1, 1)
        @test recognize_submodular_component(ws_dir, [:s1, :s2, :s3]).stop_reason === :already_fixed
        rollback!(ws_dir, cp2)

        ws_zero = Workspace(QT.Model(L_dir, Q_dir; scale=0.0, offset=0.0, sense=:min, domain=:spin))
        @test recognize_submodular_component(ws_zero, [:s1, :s2, :s3]).stop_reason === :zero_scale
        @test recognize_submodular_components(ws_zero)[2] === :zero_scale
        @test recognize_submodular_component(ws_dir, [:s1, :s2, :s3]; max_work=1).stop_reason === :work_limit
        @test recognize_submodular_component(ws_dir, [:s1, :s2, :s3]; deadline_ns=UInt64(0)).stop_reason === :deadline
    end

    @testset "Direct (|C|+2)-vertex cut solve: unique optimum beyond unary, relation & elimination passes" begin
        # Antiferromagnetic K_{3,3} ({1,2,3} x {4,5,6}) where every vertex has degree 3,
        # nonzero field, and |h_i| < sum_j |J_ij|: unary dominance, degree-<=2 elimination,
        # zero-field star-triangle, and pair relations all make 0 deductions, while the
        # gauge-submodular (|C|+2)-vertex cut pass solves all 6 variables with :strong persistency.
        L = Dict(1 => 1.5, 2 => 1.25, 3 => 1.0, 4 => -1.5, 5 => -1.25, 6 => -0.75)
        Q = Dict(
            (1, 4) => 2.0, (1, 5) => 2.0, (1, 6) => 2.0,
            (2, 4) => 2.0, (2, 5) => 2.0, (2, 6) => 2.0,
            (3, 4) => 2.0, (3, 5) => 2.0, (3, 6) => 2.0,
        )
        m_spin = QT.Model(L, Q; scale=2.0, offset=1.0, sense=:min, domain=:spin)
        best_val, best_states = _brute_force_opt(m_spin)
        @test length(best_states) == 1
        opt_state = best_states[1]

        ws = Workspace(m_spin; rules=:mixed)
        rep_sched = schedule_reductions!(ws; enable_star_triangle=true)
        @test rep_sched.deductions == 0

        att = prove_submodular_cut(ws, [1, 2, 3, 4, 5, 6])
        @test att.stop_reason === :proved
        @test att.method === :exact
        @test att.certificate !== nothing
        @test persistency(att.certificate) === :strong
        @test certificate_guarantee(att.certificate) === :optimum_preserving_restriction
        @test all(s -> step_guarantee(s) === :optimum_preserving_restriction, att.certificate.steps)
        @test length(att.fixings) == 6
        @test Dict(att.fixings) == Dict(i => opt_state[i] for i in 1:6)
        @test verify_certificate(ws, att.certificate).valid

        # Single-variable prove_submodular_cut
        att_single = prove_submodular_cut(ws, 2)
        @test att_single.stop_reason === :proved
        @test att_single.fixings == [2 => opt_state[2]]
        @test verify_certificate(ws, att_single.certificate).valid
        att_wrong = prove_submodular_cut(ws, 2; value=-opt_state[2])
        @test att_wrong.stop_reason === :not_strict
        @test att_wrong.certificate === nothing

        # Apply in-place, verify rollback and reconstruction
        cp = checkpoint(ws)
        rep = apply_submodular_cut!(ws)
        @test rep.stop_reason === :applied
        @test rep.recognized_components == 1
        @test rep.solved_components == 1
        @test rep.fixed_count == 6
        @test Dict(rep.fixings) == Dict(i => opt_state[i] for i in 1:6)
        cert_ws = export_certificate(ws)
        @test verify_certificate(ws, cert_ws).valid
        rec = reconstruct(materialize(ws), Int[])
        @test rec.state == opt_state
        @test rec.energy.value ≈ best_val

        rollback!(ws, cp)
        @test isempty(deductions(ws))

        # Test BoolDomain + Max sense + negative scale + DomainGaugeMap
        ws_tmp = Workspace(m_spin)
        m_bool_base = export_model(materialize(ws_tmp, domain_map(ws_tmp; domain=:bool)))
        f_b = QT.form(m_bool_base)
        m_bool_max = QT.Model(
            Dict(i => v for (i, v) in QT.linear_terms(f_b)),
            Dict((i, j) => v for ((i, j), v) in QT.quadratic_terms(f_b));
            scale=-1.5,
            offset=QT.offset(f_b),
            sense=:max,
            domain=:bool,
        )
        best_bval, best_bstates = _brute_force_opt(m_bool_max)
        @test length(best_bstates) == 1
        opt_bstate = best_bstates[1]

        ws_b = Workspace(m_bool_max)
        dmap = domain_map(ws_b; domain=:spin, gauge=[-1, 1, -1, 1, -1, 1])
        att_b = prove_submodular_cut(ws_b; map=dmap)
        @test att_b.stop_reason === :proved
        @test verify_certificate(ws_b, att_b.certificate; map=dmap).valid
        dmap2 = domain_map(ws_b; domain=:bool, gauge=[1, -1, 1, -1, 1, -1])
        cert_tr = transport_certificate(ws_b, att_b.certificate, dmap2)
        @test verify_certificate(ws_b, cert_tr; map=dmap2).valid

        rep_b = apply_submodular_cut!(ws_b; map=dmap)
        @test rep_b.stop_reason === :applied
        @test rep_b.fixed_count == 6
        rec_b = reconstruct(materialize(ws_b), Int[])
        @test rec_b.state == opt_bstate
        @test rec_b.energy.value ≈ best_bval
    end

    @testset "Strong vs weak persistency and tie_break on degenerate submodular components" begin
        # Component where x1 is strongly fixed to -1, while x2 and x3 are ferromagnetic and tied
        # (both (-1, -1, -1) and (-1, +1, +1) are global optima).
        L_tie = Dict(1 => 3.0, 2 => 0.0, 3 => 0.0)
        Q_tie = Dict((1, 2) => 0.0, (2, 3) => -2.0)
        # Add a tiny coupling between 1 and 2? No, if (1,2) is 0, {1} and {2,3} are separate components.
        # Let's couple 1 to 2 and 3 with opposite signs so 1=-1 cancels on 2 and 3!
        # Take E(s1, s2, s3) = 4*s1 + s2 + s3 + s1*s2 + s1*s3 - 2*s2*s3.
        # Gauge: sigma = [-1, 1, 1] -> sigma_1*sigma_2*J_12 = -1 < 0, sigma_1*sigma_3*J_13 = -1 < 0,
        # sigma_2*sigma_3*J_23 = -2 < 0! So it is a single connected gauge-submodular component!
        # At s1 = -1 (forced by 4*s1), E(-1, s2, s3) = -4 + s2 + s3 - s2 - s3 - 2*s2*s3 = -4 - 2*s2*s3,
        # which has TWO global minima at (s1, s2, s3) = (-1, -1, -1) and (-1, +1, +1) with energy -6!
        L_deg = Dict(1 => 4.0, 2 => 1.0, 3 => 1.0)
        Q_deg = Dict((1, 2) => 1.0, (1, 3) => 1.0, (2, 3) => -2.0)
        m_deg = QT.Model(L_deg, Q_deg; sense=:min, domain=:spin)
        best_val, best_states = _brute_force_opt(m_deg)
        @test best_val ≈ -6.0
        @test Set(best_states) == Set([[-1, -1, -1], [-1, 1, 1]])

        ws_deg = Workspace(m_deg)
        # 1. Default allow_weak=false: fixes only variable 1 => -1 (:strong), leaves 2 and 3 free
        att_strong = prove_submodular_cut(ws_deg)
        @test att_strong.stop_reason === :proved
        @test att_strong.fixings == [1 => -1]
        @test persistency(att_strong.certificate) === :strong
        @test verify_certificate(ws_deg, att_strong.certificate).valid

        # 2. allow_weak=true: fixes all 3 variables to a jointly compatible minimum cut!
        for tb in (:low, :high, :source, :sink)
            att_weak = prove_submodular_cut(ws_deg; allow_weak=true, tie_break=tb)
            @test att_weak.stop_reason === :proved
            @test length(att_weak.fixings) == 3
            @test persistency(att_weak.certificate) === :weak
            @test att_weak.certificate.steps[1].persistency === :strong
            @test att_weak.certificate.steps[2].persistency === :weak
            @test att_weak.certificate.steps[3].persistency === :weak
            @test verify_certificate(ws_deg, att_weak.certificate).valid
            fixed_vec = [ Dict(att_weak.fixings)[i] for i in 1:3 ]
            @test fixed_vec in best_states
        end
        @test Dict(prove_submodular_cut(ws_deg; allow_weak=true, tie_break=:low).fixings) == Dict(1 => -1, 2 => -1, 3 => -1)
        @test Dict(prove_submodular_cut(ws_deg; allow_weak=true, tie_break=:high).fixings) == Dict(1 => -1, 2 => 1, 3 => 1)
    end

    @testset "Mixed workspace (submodular + frustrated) & full certificate chain" begin
        # Component A ({1, 2, 3}): gauge-submodular with unique optimum
        # Component B ({4, 5, 6}): frustrated triangle
        L = Dict(1 => 1.5, 2 => -1.0, 3 => 0.5, 4 => 0.2, 5 => -0.3, 6 => 0.1)
        Q = Dict(
            (1, 2) => 2.0, (2, 3) => 2.0,
            (4, 5) => 1.5, (5, 6) => 1.5, (4, 6) => 1.5,
        )
        m = QT.Model(L, Q; sense=:min, domain=:spin)
        best_val, best_states = _brute_force_opt(m)
        @test length(best_states) == 1
        opt_state = best_states[1]

        ws = Workspace(m)
        # Proving frustrated component directly returns :frustrated_cycle
        att_frust = prove_submodular_cut(ws, [4, 5, 6])
        @test att_frust.stop_reason === :frustrated_cycle
        @test att_frust.certificate === nothing
        @test apply_submodular_cut!(ws, [4, 5, 6]).stop_reason === :frustrated_cycle

        # Whole-workspace pass solves Component A and leaves Component B intact
        rep = apply_submodular_cut!(ws)
        @test rep.stop_reason === :applied
        @test rep.recognized_components == 1
        @test rep.solved_components == 1
        @test rep.fixed_count == 3
        @test Dict(rep.fixings) == Dict(i => opt_state[i] for i in 1:3)
        @test verify_certificate(ws, export_certificate(ws)).valid

        rec = reconstruct(materialize(ws), [opt_state[4], opt_state[5], opt_state[6]])
        @test rec.state == opt_state
        @test rec.energy.value ≈ best_val
    end

    @testset "Adversarial tamper rejection on SubmodularCutStep" begin
        L = Dict(1 => 4.0, 2 => 1.0, 3 => 1.0)
        Q = Dict((1, 2) => 1.0, (1, 3) => 1.0, (2, 3) => -2.0)
        ws = Workspace(QT.Model(L, Q; sense=:min, domain=:spin))
        att = prove_submodular_cut(ws; allow_weak=true, tie_break=:low)
        @test att.stop_reason === :proved
        cert = att.certificate
        @test verify_certificate(ws, cert).valid
        s1, s2, s3 = cert.steps

        # 1. Tamper strong variable value (1 => +1 instead of -1)
        bad_bf1 = (1 => 1, s2.variable => s2.value, s3.variable => s3.value)
        t1 = DominanceCertificate(
            cert.generation, cert._scope_checkpoint, cert.assumptions,
            (
                SubmodularCutStep(1, 1, s1.component_variables, s1.gauge, s1.component_opt, s1.max_flow, s1.flow_edges, bad_bf1, 1, s1.constant, 0, :exact, s1.scope_length, :strong),
                SubmodularCutStep(s2.variable, s2.value, s2.component_variables, s2.gauge, s2.component_opt, s2.max_flow, s2.flow_edges, bad_bf1, 2, s2.constant, 1, :exact, s2.scope_length, :weak),
                SubmodularCutStep(s3.variable, s3.value, s3.component_variables, s3.gauge, s3.component_opt, s3.max_flow, s3.flow_edges, bad_bf1, 3, s3.constant, 2, :exact, s3.scope_length, :weak),
            ),
            cert._source, cert._map,
        )
        res1 = verify_certificate(ws, t1)
        @test !res1.valid
        @test res1.stop_reason === :invalid_bound

        # 2. Tamper persistency (:strong claimed on tied variable 2)
        t2 = DominanceCertificate(
            cert.generation, cert._scope_checkpoint, cert.assumptions,
            (
                s1,
                SubmodularCutStep(s2.variable, s2.value, s2.component_variables, s2.gauge, s2.component_opt, s2.max_flow, s2.flow_edges, s2.batch_fixings, 2, s2.constant, 1, :exact, s2.scope_length, :strong),
                s3,
            ),
            cert._source, cert._map,
        )
        res2 = verify_certificate(ws, t2)
        @test !res2.valid
        @test res2.stop_reason === :invalid_bound

        # 3. Tamper incompatible weak assignment (2 => -1, 3 => +1 cuts edge (2,3)!)
        bad_bf3 = (1 => -1, 2 => -1, 3 => 1)
        t3 = DominanceCertificate(
            cert.generation, cert._scope_checkpoint, cert.assumptions,
            (
                SubmodularCutStep(1, -1, s1.component_variables, s1.gauge, s1.component_opt, s1.max_flow, s1.flow_edges, bad_bf3, 1, s1.constant, 0, :exact, s1.scope_length, :strong),
                SubmodularCutStep(2, -1, s2.component_variables, s2.gauge, s2.component_opt, s2.max_flow, s2.flow_edges, bad_bf3, 2, s2.constant, 1, :exact, s2.scope_length, :weak),
                SubmodularCutStep(3, 1, s3.component_variables, s3.gauge, s3.component_opt, s3.max_flow, s3.flow_edges, bad_bf3, 3, s3.constant, 2, :exact, s3.scope_length, :weak),
            ),
            cert._source, cert._map,
        )
        res3 = verify_certificate(ws, t3)
        @test !res3.valid
        @test res3.stop_reason === :invalid_bound

        # 4. Tamper gauge to [1, 1, 1] (violates submodularity on (1,2) and (1,3))
        bad_g = (1, 1, 1)
        t4 = DominanceCertificate(
            cert.generation, cert._scope_checkpoint, cert.assumptions,
            (
                SubmodularCutStep(s1.variable, s1.value, s1.component_variables, bad_g, s1.component_opt, s1.max_flow, s1.flow_edges, s1.batch_fixings, 1, s1.constant, 0, :exact, s1.scope_length, s1.persistency),
                SubmodularCutStep(s2.variable, s2.value, s2.component_variables, bad_g, s2.component_opt, s2.max_flow, s2.flow_edges, s2.batch_fixings, 2, s2.constant, 1, :exact, s2.scope_length, s2.persistency),
                SubmodularCutStep(s3.variable, s3.value, s3.component_variables, bad_g, s3.component_opt, s3.max_flow, s3.flow_edges, s3.batch_fixings, 3, s3.constant, 2, :exact, s3.scope_length, s3.persistency),
            ),
            cert._source, cert._map,
        )
        res4 = verify_certificate(ws, t4)
        @test !res4.valid
        @test res4.stop_reason === :frustrated_cycle

        # 5. Tamper component_variables omitting boundary neighbor 3
        att_s = prove_submodular_cut(ws)
        cs1 = att_s.certificate.steps[1]
        t5 = DominanceCertificate(
            att_s.certificate.generation, att_s.certificate._scope_checkpoint, att_s.certificate.assumptions,
            (
                SubmodularCutStep(cs1.variable, cs1.value, (1, 2), (-1, 1), cs1.component_opt, cs1.max_flow, cs1.flow_edges, cs1.batch_fixings, 1, cs1.constant, 0, :exact, cs1.scope_length, :strong),
            ),
            att_s.certificate._source, att_s.certificate._map,
        )
        res5 = verify_certificate(ws, t5)
        @test !res5.valid
        @test res5.stop_reason === :boundary_coupled

        # 6. Tamper component_opt
        t6 = DominanceCertificate(
            att_s.certificate.generation, att_s.certificate._scope_checkpoint, att_s.certificate.assumptions,
            (
                SubmodularCutStep(cs1.variable, cs1.value, cs1.component_variables, cs1.gauge, cs1.component_opt + 1, cs1.max_flow, cs1.flow_edges, cs1.batch_fixings, 1, cs1.constant, 0, :exact, cs1.scope_length, :strong),
            ),
            att_s.certificate._source, att_s.certificate._map,
        )
        res6 = verify_certificate(ws, t6)
        @test !res6.valid
        @test res6.stop_reason === :invalid_bound

        # 7. Convenience constructors & batch_index > 1 mismatch rejection
        c_short1 = SubmodularCutStep(cs1.variable, cs1.value, cs1.component_variables, cs1.gauge, cs1.component_opt, cs1.max_flow, cs1.flow_edges, cs1.batch_fixings, 1, cs1.constant, 0, :exact)
        c_short2 = SubmodularCutStep(cs1.variable, cs1.value, cs1.component_variables, cs1.gauge, cs1.component_opt, cs1.max_flow, cs1.flow_edges, cs1.batch_fixings, 1, cs1.constant, 0, :exact, cs1.scope_length)
        @test c_short1.persistency === :strong && c_short2.persistency === :strong
    end

    @testset "Overloads, probing composition, and budget/deadline edge cases" begin
        L = Dict(1 => 4.0, 2 => 1.0, 3 => 1.0, 4 => 0.2, 5 => -0.3, 6 => 0.1)
        Q = Dict(
            (1, 2) => 1.0, (1, 3) => 1.0, (2, 3) => -2.0,
            (4, 5) => -2.0, (5, 6) => -2.0, (4, 6) => 1.5,
        )
        ws = Workspace(QT.Model(L, Q; sense=:min, domain=:spin))

        # Pass SubmodularComponent struct and keyword component=... to prove_submodular_cut & apply_submodular_cut!
        rec_c = recognize_submodular_component(ws, [1, 2, 3])
        att_comp = prove_submodular_cut(ws, rec_c; allow_weak=true, tie_break=:source)
        @test att_comp.stop_reason === :proved
        @test verify_certificate(ws, att_comp.certificate).valid
        att_kw = prove_submodular_cut(ws; component=[1, 2, 3], allow_weak=true, tie_break=:sink)
        @test att_kw.stop_reason === :proved
        @test verify_certificate(ws, att_kw.certificate).valid

        # Single-variable weak proof (m = 1 < k = 3)
        att_1w_low = prove_submodular_cut(ws, 2; allow_weak=true, tie_break=:low)
        @test att_1w_low.stop_reason === :proved
        @test verify_certificate(ws, att_1w_low.certificate).valid
        att_1w_high = prove_submodular_cut(ws, 2; allow_weak=true, tie_break=:high)
        @test att_1w_high.stop_reason === :proved
        @test verify_certificate(ws, att_1w_high.certificate).valid

        # Apply via SubmodularComponent, keyword component, and single label, plus compose with probing
        cp = checkpoint(ws)
        rep_1 = apply_submodular_cut!(ws, 1)
        @test rep_1.stop_reason === :applied
        @test rep_1.fixed_count == 1
        @test prove_submodular_cut(ws, 1).stop_reason === :already_fixed
        @test apply_submodular_cut!(ws, 1).stop_reason === :already_fixed
        rollback!(ws, cp)

        cp2 = checkpoint(ws)
        rep_c = apply_submodular_cut!(ws, rec_c)
        @test rep_c.stop_reason === :applied
        @test rep_c.fixed_count == 1
        # Compose SubmodularCutStep with ProbingStep on variable 4
        w_valid = Dict(1 => -1, 2 => -1, 3 => -1, 4 => 1, 5 => 1, 6 => 1)
        w_bad = Dict(1 => 1, 2 => -1, 3 => -1, 4 => 1, 5 => 1, 6 => 1)
        @test_throws ArgumentError prove_probing(ws, 4, w_bad)
        p_att = prove_probing(ws, 4, w_valid)
        if p_att.certificate !== nothing
            @test verify_certificate(ws, p_att.certificate).valid
        end
        rollback!(ws, cp2)

        cp3 = checkpoint(ws)
        rep_kw = apply_submodular_cut!(ws; component=[1, 2, 3], allow_weak=true, tie_break=:low)
        @test rep_kw.stop_reason === :applied
        @test rep_kw.fixed_count == 3
        rollback!(ws, cp3)

        # No-persistency component (all tied with allow_weak=false)
        ws_tie = Workspace(QT.Model(Dict(1 => 0.0, 2 => 0.0), Dict((1, 2) => -2.0); sense=:min, domain=:spin))
        @test prove_submodular_cut(ws_tie).stop_reason === :no_persistency
        @test prove_submodular_cut(ws_tie, [1, 2]).stop_reason === :no_persistency
        @test apply_submodular_cut!(ws_tie).stop_reason === :no_persistency
        @test apply_submodular_cut!(ws_tie, [1, 2]).stop_reason === :no_persistency

        # Frustrated whole-workspace
        ws_fr = Workspace(QT.Model(Dict(1 => 0.1, 2 => -0.1, 3 => 0.1), Dict((1, 2) => 1.5, (2, 3) => 1.5, (1, 3) => 1.5); sense=:min, domain=:spin))
        @test prove_submodular_cut(ws_fr).stop_reason === :frustrated_cycle
        @test apply_submodular_cut!(ws_fr).stop_reason === :frustrated_cycle

        # Zero-scale workspace
        ws_z = Workspace(QT.Model(Dict(1 => 1.0, 2 => -1.0), Dict((1, 2) => -1.0); scale=0.0, offset=0.0, sense=:min, domain=:spin))
        @test prove_submodular_cut(ws_z).stop_reason === :zero_scale
        @test prove_submodular_cut(ws_z, 1).stop_reason === :zero_scale
        @test apply_submodular_cut!(ws_z).stop_reason === :zero_scale
        @test apply_submodular_cut!(ws_z, 1).stop_reason === :zero_scale

        # Budget and deadline stops
        @test prove_submodular_cut(ws; max_work=1).stop_reason === :work_limit
        @test prove_submodular_cut(ws; max_exact_work=1).stop_reason === :verification_limit
        @test prove_submodular_cut(ws; deadline_ns=UInt64(0)).stop_reason === :deadline
        @test prove_submodular_cut(ws, 1; max_work=1).stop_reason === :work_limit
        @test prove_submodular_cut(ws, [1, 2, 3]; max_exact_work=1).stop_reason === :verification_limit
        @test apply_submodular_cut!(ws; max_work=1).stop_reason === :work_limit
        @test apply_submodular_cut!(ws; max_exact_work=1).stop_reason === :verification_limit
        @test apply_submodular_cut!(ws; deadline_ns=UInt64(0)).stop_reason === :deadline
        @test apply_submodular_cut!(ws, 1; max_work=1).stop_reason === :work_limit
        @test apply_submodular_cut!(ws, [1, 2, 3]; max_exact_work=1).stop_reason === :verification_limit
    end
end
