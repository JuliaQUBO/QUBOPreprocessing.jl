function _exhaustive_optima_mc(model::QT.Model)
    f = QT.form(model)
    n = QT.dimension(model)
    is_bool = QT.domain(model) === QT.BoolDomain
    low = is_bool ? 0 : -1
    sense = QT.sense(model)
    best_val = sense === QT.Min ? Inf : -Inf
    states = Vector{Int}[]
    for mask in 0:((1 << n) - 1)
        st = Int[((mask >> (b - 1)) & 1) == 1 ? 1 : low for b in 1:n]
        val = QT.value(st, f)
        if (sense === QT.Min && val < best_val - 1e-12) || (sense === QT.Max && val > best_val + 1e-12)
            best_val = val
            empty!(states)
            push!(states, st)
        elseif abs(val - best_val) <= 1e-12
            push!(states, st)
        end
    end
    return best_val, states
end

@testset "Weighted Max-Cut preprocessing (#18)" begin
    @testset "Ising <-> Max-Cut representation & all-state energy/gauge identity" begin
        L_spin = Dict{Symbol,Float64}(:s1 => -1.5, :s2 => 2.25, :s3 => 0.0)
        Q_spin = Dict{Tuple{Symbol,Symbol},Float64}(
            (:s1, :s2) => -2.0,
            (:s2, :s3) => 1.25,
            (:s1, :s3) => -0.75,
        )
        model_spin = QT.Model(L_spin, Q_spin; scale=2.0, offset=-0.5, sense=:min, domain=:spin)
        ws_spin = Workspace(model_spin; rules=:mixed)
        mc = maxcut_graph(ws_spin)
        @test mc.stop_reason === :completed
        @test generation(mc) == generation(ws_spin)
        @test mc.reference_vertex == 0
        @test mc.variables == [:s1, :s2, :s3]
        @test mc.reference_degree == 2
        @test mc.internal_edges == 3
        @test mc.total_edges == 5

        f_spin = QT.form(model_spin)
        for z0 in (-1, 1), z1 in (-1, 1), z2 in (-1, 1), z3 in (-1, 1)
            cut_vec = [z0, z1, z2, z3]
            cut_neg = [-z0, -z1, -z2, -z3]
            cut_dict = Dict(:reference => z0, :s1 => z1, :s2 => z2, :s3 => z3)
            @test maxcut_cut_weight(mc, cut_vec) == maxcut_cut_weight(mc, cut_neg)
            @test maxcut_cut_weight(mc, cut_vec) == maxcut_cut_weight(mc, cut_dict)
            @test maxcut_energy(mc, cut_vec) == maxcut_energy(mc, cut_neg)
            s_vec = maxcut_to_spin(mc, cut_vec)
            @test s_vec == maxcut_to_spin(mc, cut_neg)
            @test s_vec == [z0 * z1, z0 * z2, z0 * z3]
            @test spin_to_maxcut(mc, s_vec; reference_side=z0) == cut_vec
            @test Float64(maxcut_energy(mc, cut_vec; scaled=true)) ≈ QT.value(s_vec, f_spin)
        end

        # Boolean model + Max sense + negative scale + DomainGaugeMap + caller assumption
        L_bool = Dict{Int,Float64}(1 => 3.0, 2 => -2.0, 3 => 1.5, 4 => -0.5)
        Q_bool = Dict{Tuple{Int,Int},Float64}(
            (1, 2) => -4.0,
            (2, 3) => 2.0,
            (3, 4) => -1.0,
            (1, 4) => 3.0,
        )
        model_bool = QT.Model(L_bool, Q_bool; scale=-1.5, offset=1.25, sense=:max, domain=:bool)
        ws_bool = Workspace(model_bool; rules=:mixed)
        assume!(ws_bool, 4, 1)
        dmap = domain_map(ws_bool; domain=:spin, gauge=[1, -1, 1, -1])
        mc_b = maxcut_graph(ws_bool; map=dmap)
        @test mc_b.stop_reason === :completed
        @test mc_b.variables == [1, 2, 3]
        @test mc_b.gauge == [1, -1, 1]
        f_bool = QT.form(model_bool)
        for z0 in (-1, 1), z1 in (-1, 1), z2 in (-1, 1), z3 in (-1, 1)
            cvec = [z0, z1, z2, z3]
            s_orig = maxcut_to_spin(mc_b, cvec; mapped=false)
            s_map = maxcut_to_spin(mc_b, cvec; mapped=true)
            @test s_orig == [mc_b.gauge[a] * s_map[a] for a in 1:3]
            @test spin_to_maxcut(mc_b, s_orig; reference_side=z0, mapped=false) == cvec
            @test spin_to_maxcut(mc_b, s_map; reference_side=z0, mapped=true) == cvec
            x_full = [((s_orig[1] + 1) ÷ 2), ((s_orig[2] + 1) ÷ 2), ((s_orig[3] + 1) ÷ 2), 1]
            # direction = (Max -> -1) * (scale < 0 -> -1) = +1, so scaled maxcut_energy == -1.5 * F_unscaled == -QT.value
            @test Float64(maxcut_energy(mc_b, cvec; scaled=false)) ≈ QT.value(x_full, f_bool) / (-1.5)
        end
    end

    @testset "Positive triangle contraction beyond unary, GLK pair, roof duality, and submodular cut" begin
        # 4-spin zero-field model with frustrated triangle {2, 3, 4} (+2, +0.5, +0.5)
        # and supportive triangle {1, 2, 3} (J12 = -2, J13 = +2, J23 = +2).
        L = Dict{Symbol,Float64}(:s1 => 0.0, :s2 => 0.0, :s3 => 0.0, :s4 => 0.0)
        Q = Dict{Tuple{Symbol,Symbol},Float64}(
            (:s1, :s2) => -2.0,
            (:s1, :s3) => 2.0,
            (:s2, :s3) => 2.0,
            (:s1, :s4) => 0.5,
            (:s2, :s4) => 0.5,
            (:s3, :s4) => 0.5,
        )
        model = QT.Model(L, Q; sense=:min, domain=:spin)
        ws = Workspace(model; rules=:mixed)

        # Standard unary dominance, single-endpoint/GLK pair relations, roof duality, and submodular cut fail,
        # while shared-neighborhood :coflip_pair and :maxcut_triangle succeed:
        @test prove_dominance(ws, :s1).stop_reason === :not_strict
        @test prove_relation(ws, :s1, :s2).method === :coflip_pair
        @test prove_roof_duality(ws).stop_reason === :no_persistency
        @test prove_submodular_cut(ws).stop_reason === :frustrated_cycle

        # Max-Cut triangle rule succeeds on (:s1, :s2) with sign = +1 and margin = 7//2:
        att = prove_maxcut(ws, :s1, :s2)
        @test att.stop_reason === :proved
        @test att.method === :maxcut_triangle
        @test att.margin == 7 // 2
        @test att.triangles_used == 2
        @test att.certificate !== nothing
        @test verify_certificate(ws, att.certificate).valid
        step = att.certificate.steps[end]::MaxCutStep
        @test step.eliminated == 1 && step.representative == 2
        @test step.sign == 1 && step.orig_sign == 1
        @test step_guarantee(step) === :optimum_preserving_restriction
        @test persistency(step) === :strong

        # Without triangles (max_triangles = 0), (:s1, :s2) cannot be proved:
        att_no_tri = prove_maxcut(ws, :s1, :s2; max_triangles=0)
        @test att_no_tri.stop_reason === :not_strict
        @test att_no_tri.method === :maxcut_edge
        @test att_no_tri.triangles_used == 0

        # Apply to workspace, verify certificate, materialize, and check all optima preserved:
        rep = apply_maxcut!(ws, :s1, :s2)
        @test rep.stop_reason === :applied
        @test rep.deductions == 1
        @test rep.pair_contractions == 1
        @test rep.triangle_deductions == 1
        @test rep.contractions == [(:s1, :s2, 1)]
        @test relation_map(ws, :s1) == (:s2 => 1)
        cert = export_certificate(ws)
        @test verify_certificate(ws, cert).valid

        opt_val, opt_states = _exhaustive_optima_mc(model)
        @test all(st -> st[1] == st[2], opt_states)
        exported = materialize(ws)
        res_model = export_model(exported)
        res_val, res_states = _exhaustive_optima_mc(res_model)
        @test res_val ≈ opt_val
        lifted = [reconstruct(exported, y).state for y in res_states]
        @test Set(lifted) == Set(opt_states)

        # Pair MaxCutStep depends on free triangle vertices: subsequent assume! on a free
        # triangle vertex (:s3) rolls back the pair MaxCutStep suffix before replaying:
        assume!(ws, :s3, 1)
        @test isempty(reductions(ws))
        @test assumptions(ws) == [:s3 => 1]
        @test export_certificate(ws) === nothing
    end

    @testset "Frustrated triangle co-flip relief and unary reference-triangle fixing" begin
        # 1. Frustrated triangle {1, 2, 3}: J12 = -2.5, J13 = -2.0, J23 = +0.5 (frustrated for sigma = +1),
        #    plus J14 = +0.5, J25 = +2.5 (so anchor 2 has 2.5 - 0.5 - 2.5 = -0.5 < 0 and rad_coflip = 2.75 > 2.5), and zero fields.
        #    Standard/coflip relation margin on (1, 2) is <= 0 (not strict),
        #    while co-flipping c = 3 with a = 1 reduces penalty on (1, 3) from 2.0 to |J23| = 0.5,
        #    giving Max-Cut triangle margin 2.5 - 0.5 - 0.5 = +1.5 > 0!
        L_fr = Dict{Symbol,Float64}(:s1 => 0.0, :s2 => 0.0, :s3 => 0.0, :s4 => 0.0, :s5 => 0.0)
        Q_fr = Dict{Tuple{Symbol,Symbol},Float64}(
            (:s1, :s2) => -2.5,
            (:s1, :s3) => -2.0,
            (:s2, :s3) => 0.5,
            (:s1, :s4) => 0.5,
            (:s2, :s5) => 2.5,
        )
        model_fr = QT.Model(L_fr, Q_fr; sense=:min, domain=:spin)
        ws_fr = Workspace(model_fr; rules=:mixed)
        @test prove_relation(ws_fr, :s1, :s2; sign=1).stop_reason === :not_strict
        @test prove_relation(ws_fr, :s2, :s1; sign=1).stop_reason === :not_strict
        att_fr = prove_maxcut(ws_fr, :s1, :s2; sign=1)
        @test att_fr.stop_reason === :proved
        @test att_fr.method === :maxcut_triangle
        @test att_fr.margin == 3 // 2
        @test verify_certificate(ws_fr, att_fr.certificate).valid

        # 2. Unary fixing via reference-node triangle {u, 0, c}:
        #    h1 = -2, h2 = -2, J12 = -3, J13 = -1, J23 = +0.5 (frustrated 3-cycle {1, 2, 3} with product > 0).
        #    Unary dominance on s1 has |h1| - |J12| - |J13| = 2 - 3 - 1 = -2 < 0 (fails).
        #    Reference triangle {1, 0, 2} gives gamma = min(3, 2 - 0.5) = +1.5, so margin = 2 + 1.5 - 1 = +2.5 > 0!
        L_un = Dict{Symbol,Float64}(:s1 => -2.0, :s2 => -2.0, :s3 => 0.0)
        Q_un = Dict{Tuple{Symbol,Symbol},Float64}(
            (:s1, :s2) => -3.0,
            (:s1, :s3) => -1.0,
            (:s2, :s3) => 0.5,
        )
        model_un = QT.Model(L_un, Q_un; sense=:min, domain=:spin)
        ws_un = Workspace(model_un; rules=:mixed)
        @test prove_dominance(ws_un, :s1).stop_reason === :not_strict
        @test prove_submodular_cut(ws_un, :s1).stop_reason === :frustrated_cycle
        att_un = prove_maxcut(ws_un, :s1)
        @test att_un.stop_reason === :proved
        @test att_un.method === :maxcut_triangle
        @test att_un.margin == 5 // 2
        @test verify_certificate(ws_un, att_un.certificate).valid

        rep_un = apply_maxcut!(ws_un, :s1)
        @test rep_un.stop_reason === :applied
        @test rep_un.unary_fixings == 1
        @test rep_un.fixings == [:s1 => 1]
        @test deductions(ws_un) == [:s1 => 1]
        @test verify_certificate(ws_un, export_certificate(ws_un)).valid
        opt_val, opt_states = _exhaustive_optima_mc(model_un)
        @test all(st -> st[1] == 1, opt_states)
    end

    @testset "Negative example: Multicut-only triangle rule fails on signed Max-Cut" begin
        # Naive Multicut triangle rule ignores external degree R_3^(1,2) = |h3| = 6 on triangle vertex s3
        # and computes -J12 + min(|J13|, |J23|) - |J14| = 2 + 2 - 3.5 = +0.5 > 0 (claiming s1 = +s2).
        # However, s3 = +1 and s4 = +1 are pinned by h3 = h4 = -6, which forces the unique global
        # optimum to (-1, +1, +1, +1) with s1 = -1 != s2 = +1!
        L_neg = Dict{Symbol,Float64}(:s1 => 0.0, :s2 => 0.0, :s3 => -6.0, :s4 => -6.0)
        Q_neg = Dict{Tuple{Symbol,Symbol},Float64}(
            (:s1, :s2) => -2.0,
            (:s1, :s3) => 2.0,
            (:s2, :s3) => 2.0,
            (:s1, :s4) => 3.5,
            (:s2, :s4) => -5.5,
        )
        model_neg = QT.Model(L_neg, Q_neg; sense=:min, domain=:spin)
        opt_val, opt_states = _exhaustive_optima_mc(model_neg)
        @test opt_val ≈ -19.0
        @test opt_states == [[-1, 1, 1, 1]]
        @test opt_states[1][1] != opt_states[1][2]

        ws_neg = Workspace(model_neg; rules=:mixed)
        att_neg = prove_maxcut(ws_neg, :s1, :s2; sign=1)
        @test att_neg.stop_reason === :not_strict
        @test att_neg.certificate === nothing
        @test att_neg.margin == -7 // 2
        rep_neg = apply_maxcut!(ws_neg, :s1, :s2; sign=1)
        @test rep_neg.stop_reason === :not_strict
        @test rep_neg.deductions == 0
    end

    @testset "Whole-pass apply_maxcut!, DomainGaugeMap transport, rollback, and reference degree" begin
        L = Dict{Int,Float64}(1 => -2.5, 2 => 0.0, 3 => 0.0, 4 => 0.0, 5 => 0.5)
        Q = Dict{Tuple{Int,Int},Float64}(
            (1, 2) => -2.5,
            (1, 3) => 2.0,
            (2, 3) => 2.0,
            (2, 4) => -3.0,
            (2, 5) => -2.0,
            (4, 5) => -2.0,
            (3, 5) => 0.25,
        )
        model = QT.Model(L, Q; scale=1.5, offset=-1.0, sense=:min, domain=:bool)
        opt_val, opt_states = _exhaustive_optima_mc(model)

        ws = Workspace(model; rules=:mixed)
        cp0 = checkpoint(ws)
        dmap = domain_map(ws; domain=:spin, gauge=[1, -1, 1, -1, 1])
        rep = apply_maxcut!(ws; map=dmap)
        @test rep.stop_reason === :quiescent
        @test rep.deductions >= 1
        @test rep.initial_reference_degree == maxcut_graph(Workspace(model)).reference_degree
        @test rep.residual_reference_degree == maxcut_graph(ws).reference_degree

        cert = export_certificate(ws)
        @test cert !== nothing
        @test verify_certificate(ws, cert).valid
        tcert = transport_certificate(ws, cert, dmap)
        @test verify_certificate(ws, tcert; map=dmap).valid

        exported = materialize(ws; map=dmap)
        res_model = export_model(exported)
        res_val, res_states = _exhaustive_optima_mc(res_model)
        @test res_val ≈ opt_val
        for y in res_states
            rec = reconstruct(exported, y)
            @test rec.energy.value ≈ opt_val
            @test rec.state in opt_states
        end

        # Rollback restores exact pre-pass state and reference degree:
        rb = rollback!(ws, cp0; report=true)
        @test rb.checkpoint == cp0
        @test isempty(reductions(ws))
        @test maxcut_graph(ws).reference_degree == rep.initial_reference_degree

        # Re-apply and test assume! after MaxCutStep:
        apply_maxcut!(ws)
        @test !isempty(reductions(ws))
        @test_throws ArgumentError assume!(ws, 3, 1)
        ws_pair = Workspace(model; rules=:mixed)
        apply_maxcut!(ws_pair, 1)
        @test length(reductions(ws_pair)) == 1
        u_rep = assume!(ws_pair, 4, 1)
        @test u_rep.stop_reason === :applied
        @test assumptions(ws_pair) == [4 => 1]
    end

    @testset "Budgets, max_triangles, max_fill, weak ties, and certificate tamper rejection" begin
        # 1. Two productive triangles on (1, 2): test max_triangles = 1 vs 2
        L_two = Dict{Int,Float64}(1 => 0.0, 2 => 0.0, 3 => 0.0, 4 => 0.0)
        Q_two = Dict{Tuple{Int,Int},Float64}(
            (1, 2) => -1.5,
            (1, 3) => -2.0,
            (2, 3) => -2.0,
            (1, 4) => -1.0,
            (2, 4) => -1.0,
        )
        ws_two = Workspace(QT.Model(L_two, Q_two; sense=:min, domain=:spin); rules=:mixed)
        att_1 = prove_maxcut(ws_two, 1, 2; max_triangles=1)
        att_2 = prove_maxcut(ws_two, 1, 2; max_triangles=2)
        @test att_1.stop_reason === :proved && att_1.triangles_used == 1 && att_1.margin == 5 // 2
        @test att_2.stop_reason === :proved && att_2.triangles_used == 2 && att_2.margin == 9 // 2

        # 2. Fill limit blocks fill-producing contraction:
        L_fill = Dict{Int,Float64}(1 => 0.0, 2 => 0.0, 3 => -5.0, 4 => -5.0)
        Q_fill = Dict{Tuple{Int,Int},Float64}(
            (1, 2) => -5.0,
            (1, 3) => 1.0,
            (2, 4) => 1.0,
        )
        ws_fill = Workspace(QT.Model(L_fill, Q_fill; sense=:min, domain=:spin); rules=:mixed)
        @test apply_maxcut!(ws_fill, 1, 2; max_fill=0).stop_reason === :fill_limit
        @test apply_maxcut!(ws_fill; enable_unary=false, max_fill=0).stop_reason === :fill_limit
        @test apply_maxcut!(ws_fill, 1, 2; max_fill=1).stop_reason === :applied

        # 3. Weak tie handling (margin == 0):
        L_tie = Dict{Int,Float64}(1 => 0.0, 2 => 0.0, 3 => 0.0)
        Q_tie = Dict{Tuple{Int,Int},Float64}(
            (1, 2) => -1.0,
            (1, 3) => -1.0,
            (2, 3) => 1.0,
        )
        ws_tie = Workspace(QT.Model(L_tie, Q_tie; sense=:min, domain=:spin); rules=:mixed)
        @test prove_maxcut(ws_tie, 1, 2; allow_weak=false).stop_reason === :not_strict
        att_weak = prove_maxcut(ws_tie, 1, 2; allow_weak=true)
        @test att_weak.stop_reason === :proved
        @test att_weak.margin == 0
        @test persistency(att_weak.certificate) === :weak
        @test verify_certificate(ws_tie, att_weak.certificate).valid

        # 4. Work, verification, and deadline limits:
        @test prove_maxcut(ws_two, 1, 2; max_work=1).stop_reason === :work_limit
        @test prove_maxcut(ws_two, 1, 2; max_exact_work=1).stop_reason === :verification_limit
        @test prove_maxcut(ws_two, 1, 2; deadline_ns=UInt64(1)).stop_reason === :deadline
        @test apply_maxcut!(ws_two; enable_unary=false, enable_pairs=false).stop_reason === :optional_pass_disabled

        # 5. Tamper rejection:
        cert_ok = att_2.certificate
        @test verify_certificate(ws_two, cert_ok).valid
        s_ok = cert_ok.steps[1]::MaxCutStep
        make_cert(st_mod) = DominanceCertificate(
            cert_ok.generation, cert_ok._scope_checkpoint, cert_ok.assumptions,
            (st_mod,), cert_ok._source, cert_ok._map,
        )
        # Tamper margin:
        s_bad_m = MaxCutStep(
            s_ok.eliminated, s_ok.representative, s_ok.anchor, s_ok.sign, s_ok.orig_sign, s_ok.value,
            s_ok.margin + 1, s_ok.direct_weight, s_ok.non_triangle_slack, s_ok.triangles,
            s_ok.constant, s_ok.predecessors, s_ok.method, s_ok.scope_length, s_ok.persistency,
        )
        @test verify_certificate(ws_two, make_cert(s_bad_m)).stop_reason === :invalid_bound

        # Tamper triangle gamma:
        t1 = s_ok.triangles[1]
        bad_tris = ((t1[1], t1[2], t1[3], t1[4], t1[5] + 1), s_ok.triangles[2])
        s_bad_tri = MaxCutStep(
            s_ok.eliminated, s_ok.representative, s_ok.anchor, s_ok.sign, s_ok.orig_sign, s_ok.value,
            s_ok.margin + 1, s_ok.direct_weight, s_ok.non_triangle_slack, bad_tris,
            s_ok.constant, s_ok.predecessors, s_ok.method, s_ok.scope_length, s_ok.persistency,
        )
        @test verify_certificate(ws_two, make_cert(s_bad_tri)).stop_reason === :invalid_bound

        # Tamper triangle ordering:
        rev_tris = (s_ok.triangles[2], s_ok.triangles[1])
        s_bad_ord = MaxCutStep(
            s_ok.eliminated, s_ok.representative, s_ok.anchor, s_ok.sign, s_ok.orig_sign, s_ok.value,
            s_ok.margin, s_ok.direct_weight, s_ok.non_triangle_slack, rev_tris,
            s_ok.constant, s_ok.predecessors, s_ok.method, s_ok.scope_length, s_ok.persistency,
        )
        @test verify_certificate(ws_two, make_cert(s_bad_ord)).stop_reason === :invalid_step

        # Tamper sign:
        s_bad_sign = MaxCutStep(
            s_ok.eliminated, s_ok.representative, s_ok.anchor, -s_ok.sign, s_ok.orig_sign, s_ok.value,
            s_ok.margin, s_ok.direct_weight, s_ok.non_triangle_slack, s_ok.triangles,
            s_ok.constant, s_ok.predecessors, s_ok.method, s_ok.scope_length, s_ok.persistency,
        )
        @test verify_certificate(ws_two, make_cert(s_bad_sign)).stop_reason === :invalid_value

        # Tamper constant:
        s_bad_const = MaxCutStep(
            s_ok.eliminated, s_ok.representative, s_ok.anchor, s_ok.sign, s_ok.orig_sign, s_ok.value,
            s_ok.margin, s_ok.direct_weight, s_ok.non_triangle_slack, s_ok.triangles,
            s_ok.constant + 1, s_ok.predecessors, s_ok.method, s_ok.scope_length, s_ok.persistency,
        )
        @test verify_certificate(ws_two, make_cert(s_bad_const)).stop_reason === :invalid_constant
    end
end
