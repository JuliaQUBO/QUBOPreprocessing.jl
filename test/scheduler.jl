# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

@testset "mixed scheduler pass ordering, cascading and exact oracle traces" begin
    R = Rational{BigInt}
    # 7-variable spin model exercising all four passes in a single shared Workspace:
    # - v1: strongly dominated leaf (h_1 = +5, J_{1,2} = 1 -> s_1 = -1), shifting h_2
    # - v2: degree-1 leaf after v1 is fixed -> eliminated by :elimination (degree <= 2)
    # - v3, v4: strongly coupled pair (J_{3,4} = -6) with shared neighbors v5, v6 -> contracted by :relations
    # - After contracting v3 into v4, v5 drops from degree 4 to degree 3 with h_5 == 0 -> eliminated by :star_triangle
    # - Remaining triangle (v4, v6, v7) cascades via degree-2/1/0 :elimination to 0 variables!
    labels = [:v1, :v2, :v3, :v4, :v5, :v6, :v7]
    L_spin = [5.0, 0.5, 0.25, -0.25, 0.0, 0.25, -0.5]
    Q_spin = zeros(7, 7)
    Q_spin[1, 2] = 1.0
    Q_spin[2, 3] = -0.5
    Q_spin[3, 4] = -6.0
    Q_spin[3, 5] = 0.5
    Q_spin[3, 6] = 0.5
    Q_spin[4, 5] = 0.5
    Q_spin[4, 6] = 0.5
    Q_spin[4, 7] = 1.0
    Q_spin[5, 6] = -1.0
    Q_spin[5, 7] = 1.0
    Q_spin[6, 7] = -1.0

    for domain in (:spin, :bool), sense in (:min, :max), scale in (1.0, -2.0)
        dir = (sense === :min ? 1 : -1) * (scale < 0 ? -1 : 1)
        h_s = R.(dir .* L_spin)
        J_s = R.(dir .* Q_spin)
        L_f, Q_f, c_f = if domain === :spin
            Float64.(h_s), Float64.(J_s), 0.25
        else
            Q_b = 4 .* J_s
            L_b = [2 * h_s[i] - sum(2 * J_s[min(i, j), max(i, j)] for j in 1:7 if j != i) for i in 1:7]
            c_b = R(1//4) - sum(h_s) + sum(J_s[i, j] for i in 1:7 for j in (i+1):7)
            Float64.(L_b), Float64.(Q_b), Float64(c_b)
        end
        m = fixture(labels, L_f, Q_f; domain, sense, scale, offset=c_f)
        optima = oracle_optima(L_f, Q_f, scale, c_f, domain, sense, ())
        opt_e = reference(L_f, Q_f, scale, c_f, first(optima), R)

        # 1. Default mixed schedule (enable_star_triangle=false) stops at cheap + relations fixpoint
        #    and reports :star_triangle in optional_passes_disabled:
        ws_cheap, rep_cheap = preprocess(m; rules=:mixed)
        @test rep_cheap isa ScheduleReport
        @test generation(rep_cheap) == generation(ws_cheap)
        @test rep_cheap.stop_reason === :quiescent
        @test rep_cheap.dominance_deductions >= 1
        @test rep_cheap.elimination_deductions >= 1
        @test rep_cheap.relation_deductions >= 1
        @test rep_cheap.star_triangle_deductions == 0
        @test :star_triangle in rep_cheap.optional_passes_disabled
        @test rep_cheap.initial_variables == 7
        @test rep_cheap.residual_variables == 7 - rep_cheap.deductions
        @test verify_certificate(ws_cheap, export_certificate(ws_cheap)).valid
        res_cheap = materialize(ws_cheap; coefficient_type=R)
        @test QUBOPreprocessing.index_map(res_cheap) == QUBOPreprocessing.index_map(ws_cheap)
        assert_universal_lifting_and_persistency(res_cheap, L_f, Q_f, scale, c_f, domain, sense, optima, opt_e)

        # 2. Enabling star-triangle on the SAME workspace continues from the exact state without rescanning
        #    and cascades the remaining vertices to 0 free variables:
        rep_star = schedule_reductions!(ws_cheap; enable_star_triangle=true)
        @test rep_star.stop_reason === :quiescent
        @test rep_star.star_triangle_deductions >= 1
        @test rep_star.residual_variables == 0
        @test rep_star.residual_edges == 0
        @test isempty(rep_star.optional_passes_disabled)
        @test verify_certificate(ws_cheap, export_certificate(ws_cheap)).valid
        res_full = materialize(ws_cheap; coefficient_type=R)
        assert_universal_lifting_and_persistency(res_full, L_f, Q_f, scale, c_f, domain, sense, optima, opt_e)

        # 3. Step-by-step deterministic transaction trace (max_deductions=1 per transaction)
        #    verifying original and scoped optima after EVERY single transaction:
        ws_step = Workspace(m; rules=:mixed)
        gmap = domain_map(ws_step; domain=(domain === :spin ? :bool : :spin), gauge=[-1, 1, -1, 1, -1, 1, -1])
        @test generation(gmap) == generation(ws_step)
        step_count = 0
        while true
            r_step = schedule_reductions!(ws_step; map=gmap, enable_star_triangle=true, max_deductions=1)
            @test r_step.stop_reason in (:deduction_limit, :quiescent)
            cert_step = export_certificate(ws_step)
            if cert_step !== nothing
                @test verify_certificate(ws_step, cert_step).valid
                @test verify_certificate(ws_step, export_certificate(ws_step; map=gmap); map=gmap).valid
            end
            res_step = materialize(ws_step; coefficient_type=R)
            assert_universal_lifting_and_persistency(res_step, L_f, Q_f, scale, c_f, domain, sense, optima, opt_e)
            res_mapped = materialize(ws_step, gmap; coefficient_type=R)
            assert_universal_lifting_and_persistency(res_mapped, L_f, Q_f, scale, c_f, domain, sense, optima, opt_e)
            r_step.stop_reason === :quiescent && break
            step_count += 1
            @test step_count <= 7
            step_count <= 7 || break
        end
        @test step_count == 7

        # 4. Scoped transaction trace: assume a variable, run mixed schedule step-by-step, verify scoped oracle,
        #    rollback, and verify full state restoration:
        ws_scoped = Workspace(m; rules=:mixed)
        cp_root = checkpoint(ws_scoped)
        low_val = domain === :bool ? 0 : -1
        for pin_val in (low_val, 1)
            @test assume!(ws_scoped, :v6, pin_val).stop_reason === :applied
            sc_optima = oracle_optima(L_f, Q_f, scale, c_f, domain, sense, [(6, pin_val)])
            sc_e = reference(L_f, Q_f, scale, c_f, first(sc_optima), R)
            sc_iters = 0
            while true
                sc_iters += 1
                rs = schedule_reductions!(ws_scoped; enable_star_triangle=true, max_deductions=1)
                res_sc = materialize(ws_scoped; coefficient_type=R)
                @test res_sc.certificate.scope === :assumptions
                assert_universal_lifting_and_persistency(res_sc, L_f, Q_f, scale, c_f, domain, sense, sc_optima, sc_e)
                (rs.stop_reason === :quiescent || sc_iters >= 10) && break
            end
            rollback!(ws_scoped, cp_root)
            @test ws_scoped._state.active_edges == ws_scoped._state.initial_edges
            @test isempty(ws_scoped._state.fixes)
        end
    end
end

@testset "stop reasons, budgets, interruption/resumption and unsupported arithmetic" begin
    R = Rational{BigInt}
    # 1. Argument validation and rules checks:
    m_simple = fixture([:a, :b, :c], [1.0, -0.5, 0.25], [0.0 -1.0 0.5; 0.0 0.0 -0.75; 0.0 0.0 0.0]; domain=:spin)
    @test_throws ArgumentError Workspace(m_simple; rules=:unknown_rule)
    @test_throws ArgumentError preprocess(m_simple; rules=:identity, max_work=10)
    ws_id = Workspace(m_simple; rules=:identity)
    @test_throws ArgumentError schedule_reductions!(ws_id)
    ws_mix = Workspace(m_simple; rules=:mixed)
    @test_throws ArgumentError schedule_reductions!(ws_mix; tie_break=:middle)
    @test_throws ArgumentError schedule_reductions!(ws_mix; max_fill=-1)
    @test_throws ArgumentError schedule_reductions!(ws_mix; max_total_fill=-1)
    @test_throws ArgumentError schedule_reductions!(ws_mix; relation_work_budget=-1)

    # 2. :optional_pass_disabled when all passes are disabled or stop_on_disabled_optional=true:
    rep_all_off = schedule_reductions!(
        ws_mix;
        enable_dominance=false, enable_elimination=false,
        enable_relations=false, enable_star_triangle=false,
    )
    @test rep_all_off.stop_reason === :optional_pass_disabled
    @test :dominance in rep_all_off.optional_passes_disabled
    @test :elimination in rep_all_off.optional_passes_disabled
    @test :relations in rep_all_off.optional_passes_disabled

    # Star-triangle K_4 with zero field on v1 and stop_on_disabled_optional=true:
    Q_k4 = [0.0 1.0 -1.5 2.0; 0.0 0.0 0.5 -0.75; 0.0 0.0 0.0 1.25; 0.0 0.0 0.0 0.0]
    ws_k4 = Workspace(fixture([:u, :w1, :w2, :w3], [0.0, 0.25, -0.5, 0.75], Q_k4; domain=:spin); rules=:mixed)
    rep_k4_dis = schedule_reductions!(ws_k4; enable_star_triangle=false, stop_on_disabled_optional=true)
    @test rep_k4_dis.stop_reason === :optional_pass_disabled
    @test rep_k4_dis.optional_passes_disabled == (:star_triangle,)
    # Also test stop_on_disabled_optional=true when enable_relations=false on K_4:
    ws_k4_rel = Workspace(fixture([:u, :w1, :w2, :w3], [0.5, 0.25, -0.5, 0.75], Q_k4; domain=:spin); rules=:mixed)
    rep_k4_reldis = schedule_reductions!(ws_k4_rel; enable_relations=false, stop_on_disabled_optional=true)
    @test rep_k4_reldis.stop_reason === :optional_pass_disabled
    @test :relations in rep_k4_reldis.optional_passes_disabled

    # 3. :unsupported_arithmetic:
    #    (a) Zero objective scale:
    ws_zscale = Workspace(fixture([:a, :b], [1.0, -1.0], [0.0 0.5; 0.0 0.0]; scale=0.0, domain=:spin); rules=:mixed)
    rep_zscale = schedule_reductions!(ws_zscale)
    @test rep_zscale.stop_reason === :unsupported_arithmetic

    #    (b) Dominance near-tie requiring exact Rational{BigInt} fallback when allow_exact_fallback=false:
    #        In BoolDomain, a_1 = 1.0, b_{1,2} = -0.25, b_{1,3} = -0.75 + 2.0^-53 -> exact lower = +2^-53 > 0,
    #        but Float64 outward interval prevfloat(1.0 - 0.25) + (-0.75 + 2^-53) rounds to 0.0 -> prevfloat(0.0) < 0!
    L_near = [1.0, 0.5, 0.5]
    Q_near = [0.0 -0.25 (-0.75 + 2.0^-53); 0.0 0.0 -0.25; 0.0 0.0 0.0]
    ws_near = Workspace(fixture([:x1, :x2, :x3], L_near, Q_near; domain=:bool); rules=:mixed)
    cp_near = checkpoint(ws_near)
    rep_near_nofb = schedule_reductions!(ws_near; enable_elimination=false, enable_relations=false, allow_exact_fallback=false)
    @test rep_near_nofb.stop_reason === :unsupported_arithmetic
    @test rep_near_nofb.deductions == 0 && checkpoint(ws_near) == cp_near
    rep_near_fb = schedule_reductions!(ws_near; enable_elimination=false, enable_relations=false, allow_exact_fallback=true)
    @test rep_near_fb.stop_reason === :quiescent
    @test rep_near_fb.dominance_deductions >= 1
    @test rep_near_fb.exact_fallbacks >= 1
    @test verify_certificate(ws_near, export_certificate(ws_near)).valid

    #    (c) Weak/marginal dominance with allow_exact_fallback=false:
    ws_weak_dom = Workspace(fixture([:x1, :x2], [0.0, 0.0], [0.0 1.0; 0.0 0.0]; domain=:bool); rules=:mixed)
    @test schedule_reductions!(ws_weak_dom; allow_weak_dominance=true, allow_exact_fallback=false).stop_reason === :unsupported_arithmetic
    # Marginal dominance (where cached interval straddles 0, so step === nothing before _marginal_dominance_witness):
    ws_marg_dom = Workspace(fixture([:x1, :x2], [1.0, -1.0], [0.0 -2.0; 0.0 0.0]; domain=:bool); rules=:mixed)
    @test schedule_reductions!(ws_marg_dom; allow_weak_dominance=true, allow_exact_fallback=false).stop_reason === :unsupported_arithmetic
    @test schedule_reductions!(ws_marg_dom; allow_weak_dominance=true, allow_exact_fallback=true).stop_reason === :quiescent

    #    (d) Elimination with tie (unique_argmin == false) or high-dynamic-range non-Float64 delta when allow_exact_fallback=false:
    ws_tie_el = Workspace(fixture([:x1, :x2], [0.0, 0.5], [0.0 0.0; 0.0 0.0]; domain=:spin); rules=:mixed)
    @test schedule_reductions!(ws_tie_el; enable_dominance=false, allow_exact_fallback=false).stop_reason === :unsupported_arithmetic
    @test schedule_reductions!(ws_tie_el; enable_dominance=false, allow_exact_fallback=true).stop_reason === :quiescent
    # High dynamic range degree-2 elimination where constant_delta = -(1e16 + 0.25) is not exact Float64:
    ws_hdr = Workspace(fixture([:x1, :x2, :x3], [1e16, 0.5, -0.5], [0.0 1e16 0.5; 0.0 0.0 0.0; 0.0 0.0 0.0]; domain=:spin); rules=:mixed)
    @test schedule_reductions!(ws_hdr; enable_dominance=false, enable_relations=false, allow_exact_fallback=false).stop_reason === :unsupported_arithmetic
    rep_hdr_ok = schedule_reductions!(ws_hdr; enable_dominance=false, enable_relations=false, allow_exact_fallback=true)
    @test rep_hdr_ok.stop_reason === :quiescent && rep_hdr_ok.exact_fallbacks >= 1

    #    (e) Relation requiring GLK pair / exact fallback when allow_exact_fallback=false:
    #        In SpinDomain, h_1 = 0.5, h_2 = 0.5, J_{1,2} = -0.75: single-flip interval has |J_{1,2}| - |h_1| = 0.25 > 0,
    #        whereas for h_1 = 1.0, h_2 = 1.0, J_{1,2} = -0.75, single-flip fails (-0.25 < 0) and GLK pair succeeds (1.5 - 0 = 1.5 > 0)!
    ws_glk = Workspace(fixture([:s1, :s2, :s3, :s4], [1.0, 1.0, 0.25, -0.25],
        [0.0 -0.75 0.1 -0.1; 0.0 0.0 0.1 -0.1; 0.0 0.0 0.0 0.5; 0.0 0.0 0.0 0.0]; domain=:spin); rules=:mixed)
    @test schedule_reductions!(
        ws_glk; enable_dominance=false, enable_elimination=false, allow_exact_fallback=false
    ).stop_reason === :unsupported_arithmetic
    rep_glk_ok = schedule_reductions!(
        ws_glk; enable_dominance=false, enable_elimination=false, allow_exact_fallback=true
    )
    @test rep_glk_ok.stop_reason === :quiescent && rep_glk_ok.relation_deductions >= 1 && rep_glk_ok.exact_fallbacks >= 1

    # 4. :fill_limit (both per-step max_fill and cumulative max_total_fill) across elimination, star-triangle, and relations:
    #    Construct an 8-vertex graph with:
    #    - degree-2 vertex :v1 between :v3 and :v4 (not connected -> fill == 1)
    #    - degree-2 vertex :v2 between :v5 and :v6 (not connected -> fill == 1)
    #    - core vertices :v3..:v8 with degree >= 3 so they aren't degree-2 initially
    L_fl = [0.25, -0.25, 0.5, -0.5, 0.3, -0.3, 0.4, -0.4]
    Q_fl = zeros(8, 8)
    Q_fl[1, 3] = 1.0; Q_fl[1, 4] = -1.25 # eliminating v1 adds fill edge (3, 4)
    Q_fl[2, 5] = 1.0; Q_fl[2, 6] = -1.25 # eliminating v2 adds fill edge (5, 6)
    Q_fl[3, 5] = 0.5; Q_fl[3, 7] = -0.5; Q_fl[3, 8] = 0.5
    Q_fl[4, 6] = 0.5; Q_fl[4, 7] = -0.5; Q_fl[4, 8] = 0.5
    Q_fl[5, 7] = 0.5; Q_fl[5, 8] = -0.5
    Q_fl[6, 7] = -0.5; Q_fl[6, 8] = 0.5
    Q_fl[7, 8] = 1.0
    ws_fl = Workspace(fixture([Symbol("v$i") for i in 1:8], L_fl, Q_fl; domain=:spin); rules=:mixed)
    # With max_fill=0, both v1 and v2 are blocked by fill -> stops with :fill_limit and 0 deductions:
    rep_fl0 = schedule_reductions!(ws_fl; enable_relations=false, max_fill=0)
    @test rep_fl0.stop_reason === :fill_limit
    @test rep_fl0.deductions == 0 && rep_fl0.fill_edges == 0
    # With max_fill=1 and max_total_fill=1, v1 is eliminated (fill_edges=1), then eff_fill drops to 0 so v2 is blocked -> :fill_limit!
    rep_fl1 = schedule_reductions!(ws_fl; enable_relations=false, max_fill=1, max_total_fill=1)
    @test rep_fl1.stop_reason === :fill_limit
    @test rep_fl1.elimination_deductions == 1 && rep_fl1.fill_edges == 1
    # Increasing max_total_fill=2 on the same workspace unblocks v2 and reaches :quiescent!
    rep_fl2 = schedule_reductions!(ws_fl; enable_relations=false, max_fill=1, max_total_fill=2)
    @test rep_fl2.stop_reason === :quiescent
    @test rep_fl2.elimination_deductions == 1 && rep_fl2.fill_edges == 1
    @test verify_certificate(ws_fl, export_certificate(ws_fl)).valid

    # Also test :fill_limit on :star_triangle (bucket 4) and :relations:
    # Star-triangle on 8-vertex graph where v1 has degree 3, zero field, and actual_fill == 2:
    L_stf = [0.0, 0.25, -0.5, 0.75, 0.1, -0.2, 0.3, -0.4]
    Q_stf = zeros(8, 8)
    Q_stf[1, 2] = 1.0; Q_stf[1, 3] = 1.0; Q_stf[1, 4] = 3.0
    for i in 2:4, j in 5:8
        Q_stf[i, j] = 0.5 * ((i + j) % 2 == 0 ? 1 : -1)
    end
    for i in 5:8, j in (i+1):8
        Q_stf[i, j] = 1.0
    end
    ws_stf = Workspace(fixture([Symbol("v$i") for i in 1:8], L_stf, Q_stf; domain=:spin); rules=:mixed)
    rep_stf1 = schedule_reductions!(ws_stf; enable_relations=false, enable_star_triangle=true, max_fill=1)
    @test rep_stf1.stop_reason === :fill_limit && rep_stf1.deductions == 0
    rep_stf2 = schedule_reductions!(ws_stf; enable_relations=false, enable_star_triangle=true, max_fill=2)
    @test rep_stf2.stop_reason === :quiescent && rep_stf2.star_triangle_deductions == 1

    # Relation fill limit where contracting (1, 2) introduces 1 fill edge:
    L_rf = [0.0, 0.0, 0.25, -0.25, 0.5]
    Q_rf = [
        0.0 -10.0  1.0  1.0  0.0;
        0.0   0.0  1.0  0.0  1.0;
        0.0   0.0  0.0  1.0  1.0;
        0.0   0.0  0.0  0.0  1.0;
        0.0   0.0  0.0  0.0  0.0
    ]
    ws_rf = Workspace(fixture([:r1, :r2, :c1, :c2, :c3], L_rf, Q_rf; domain=:spin); rules=:mixed)
    rep_rf0 = schedule_reductions!(ws_rf; enable_dominance=false, enable_elimination=false, max_fill=0)
    @test rep_rf0.stop_reason === :fill_limit && rep_rf0.deductions == 0
    rep_rf_dis = schedule_reductions!(
        ws_rf; enable_dominance=false, enable_elimination=false,
        enable_relations=false, stop_on_disabled_optional=true, max_fill=1,
    )
    @test rep_rf_dis.stop_reason === :optional_pass_disabled && :relations in rep_rf_dis.optional_passes_disabled
    rep_rf1 = schedule_reductions!(ws_rf; enable_dominance=false, enable_elimination=false, max_fill=1)
    @test rep_rf1.stop_reason === :quiescent && rep_rf1.relation_deductions >= 1

    # 5. Work limits, verification limits, relation_work_budget, and deadline_ns across all 4 passes,
    #    plus resumption to exact quiescence without duplicate deductions or lost work:
    labels7 = [:v1, :v2, :v3, :v4, :v5, :v6, :v7]
    L7 = [5.0, 0.5, 0.25, -0.25, 0.0, 0.25, -0.5]
    Q7 = zeros(7, 7)
    Q7[1, 2] = 1.0; Q7[2, 3] = -0.5; Q7[3, 4] = -6.0
    Q7[3, 5] = 0.5; Q7[3, 6] = 0.5; Q7[4, 5] = 0.5
    Q7[4, 6] = 0.5; Q7[4, 7] = 1.0; Q7[5, 6] = -1.0
    Q7[5, 7] = 1.0; Q7[6, 7] = -1.0
    m7 = fixture(labels7, L7, Q7; domain=:spin)
    # Tight single-call work_limit and verification_limit across passes:
    ws_wl1 = Workspace(m7; rules=:mixed)
    @test schedule_reductions!(ws_wl1; max_work=1).stop_reason === :work_limit
    @test schedule_reductions!(ws_wl1; max_exact_work=1).stop_reason === :verification_limit
    @test schedule_reductions!(ws_wl1; enable_dominance=false, max_work=1).stop_reason === :work_limit
    @test schedule_reductions!(ws_wl1; enable_dominance=false, max_exact_work=1).stop_reason === :verification_limit

    for w_step in (18, 25)
        ws_res = Workspace(m7; rules=:mixed)
        total_d = 0
        iters = 0
        while true
            iters += 1
            r = schedule_reductions!(ws_res; enable_star_triangle=true, max_work=w_step)
            total_d += r.deductions
            r.stop_reason === :quiescent && break
            @test r.stop_reason === :work_limit
            @test iters <= 30
            iters <= 30 || break
        end
        @test total_d == 7
        @test ws_res._state.active_edges == 0
        @test verify_certificate(ws_res, export_certificate(ws_res)).valid
    end
    for x_step in (18, 25)
        ws_res = Workspace(m7; rules=:mixed)
        total_d = 0
        iters = 0
        while true
            iters += 1
            r = schedule_reductions!(ws_res; enable_star_triangle=true, max_exact_work=x_step)
            total_d += r.deductions
            r.stop_reason === :quiescent && break
            @test r.stop_reason === :verification_limit
            @test iters <= 30
            iters <= 30 || break
        end
        @test total_d == 7
        @test verify_certificate(ws_res, export_certificate(ws_res)).valid
    end
    # relation_work_budget limit:
    ws_relb = Workspace(m7; rules=:mixed)
    rep_relb = schedule_reductions!(ws_relb; relation_work_budget=1)
    @test rep_relb.stop_reason === :work_limit
    @test any(p -> p.pass === :relations && p.stop_reason === :work_limit, rep_relb.passes)
    # Resuming with unrestricted relation_work_budget completes:
    rep_relb2 = schedule_reductions!(ws_relb; enable_star_triangle=true)
    @test rep_relb2.stop_reason === :quiescent && rep_relb2.residual_variables == 0

    # Expired deadline_ns across each pass (:dominance, :elimination, :star_triangle, :relations):
    ws_dl_dom = Workspace(m7; rules=:mixed)
    @test schedule_reductions!(ws_dl_dom; deadline_ns=UInt64(1)).stop_reason === :deadline
    ws_dl_el = Workspace(m7; rules=:mixed)
    @test schedule_reductions!(ws_dl_el; enable_dominance=false, deadline_ns=UInt64(1)).stop_reason === :deadline
    ws_dl_st = Workspace(fixture([:u, :w1, :w2, :w3], [0.0, 0.25, -0.5, 0.75], Q_k4; domain=:spin); rules=:mixed)
    @test schedule_reductions!(
        ws_dl_st; enable_dominance=false, enable_elimination=false, enable_star_triangle=true, deadline_ns=UInt64(1)
    ).stop_reason === :deadline
    ws_dl_rel = Workspace(m7; rules=:mixed)
    @test schedule_reductions!(
        ws_dl_rel; enable_dominance=false, enable_elimination=false, enable_relations=true, deadline_ns=UInt64(1)
    ).stop_reason === :deadline

    # Deduction limit in each pass (:dominance, :elimination, :star_triangle, :relations):
    ws_dd = Workspace(m7; rules=:mixed)
    @test schedule_reductions!(ws_dd; max_deductions=0).stop_reason === :deduction_limit
    @test schedule_reductions!(ws_dd; enable_dominance=false, max_deductions=0).stop_reason === :deduction_limit
    @test schedule_reductions!(
        ws_dl_st; enable_dominance=false, enable_elimination=false, enable_star_triangle=true, max_deductions=0
    ).stop_reason === :deduction_limit
    @test schedule_reductions!(
        ws_dd; enable_dominance=false, enable_elimination=false, enable_relations=true, max_deductions=0
    ).stop_reason === :deduction_limit
end

@testset "no-dirty-work O(1) overhead and scale-invariant local updates (n=10 vs n=2000)" begin
    function build_sparse_ring_with_gadget(n::Int)
        # Vertices 1..4 form a local reducible gadget; vertices 5..n form a balanced 4-regular ring+chords
        # where no dominance, low-degree elimination (deg == 4), or relation applies!
        I_idx = Int[]
        J_idx = Int[]
        V_val = Float64[]
        L = zeros(Float64, n)
        # Local gadget on 1..4:
        L[1] = 4.0; L[2] = 0.5; L[3] = -0.25; L[4] = 0.75
        push!(I_idx, 1); push!(J_idx, 2); push!(V_val, 1.0)
        push!(I_idx, 2); push!(J_idx, 3); push!(V_val, -1.5)
        push!(I_idx, 3); push!(J_idx, 4); push!(V_val, 1.0)
        # 4-regular background on 5..n:
        m_ring = n - 4
        if m_ring >= 6
            for k in 0:(m_ring - 1)
                u = 5 + k
                v1 = 5 + ((k + 1) % m_ring)
                v2 = 5 + ((k + 2) % m_ring)
                L[u] = isodd(u) ? 0.25 : -0.25
                a1, b1 = minmax(u, v1)
                push!(I_idx, a1); push!(J_idx, b1); push!(V_val, isodd(k) ? 1.0 : -1.0)
                a2, b2 = minmax(u, v2)
                push!(I_idx, a2); push!(J_idx, b2); push!(V_val, isodd(k) ? -1.0 : 1.0)
            end
        end
        Q = sparse(I_idx, J_idx, V_val, n, n)
        return QT.Model{Int,Float64,Int}(collect(1:n), SparseVector(L), Q; domain=:spin, sense=:min)
    end

    m10 = build_sparse_ring_with_gadget(10)
    m2000 = build_sparse_ring_with_gadget(2000)
    ws10, r10_init = preprocess(m10; rules=:mixed, enable_star_triangle=true)
    ws2000, r2000_init = preprocess(m2000; rules=:mixed, enable_star_triangle=true)
    @test r10_init.stop_reason === :quiescent && r10_init.deductions == 4
    @test r2000_init.stop_reason === :quiescent && r2000_init.deductions == 4

    # Warm up no-dirty-work call:
    schedule_reductions!(ws10; enable_star_triangle=true)
    schedule_reductions!(ws2000; enable_star_triangle=true)

    # Second call with no dirty work performs 0 candidate/edge/exact work and O(1) allocation independent of n:
    b10_idle = @allocated (r10_idle = schedule_reductions!(ws10; enable_star_triangle=true))
    b2000_idle = @allocated (r2000_idle = schedule_reductions!(ws2000; enable_star_triangle=true))
    @test r10_idle.stop_reason === :quiescent
    @test r2000_idle.stop_reason === :quiescent
    @test r10_idle.candidates == 0 && r10_idle.edge_visits == 0 && r10_idle.exact_work == 0 && r10_idle.pending == 0
    @test r2000_idle.candidates == 0 && r2000_idle.edge_visits == 0 && r2000_idle.exact_work == 0 && r2000_idle.pending == 0
    @test isempty(r10_idle.passes) && isempty(r2000_idle.passes)
    @test b2000_idle <= max(4096, 2 * b10_idle)

    # Local branch/propagate/rollback cycle on vertex 5 (degree 4 in both n=10 and n=2000) touches only its 4 neighbors:
    function local_branch_cycle!(ws)
        cp = checkpoint(ws)
        u_rep = assume!(ws, 5, 1)
        s_rep = schedule_reductions!(ws; enable_relations=false)
        rollback!(ws, cp)
        return u_rep, s_rep
    end
    u10, s10 = local_branch_cycle!(ws10)
    u2000, s2000 = local_branch_cycle!(ws2000)
    b10_loc = @allocated local_branch_cycle!(ws10)
    b2000_loc = @allocated local_branch_cycle!(ws2000)
    @test u10.edge_visits == u2000.edge_visits == 4
    @test s10.candidates == s2000.candidates == 4
    @test s10.edge_visits == s2000.edge_visits == 0
    @test s10.exact_work == s2000.exact_work == 4
    @test b2000_loc <= max(8192, 2 * b10_loc)
end

@testset "pipeline accounting across all seven lifecycle phases and ablation fixtures" begin
    R = Rational{BigInt}
    # 1. Exercise audit_pipeline! across :identity, :dominance, :elimination, :relations, and :mixed
    #    with both Model and Workspace inputs, plus domain/gauge mapping:
    labels = [:v1, :v2, :v3, :v4, :v5]
    L_f = [4.0, 0.5, 0.0, 0.0, -0.5]
    Q_f = [
        0.0  1.0  0.0  0.0  0.0;
        0.0  0.0 -0.5  0.0  0.0;
        0.0  0.0  0.0 -5.0  1.0;
        0.0  0.0  0.0  0.0  1.0;
        0.0  0.0  0.0  0.0  0.0
    ]
    m = fixture(labels, L_f, Q_f; domain=:spin)
    for rmode in (:identity, :dominance, :elimination, :relations, :mixed)
        ws_a, acct = audit_pipeline!(m; rules=rmode, domain=:bool, gauge=[-1, 1, -1, 1, -1])
        @test acct isa PipelineAccounting
        @test generation(acct) == generation(ws_a)
        @test acct.rules === rmode
        @test acct.stop_reason === :quiescent
        @test acct.verified
        @test acct.initial_variables == 5 && acct.initial_edges == 5
        @test acct.conversion_import.phase === :conversion_import && acct.conversion_import.stop_reason === :applied
        @test acct.conversion_import.work_units > 0 && acct.conversion_import.bytes_allocated >= 0
        @test acct.discovery.phase === :discovery && acct.discovery.stop_reason === :quiescent
        @test acct.arithmetic_fallback.phase === :arithmetic_fallback
        @test acct.verification.phase === :verification && acct.verification.stop_reason === :verified
        @test acct.export_phase.phase === :export && acct.export_phase.stop_reason === :certified
        @test acct.reconstruction.phase === :reconstruction && acct.reconstruction.stop_reason === :reconstructed
        @test acct.rollback_replay.phase === :rollback_replay && acct.rollback_replay.stop_reason === :applied
        @test acct.rollback_replay.work_units > 0
    end

    # Also test audit_pipeline! with an existing Workspace and partial residual remaining (so post-discovery LIFO rollback runs):
    m_partial = fixture([:a, :b, :c, :d], [4.0, 0.25, -0.25, 0.5],
        [0.0 0.5 0.0 0.0; 0.0 0.0 1.0 -1.0; 0.0 0.0 0.0 1.0; 0.0 0.0 0.0 0.0]; domain=:spin)
    ws_part = Workspace(m_partial; rules=:mixed)
    _, acct_part = audit_pipeline!(ws_part; rules=:mixed, domain=:spin, gauge=[1, -1, 1, -1], enable_relations=false, enable_elimination=false)
    @test acct_part.stop_reason === :quiescent
    @test acct_part.residual_variables == 3
    @test acct_part.rollback_replay.work_units > 0

    # Budget/deadline interruptions at each phase boundary of audit_pipeline!:
    _, acct_dl0 = audit_pipeline!(m; rules=:mixed, deadline_ns=UInt64(1))
    @test acct_dl0.stop_reason === :deadline && acct_dl0.conversion_import.stop_reason === :deadline
    _, acct_w0 = audit_pipeline!(m; rules=:mixed, max_work=2)
    @test acct_w0.stop_reason === :work_limit && acct_w0.conversion_import.stop_reason === :work_limit
    ws_w_pre = Workspace(m; rules=:mixed)
    _, acct_w_ws = audit_pipeline!(ws_w_pre; rules=:mixed, max_work=2)
    @test acct_w_ws.stop_reason === :work_limit && acct_w_ws.conversion_import.stop_reason === :work_limit
    # Stop during rollback_replay (import needs 5+5+1=11 units):
    _, acct_w_rr = audit_pipeline!(m; rules=:mixed, max_work=11)
    @test acct_w_rr.rollback_replay.stop_reason === :work_limit && acct_w_rr.stop_reason === :work_limit
    _, acct_w_rr2 = audit_pipeline!(m; rules=:mixed, max_work=13)
    @test acct_w_rr2.rollback_replay.stop_reason === :work_limit && acct_w_rr2.stop_reason === :work_limit
    _, acct_w_rr3 = audit_pipeline!(m; rules=:mixed, max_work=15)
    @test acct_w_rr3.rollback_replay.stop_reason === :work_limit && acct_w_rr3.stop_reason === :work_limit
    # Stop during verification / export / reconstruction (with exercise_rollback_replay=false):
    _, acct_w_ver = audit_pipeline!(m; rules=:mixed, exercise_rollback_replay=false, max_work=38)
    @test !acct_w_ver.verified && acct_w_ver.stop_reason === :work_limit
    _, acct_w_exp = audit_pipeline!(m; rules=:identity, exercise_rollback_replay=false, max_work=12)
    @test acct_w_exp.export_phase.stop_reason === :work_limit && acct_w_exp.reconstruction.stop_reason === :not_run
    _, acct_w_rec = audit_pipeline!(m; rules=:identity, exercise_rollback_replay=false, max_work=25)
    @test acct_w_rec.export_phase.stop_reason === :certified && acct_w_rec.reconstruction.stop_reason === :work_limit
end

