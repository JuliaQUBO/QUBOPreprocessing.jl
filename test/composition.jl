# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

@testset "guarantee taxonomy, persistency and record constructors" begin
    ws = Workspace(fixture([:x, :y, :z], [3.0, 0.0, 0.0], [0.0 -1.0 0.0; 0.0 0.0 0.0; 0.0 0.0 0.0]))
    gmap = domain_map(ws; domain=:spin, gauge=[-1, 1, -1])
    @test ReductionCertificate === DominanceCertificate
    @test step_guarantee(gmap) === :energy_identity
    @test persistency(gmap) === :strong

    d_strong = DominanceStep(1, 0, big(1)//1, big(2)//1, big(0)//1, 0, :exact)
    d_Strong8 = DominanceStep(1, 0, big(1)//1, big(2)//1, big(0)//1, 0, :exact, 0)
    d_weak = DominanceStep(1, 0, big(0)//1, big(1)//1, big(0)//1, 0, :exact, 0, :weak)
    @test d_strong.scope_length == -1 && d_strong.persistency === :strong
    @test d_Strong8.scope_length == 0 && d_Strong8.persistency === :strong
    @test step_guarantee(d_strong) === :optimum_preserving_restriction
    @test persistency(d_strong) === :strong
    @test persistency(d_weak) === :weak

    r_strong = RelationStep(1, 2, 1, 1, big(1)//1, big(2)//1, big(0)//1, 0, :exact)
    r_strong10 = RelationStep(1, 2, 1, 1, big(1)//1, big(2)//1, big(0)//1, 0, :exact, 0)
    r_weak = RelationStep(1, 2, -1, -1, big(0)//1, big(1)//1, big(0)//1, 0, :exact, 0, :weak)
    @test r_strong.scope_length == -1 && r_strong.persistency === :strong
    @test r_strong10.scope_length == 0 && r_strong10.persistency === :strong
    @test step_guarantee(r_strong) === :optimum_preserving_restriction
    @test persistency(r_strong) === :strong
    @test persistency(r_weak) === :weak

    e_strict = EliminationStep(3, (), (0,), big(0)//1, (), (), big(0)//1, 0)
    e_tie = EliminationStep(3, (), (0,), big(0)//1, (), (), big(0)//1, 0, 0, false)
    @test e_strict.scope_length == -1 && e_strict.unique_argmin
    @test step_guarantee(e_strict) === :exact_elimination
    @test persistency(e_strict) === :strong
    @test persistency(e_tie) === :weak

    c_empty = DominanceCertificate(generation(ws), checkpoint(ws), (), (), ws._snapshot)
    c_elim = DominanceCertificate(generation(ws), checkpoint(ws), (), (e_strict,), ws._snapshot)
    c_mixed = DominanceCertificate(generation(ws), checkpoint(ws), (), (e_strict, r_weak), ws._snapshot)
    @test certificate_guarantee(c_empty) === :energy_identity
    @test certificate_guarantee(c_elim) === :exact_elimination
    @test certificate_guarantee(c_mixed) === :optimum_preserving_restriction
    @test persistency(c_elim) === :strong
    @test persistency(c_mixed) === :weak
end

function assert_universal_lifting_and_persistency(
    res,
    L_orig,
    Q_orig,
    scale_orig,
    offset_orig,
    domain::Symbol,
    sense::Symbol,
    optima,
    opt_energy,
)
    R = Rational{BigInt}
    res_model = export_model(res)
    m = QT.dimension(res_model)
    res_dom = res._map === nothing ? domain : res._map.target_domain
    L_res = R[res._linear...]
    Q_res = zeros(R, m, m)
    for (i, j, q) in res._quadratic
        Q_res[i, j] = R(q)
    end
    scale_res = R(res._scale)
    offset_res = R(res._constant)

    # 1. Every residual state's residual energy matches the original energy of its reconstructed state.
    for y in states(m, res_dom)
        rec = reconstruct(res, y)
        e_res = reference(L_res, Q_res, scale_res, offset_res, y, R)
        e_orig = reference(L_orig, Q_orig, scale_orig, offset_orig, rec.state, R)
        @test e_res == e_orig
    end

    # 2. Universal lifting guarantee: independently identify ALL residual optima and verify
    # that EVERY residual optimum lifts to an original global optimum with matching optimal energy.
    res_optima = oracle_optima(L_res, Q_res, scale_res, offset_res, res_dom, sense, ())
    @test !isempty(res_optima)
    lifted_optima = Vector{Int}[]
    for y_opt in res_optima
        e_res_opt = reference(L_res, Q_res, scale_res, offset_res, y_opt, R)
        @test e_res_opt == opt_energy
        rec_opt = reconstruct(res, y_opt)
        @test rec_opt.state in optima
        @test reference(L_orig, Q_orig, scale_orig, offset_orig, rec_opt.state, R) == opt_energy
        push!(lifted_optima, rec_opt.state)
    end

    # 3. Strong persistency guarantee: check every :strong step against EVERY original optimum.
    steps = res.certificate.reduction_chain
    for step in steps
        persistency(step) === :strong || continue
        for x_opt in optima
            if step isa DominanceStep
                @test x_opt[step.variable] == step.value
            elseif step isa RelationStep
                s_u = domain === :bool ? (2 * x_opt[step.eliminated] - 1) : x_opt[step.eliminated]
                s_v = domain === :bool ? (2 * x_opt[step.representative] - 1) : x_opt[step.representative]
                @test s_u == step.orig_sign * s_v
            elseif step isa EliminationStep
                idx = 1
                for (bit_pos, nbr) in enumerate(step.neighbors)
                    x_opt[nbr] == 1 && (idx += 1 << (bit_pos - 1))
                end
                @test x_opt[step.variable] == step.table[idx]
            end
        end
    end

    # 4. When all steps are :strong, EVERY original optimum is preserved and recovered by lifting.
    if all(s -> persistency(s) === :strong, steps)
        @test Set(lifted_optima) == Set(optima)
    end
end

@testset "end-to-end composed chains and reverse-order reconstruction" begin
    R = Rational{BigInt}
    # 5-variable model where:
    # 1. Variable 1 is strongly dominated (fixed to low).
    # 2. Variable 2 and 3 have a strong pair relation (both +1 equality and -1 anti-equality tested).
    # 3. Variable 4 has degree 2 (coupled to 3 and 5) and is locally eliminated (producing a fill/updated edge and cancelling/modifying fields).
    # 4. Variable 3 is then strongly dominated on the reduced residual, leaving only variable 5 (or eliminating 5 as degree 0).
    labels = [:v1, :v2, :v3, :v4, :v5]
    for domain in (:bool, :spin), sense in (:min, :max), scale in (1.0, -2.0), rel_sign in (1, -1)
        dir = (sense === :min ? 1 : -1) * (scale < 0 ? -1 : 1)
        # Construct in spin coordinates first, then convert to bool if domain === :bool so both domains test the exact same physics.
        h_spin = R[dir * 6, dir * 1, 0, dir * 1, dir * (-2)]
        J_spin = zeros(R, 5, 5)
        J_spin[1, 2] = dir * R(1)
        J_spin[2, 3] = -dir * rel_sign * R(6) # strong relation s_2 = rel_sign * s_3
        J_spin[2, 4] = dir * R(1)
        J_spin[2, 5] = dir * R(1)
        J_spin[3, 4] = dir * R(2)
        J_spin[4, 5] = -dir * R(2)
        J_spin[3, 5] = -rel_sign * J_spin[2, 5] # chosen so relation contraction cancels edge (3, 5) to 0!
        L_float, Q_float, offset_val = if domain === :spin
            Float64.(h_spin), Float64.(J_spin), 0.5
        else
            Q_b = 4 .* J_spin
            L_b = [2 * h_spin[i] - sum(2 * J_spin[min(i, j), max(i, j)] for j in 1:5 if j != i) for i in 1:5]
            c_b = R(1//2) - sum(h_spin) + sum(J_spin[i, j] for i in 1:5 for j in (i+1):5)
            Float64.(L_b), Float64.(Q_b), Float64(c_b)
        end
        model = fixture(labels, L_float, Q_float; domain, sense, scale, offset=offset_val)
        optima = oracle_optima(L_float, Q_float, scale, offset_val, domain, sense, ())
        opt_energy = reference(L_float, Q_float, scale, offset_val, first(optima), R)

        ws = Workspace(model; rules=:dominance)
        gmap = domain_map(ws; domain=(domain === :bool ? :spin : :bool), gauge=[-1, 1, -1, 1, -1])
        cp0 = checkpoint(ws)

        # Step 1: Dominance on :v1
        p_dom = prove_dominance(ws, :v1; map=gmap)
        @test p_dom.stop_reason === :proved
        @test verify_certificate(ws, p_dom.certificate; map=gmap).valid
        rep1 = apply_dominance!(ws, :v1; map=gmap)
        @test rep1.stop_reason === :applied
        cp1 = checkpoint(ws)

        # Step 2: Relation contraction eliminating :v2 onto :v3
        p_rel = prove_relation(ws, :v2, :v3; map=gmap)
        @test p_rel.stop_reason === :proved
        @test verify_certificate(ws, p_rel.certificate; map=gmap).valid
        rep2 = contract_relation!(ws, :v2, :v3; map=gmap)
        @test rep2.stop_reason === :applied
        @test degree(ws, :v2) == 0
        # Notice edge (3, 5) was cancelled to 0 by the relation contraction!
        @test conditioned_constant(ws; map=gmap) == QUBOPreprocessing._direct_mapped_constant(ws, gmap)
        cp2 = checkpoint(ws)

        # Step 3: Local elimination of degree-2 variable :v4 (neighbors :v3 and :v5)
        @test degree(ws, :v4) == 2
        p_elim = prove_elimination(ws, :v4; map=gmap, tie_break=:high)
        @test p_elim.stop_reason === :proved
        @test verify_certificate(ws, p_elim.certificate; map=gmap).valid
        rep3 = eliminate_variable!(ws, :v4; map=gmap, tie_break=:high)
        @test rep3.stop_reason === :applied
        @test degree(ws, :v4) == 0
        # Eliminating :v4 introduces a fill edge between :v3 and :v5!
        @test conditioned_constant(ws; map=gmap) == QUBOPreprocessing._direct_mapped_constant(ws, gmap)
        cp3 = checkpoint(ws)

        # Verify intermediate composed export & certificate transport
        cert3 = export_certificate(ws)
        @test length(cert3.steps) == 3
        @test cert3.steps[1] isa DominanceStep
        @test cert3.steps[2] isa RelationStep
        @test cert3.steps[3] isa EliminationStep
        @test verify_certificate(ws, cert3).valid
        t_cert3 = transport_certificate(ws, cert3, gmap)
        @test verify_certificate(ws, t_cert3; map=gmap).valid
        @test verify_certificate(ws, export_certificate(ws; map=gmap); map=gmap).valid
        @test length(reductions(ws)) == 3
        @test length(reductions(ws; since=cp1)) == 2
        @test length(deductions(ws)) == 1

        # Reconstruct from intermediate 2-variable residual (:v3, :v5) in both unmapped and mapped exports
        for active_map in (nothing, gmap)
            res = active_map === nothing ? materialize(ws; coefficient_type=R) :
                                           materialize(ws, active_map; coefficient_type=R)
            assert_universal_lifting_and_persistency(
                res, L_float, Q_float, scale, offset_val, domain, sense, optima, opt_energy,
            )
        end

        # Step 4: Eliminate :v3 (degree 1) and :v5 (degree 0) to reduce to 0 variables!
        @test eliminate_variable!(ws, :v3; map=gmap).stop_reason === :applied
        @test eliminate_variable!(ws, :v5; map=gmap).stop_reason === :applied
        full_export = materialize(ws; coefficient_type=R)
        @test QT.dimension(export_model(full_export)) == 0
        @test verify_certificate(ws, full_export.certificate.proof).valid
        assert_universal_lifting_and_persistency(
            full_export, L_float, Q_float, scale, offset_val, domain, sense, optima, opt_energy,
        )

        # Rollback step-by-step and verify exact state restoration
        rollback!(ws, cp3)
        @test verify_certificate(ws, cert3).valid
        rollback!(ws, cp2)
        @test degree(ws, :v4) == 2
        rollback!(ws, cp1)
        @test degree(ws, :v2) > 0
        rollback!(ws, cp0)
        @test isempty(reductions(ws))
        @test all(==(2), ws._state.fixed)
        @test conditioned_constant(ws; map=gmap) == QUBOPreprocessing._direct_mapped_constant(ws, gmap)
    end
end

@testset "relation -> elimination -> dominance order and degree-3 quadratic elimination" begin
    R = Rational{BigInt}
    # Order: RelationStep -> EliminationStep -> DominanceStep
    # F(x1, x2, x3) = 4*(x1 - x2)^2 + 2*x1*x3 - x3 = 4*x1 + 4*x2 - 8*x1*x2 + 2*x1*x3 - x3
    L = [4.0, 4.0, -1.0]
    Q = [0.0 -8.0 2.0; 0.0 0.0 0.0; 0.0 0.0 0.0]
    ws = Workspace(fixture([:x1, :x2, :x3], L, Q); rules=:dominance)
    # Initially :x2 has no strict dominance (field 4, coupling -8 => bounds [-4, 4])
    @test prove_dominance(ws, :x2).stop_reason === :not_strict
    # Step 1: RelationStep x1 = x2
    @test contract_relation!(ws, :x1, :x2).stop_reason === :applied
    # Step 2: EliminationStep on :x3 (coupled to :x2 with q = 2, field = -1)
    @test eliminate_variable!(ws, :x3).stop_reason === :applied
    # Step 3: After eliminating :x3, :x2 has field +1 > 0, so DominanceStep fixes :x2 = 0!
    @test propagate!(ws).deductions == 1
    @test deductions(ws) == [:x2 => 0]
    cert = export_certificate(ws)
    @test [ typeof(s) for s in cert.steps ] == [RelationStep, EliminationStep, DominanceStep]
    @test verify_certificate(ws, cert).valid
    exported = materialize(ws)
    rec = reconstruct(exported, Int[])
    @test rec.state == [0, 0, 1]
    @test reference(L, Q, 1.0, 0.0, rec.state, R) == -1//1

    # Degree-3 variable with alpha_123 == 0 (quadratic exact marginal):
    # If u has strong field f_u = 10 and couplings q_{u,1} = -1, q_{u,2} = -1, q_{u,3} = -1,
    # then L_u(z) > 0 for all 8 boundary states, so phi(z) is linear/constant (alpha_123 == 0).
    L3 = [10.0, 1.0, -1.0, 2.0]
    Q3 = [0.0 -1.0 -1.0 -1.0; 0.0 0.0 0.5 0.0; 0.0 0.0 0.0 -0.5; 0.0 0.0 0.0 0.0]
    ws3 = Workspace(fixture([:u, :w1, :w2, :w3], L3, Q3))
    @test degree(ws3, :u) == 3
    @test prove_elimination(ws3, :u).stop_reason === :degree_too_high
    att3 = prove_elimination(ws3, :u; max_degree=3)
    @test att3.stop_reason === :proved
    @test verify_certificate(ws3, att3.certificate).valid
    @test eliminate_variable!(ws3, :u; max_degree=3).stop_reason === :applied

    # Degree-3 variable with nonzero cubic term alpha_123 != 0 is refused with :nonquadratic_elimination:
    # For u in {0, 1} with f_u = -1.0 and couplings +2.0 to w1, w2, w3:
    # phi(0,0,0) = -1, phi(1,0,0) = 0, phi(1,1,0) = 0, phi(1,1,1) = 0 => alpha_123 = 0 - 0 + 0 - (-1) = +1 != 0.
    L_cubic = [-1.0, 0.0, 0.0, 0.0]
    Q_cubic = [0.0 2.0 2.0 2.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]
    ws_cubic = Workspace(fixture([:u, :w1, :w2, :w3], L_cubic, Q_cubic))
    @test prove_elimination(ws_cubic, :u; max_degree=3).stop_reason === :nonquadratic_elimination
    @test eliminate_variable!(ws_cubic, :u; max_degree=3).stop_reason === :nonquadratic_elimination
end

@testset "weak persistency is sequential, opt-in and rejects incompatible batches" begin
    R = Rational{BigInt}
    # Antiferromagnetic pair: F(x, y) = 1 - x - y + 2*x*y
    # Optima are (0, 1) and (1, 0) with energy 0; (0, 0) and (1, 1) have energy 1.
    L = [-1.0, -1.0]
    Q = [0.0 2.0; 0.0 0.0]
    model = fixture([:x, :y], L, Q; offset=1.0)
    ws = Workspace(model; rules=:dominance)

    # 1. Default propagate!(ws) is strong-only and makes 0 deductions on the symmetric pair.
    rep_strong = propagate!(ws)
    @test rep_strong.deductions == 0
    @test isempty(deductions(ws))

    # 2. Individually, x = 0 is a valid weak restriction and y = 0 is also a valid weak restriction.
    ws_fresh = Workspace(model; rules=:dominance)
    px = prove_dominance(ws_fresh, :x; value=0, allow_weak=true)
    py = prove_dominance(ws_fresh, :y; value=0, allow_weak=true)
    @test px.stop_reason === :proved && persistency(only(px.certificate.steps)) === :weak
    @test py.stop_reason === :proved && persistency(only(py.certificate.steps)) === :weak
    @test verify_certificate(ws_fresh, px.certificate).valid
    @test verify_certificate(ws_fresh, py.certificate).valid

    # 3. Combining both individual weak steps without re-checking the conditioned residual is rejected by verify_certificate!
    sx = only(px.certificate.steps)
    sx_strong = DominanceStep(sx.variable, sx.value, sx.lower, sx.upper, sx.constant, 0, :marginal, sx.scope_length, :strong)
    @test verify_certificate(ws_fresh, DominanceCertificate(generation(ws_fresh), checkpoint(ws_fresh), (), (sx_strong,), ws_fresh._snapshot)).stop_reason === :invalid_bound
    sy_raw = only(py.certificate.steps)
    sy_forged = DominanceStep(sy_raw.variable, sy_raw.value, sy_raw.lower, sy_raw.upper,
                              sy_raw.constant, 1, sy_raw.method, sy_raw.scope_length, :weak)
    forged_cert = DominanceCertificate(generation(ws_fresh), checkpoint(ws_fresh), (), (sx, sy_forged), ws_fresh._snapshot)
    v_forged = verify_certificate(ws_fresh, forged_cert)
    @test !v_forged.valid
    @test v_forged.stop_reason === :invalid_bound

    # 4. Sequential application via apply_weak_batch! prevents applying both x=0 and y=0:
    cp_root = checkpoint(ws_fresh)
    batch_atomic = apply_weak_batch!(ws_fresh, [:x => 0, :y => 0]; atomic=true)
    @test batch_atomic.applied == 0
    @test batch_atomic.rejected == 1
    @test batch_atomic.stop_reason === :not_strict
    @test isempty(deductions(ws_fresh))

    batch_seq = apply_weak_batch!(ws_fresh, [:x => 0, :y => 0]; atomic=false)
    @test batch_seq.applied == 1
    @test batch_seq.rejected == 1
    @test deductions(ws_fresh) == [:x => 0]
    # After x = 0, y = 1 IS strongly dominant:
    @test apply_dominance!(ws_fresh, :y).stop_reason === :applied
    @test deductions(ws_fresh) == [:x => 0, :y => 1]
    @test verify_certificate(ws_fresh, export_certificate(ws_fresh)).valid
    @test reconstruct(materialize(ws_fresh), Int[]).state == [0, 1]

    # 5. Opt-in propagate!(ws; allow_weak=true) sequentially fixes x=0 (weak) then y=1 (strong):
    rollback!(ws_fresh, cp_root)
    gmap = domain_map(ws_fresh; domain=:spin, gauge=[-1, 1])
    @test prove_dominance(ws_fresh, :x; value=1, map=gmap, allow_weak=true).stop_reason === :proved
    @test apply_dominance!(ws_fresh, :x; value=1, map=gmap, allow_weak=true).stop_reason === :applied
    @test verify_certificate(ws_fresh, export_certificate(ws_fresh)).valid
    rollback!(ws_fresh, cp_root)
    rep_weak = propagate!(ws_fresh; allow_weak=true)
    @test rep_weak.deductions == 2
    @test deductions(ws_fresh) == [:x => 0, :y => 1]
    cert_weak = export_certificate(ws_fresh)
    @test persistency(cert_weak) === :weak
    @test [persistency(s) for s in cert_weak.steps] == [:weak, :strong]
    @test verify_certificate(ws_fresh, cert_weak).valid
    t_cert_weak = transport_certificate(ws_fresh, cert_weak, gmap)
    @test verify_certificate(ws_fresh, t_cert_weak; map=gmap).valid

    # 6. Derivative-bound weak dominance (lower == 0) and weak relation (lower == 0):
    ws_tie = Workspace(fixture([:a, :b], [0.0, 1.0], [0.0 1.0; 0.0 0.0]); rules=:dominance)
    @test prove_dominance(ws_tie, :a).stop_reason === :not_strict
    att_weak_deriv = prove_dominance(ws_tie, :a; allow_weak=true)
    @test att_weak_deriv.stop_reason === :proved
    @test only(att_weak_deriv.certificate.steps).method === :exact
    @test persistency(only(att_weak_deriv.certificate.steps)) === :weak
    @test verify_certificate(ws_tie, att_weak_deriv.certificate).valid
    @test propagate!(ws_tie; allow_weak=true).deductions == 2

    ws_rel_tie = Workspace(fixture([:a, :b], [0.0, 0.0], [0.0 -1.0; 0.0 0.0]; domain=:spin))
    # Add a third neighbor :c with coupling 1.0 to :a so -J_ab - |J_ac| = 1 - 1 = 0
    ws_rel_tie = Workspace(fixture([:a, :b, :c], [0.0, 0.0, 0.0],
                                   [0.0 -1.0 1.0; 0.0 0.0 0.0; 0.0 0.0 0.0]; domain=:spin))
    @test prove_relation(ws_rel_tie, :a, :b; sign=1, allow_weak=false).stop_reason === :not_strict
    att_rel_weak = prove_relation(ws_rel_tie, :a, :b; sign=1, allow_weak=true)
    @test att_rel_weak.stop_reason === :proved
    @test persistency(only(att_rel_weak.certificate.steps)) === :weak
    @test verify_certificate(ws_rel_tie, att_rel_weak.certificate).valid
end

@testset "verifier rejects out-of-order, tampered and degree-exceeded steps" begin
    # Out-of-order step rejection on a 2-step chain where step 2 requires step 1
    ws = Workspace(fixture([:x, :y, :z], [4.0, 4.0, -1.0], [0.0 -8.0 2.0; 0.0 0.0 0.0; 0.0 0.0 0.0]))
    @test contract_relation!(ws, :x, :y).stop_reason === :applied
    @test eliminate_variable!(ws, :z).stop_reason === :applied
    @test apply_dominance!(ws, :y).stop_reason === :applied
    valid_cert = export_certificate(ws)
    @test verify_certificate(ws, valid_cert).valid

    s1, s2, s3 = valid_cert.steps
    # Swap s1 (RelationStep) and s3 (DominanceStep on :y, which wasn't dominant before s1 and s2!)
    s3_first = DominanceStep(s3.variable, s3.value, s3.lower, s3.upper, s1.constant, 0, s3.method, s3.scope_length, s3.persistency)
    s1_second = RelationStep(s1.eliminated, s1.representative, s1.sign, s1.orig_sign, s1.lower, s1.upper, s1.constant, 1, s1.method, s1.scope_length, s1.persistency)
    reordered = DominanceCertificate(generation(ws), checkpoint(ws), (), (s3_first, s1_second, s2), ws._snapshot)
    @test !verify_certificate(ws, reordered).valid

    # Tamper tests for RelationStep
    ws_r = Workspace(fixture([:u, :v, :w], [0.0, 0.0, 0.0], [0.0 -5.0 1.0; 0.0 0.0 0.0; 0.0 0.0 0.0]; domain=:spin))
    # Fast interval path when max_exact_work=0, and exact fallback when small gap
    att_r_int = prove_relation(ws_r, :u, :v; max_exact_work=0)
    @test att_r_int.stop_reason === :proved && att_r_int.method === :interval
    @test verify_certificate(ws_r, att_r_int.certificate).valid
    rs = only(att_r_int.certificate.steps)
    for (bad_rs, expected_reason) in (
        (RelationStep(1, 1, 1, 1, rs.lower, rs.upper, rs.constant, 0, :interval, 0, :strong), :invalid_step),
        (RelationStep(4, 2, 1, 1, rs.lower, rs.upper, rs.constant, 0, :interval, 0, :strong), :invalid_step),
        (RelationStep(1, 2, -1, 1, rs.lower, rs.upper, rs.constant, 0, :interval, 0, :strong), :invalid_value),
        (RelationStep(1, 2, 2, 2, rs.lower, rs.upper, rs.constant, 0, :interval, 0, :strong), :invalid_value),
        (RelationStep(1, 2, 1, 1, rs.lower, rs.upper, rs.constant, 0, :heuristic, 0, :strong), :invalid_method),
        (RelationStep(1, 2, 1, 1, rs.lower, rs.upper, rs.constant + 1, 0, :interval, 0, :strong), :invalid_constant),
        (RelationStep(1, 2, 1, 1, rs.upper + 1, rs.upper, rs.constant, 0, :interval, 0, :strong), :invalid_bound),
    )
        bad_c = DominanceCertificate(generation(ws_r), checkpoint(ws_r), (), (bad_rs,), ws_r._snapshot)
        vr = verify_certificate(ws_r, bad_c)
        @test !vr.valid && vr.stop_reason === expected_reason
    end

    # Tamper tests for EliminationStep
    ws_e = Workspace(fixture([:u, :v, :w], [1.0, 0.0, 0.0], [0.0 -2.0 0.0; 0.0 0.0 0.0; 0.0 0.0 0.0]))
    att_e = prove_elimination(ws_e, :u)
    @test att_e.stop_reason === :proved
    @test verify_certificate(ws_e, att_e.certificate).valid
    es = only(att_e.certificate.steps)
    for (bad_es, expected_reason) in (
        (EliminationStep(4, es.neighbors, es.table, es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_step),
        (EliminationStep(1, (1,), es.table, es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_step),
        (EliminationStep(1, (3, 2), (0, 0, 0, 0), es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_step),
        (EliminationStep(1, (), (0,), es.constant_delta, (), (), es.constant, 0, 0, true), :invalid_step), # missing active neighbor 2
        (EliminationStep(1, (2, 3, 4, 5), Tuple(zeros(Int, 16)), es.constant_delta, (), (), es.constant, 0, 0, true), :invalid_step), # degree > 3
        (EliminationStep(1, es.neighbors, (0,), es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_value),
        (EliminationStep(1, es.neighbors, (0, 2), es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_value),
        (EliminationStep(1, es.neighbors, es.table, es.constant_delta, (3 => big(1)//1,), es.quadratic_deltas, es.constant, 0, 0, true), :invalid_step),
        (EliminationStep(1, es.neighbors, es.table, es.constant_delta, es.linear_deltas, ((2, 3, big(1)//1),), es.constant, 0, 0, true), :invalid_step),
        (EliminationStep(1, es.neighbors, es.table, es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant + 1, 0, 0, true), :invalid_constant),
        (EliminationStep(1, es.neighbors, (1, 0), es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_bound),
        (EliminationStep(1, es.neighbors, es.table, es.constant_delta + 1, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, true), :invalid_bound),
        (EliminationStep(1, es.neighbors, es.table, es.constant_delta, es.linear_deltas, es.quadratic_deltas, es.constant, 0, 0, false), :invalid_bound),
    )
        bad_c = DominanceCertificate(generation(ws_e), checkpoint(ws_e), (), (bad_es,), ws_e._snapshot)
        ve = verify_certificate(ws_e, bad_c)
        @test !ve.valid && ve.stop_reason === expected_reason
    end

    # Degree > 3 refusal in prove_elimination and eliminate_variable!
    Q5 = zeros(5, 5)
    Q5[1, 2] = -1.0
    for j in 3:5; Q5[1, j] = 1.0; end
    ws_deg4 = Workspace(fixture([:u, :a, :b, :c, :d], zeros(5), Q5))
    @test degree(ws_deg4, :u) == 4
    @test prove_elimination(ws_deg4, :u).stop_reason === :degree_too_high
    @test eliminate_variable!(ws_deg4, :u).stop_reason === :degree_too_high
    # Oversized component (> 4) refusal in marginal weak dominance
    @test prove_dominance(ws_deg4, :u; allow_weak=true).stop_reason === :not_strict

    # Boundary refusals (already_fixed, zero_scale, work_limit, verification_limit, deadline, bad args)
    @test_throws ArgumentError prove_relation(ws_r, :u, :u)
    @test_throws ArgumentError prove_relation(ws_r, :u, :v; sign=2)
    @test_throws ArgumentError prove_elimination(ws_e, :u; tie_break=:middle)
    @test prove_relation(ws_r, :u, :v; max_work=0).stop_reason === :work_limit
    @test prove_relation(ws_r, :u, :v; deadline_ns=UInt64(0)).stop_reason === :deadline
    @test prove_elimination(ws_e, :u; max_work=0).stop_reason === :work_limit
    @test prove_elimination(ws_e, :u; max_exact_work=1).stop_reason === :verification_limit
    @test prove_elimination(ws_e, :u; deadline_ns=UInt64(0)).stop_reason === :deadline

    ws_zero = Workspace(fixture([:u, :v], [1.0, 1.0], [0.0 -1.0; 0.0 0.0]; scale=0.0))
    @test prove_relation(ws_zero, :u, :v).stop_reason === :zero_scale
    @test prove_elimination(ws_zero, :u).stop_reason === :zero_scale

    assume!(ws_e, :u, 0)
    @test prove_relation(ws_e, :u, :v).stop_reason === :already_fixed
    @test prove_elimination(ws_e, :u).stop_reason === :already_fixed

    # Assume! on a variable removed by RelationStep or EliminationStep safely rolls back the reduction suffix
    # and replays retained caller assumptions before applying the new assumption!
    ws_branch = Workspace(fixture([:u, :v, :w], [0.0, 0.0, 1.0], [0.0 -5.0 1.0; 0.0 0.0 -1.0; 0.0 0.0 0.0]; domain=:spin))
    bmap = domain_map(ws_branch; domain=:bool, gauge=[-1, 1, 1])
    @test contract_relation!(ws_branch, :u, :v).stop_reason === :applied # cancels edge (v, w)
    @test assume!(ws_branch, :w, -1).stop_reason === :applied
    @test ws_branch._state.fixed[1] == 3 # :u is relation-contracted
    @test assume!(ws_branch, :u, 1; max_work=0).stop_reason === :work_limit
    @test assume!(ws_branch, :u, 1; deadline_ns=UInt64(0)).stop_reason === :deadline
    rep_assume = assume!(ws_branch, :u, 0; map=bmap) # 0 in bool with gauge -1 lifts to +1 in spin
    @test rep_assume.stop_reason === :applied
    @test isempty(reductions(ws_branch))
    @test Dict(assumptions(ws_branch)) == Dict(:w => -1, :u => 1)

    # Regression test (Finding 1): Evolved exact rational coupling after contraction must be enclosed
    # in the interval dominance pass rather than rounded via Float64(q).
    # F(u, v, w) = (1 + 2^-52)*w - 4*u*v + u*w + 2^-54*v*w in spin minimization:
    # Contracting u into v produces coupling (1 + 2^-54) between v and w.
    # Exact lower bound for w is (1 + 2^-52) - (1 + 2^-54) = 3 * 2^-54 > 0, whereas rounding
    # (1 + 2^-54) to 1.0 before outward addition would emit an invalid interval lower bound prevfloat(2^-52) == 2^-53 > 3 * 2^-54.
    L_encl = [0.0, 0.0, 1.0 + ldexp(1.0, -52)]
    Q_encl = [0.0 -4.0 1.0; 0.0 0.0 ldexp(1.0, -54); 0.0 0.0 0.0]
    ws_encl = Workspace(fixture([:u, :v, :w], L_encl, Q_encl; domain=:spin); rules=:dominance)
    @test contract_relation!(ws_encl, :u, :v).stop_reason === :applied
    att_w = prove_dominance(ws_encl, :w)
    @test att_w.stop_reason === :proved
    @test att_w.method === :exact
    @test last(att_w.certificate.steps).lower == Rational{BigInt}(3) // (BigInt(1) << 54)
    @test verify_certificate(ws_encl, att_w.certificate).valid

    # Regression test (Finding 2 & 4): Degenerate multi-optimum universal lifting and swap-remove rollback
    # Model on 5 binary variables [:d, :u, :v, :e, :f] with multiple degenerate optima:
    # - :d has field +3 (strong dominance d = 0)
    # - :u and :v have strong equality 4*(u - v)^2 = 4*u + 4*v - 8*u*v, plus u*f - v*f (which cancels (v, f) when u = v!)
    #   and v also has edge to :e so cancelling (v, e) or (v, f) tests non-tail swap-remove in adjacency[v].
    # - :e has field -1 and coupling +2*e*v (strict local elimination table(0)=1, table(1)=0, contributing -1 + v to v,
    #   and if we also add -v to v's initial field so v's net field after eliminating :e is 0, then both v=0 and v=1,
    #   and both f=0 and f=1 are optimal: 4 degenerate global optima!).
    L_deg = [3.0, 4.0, 3.0, -1.0, 0.0]
    Q_deg = [
        0.0  0.0  0.0  0.0  0.0;
        0.0  0.0 -8.0  0.0  1.0;
        0.0  0.0  0.0  2.0 -1.0;
        0.0  0.0  0.0  0.0  0.0;
        0.0  0.0  0.0  0.0  0.0
    ]
    m_deg = fixture([:d, :u, :v, :e, :f], L_deg, Q_deg)
    opt_deg = oracle_optima(L_deg, Q_deg, 1.0, 0.0, :bool, :min, ())
    @test length(opt_deg) == 4 # (d=0, u=v in {0,1}, e=1-v, f in {0,1}) all have energy -1
    ws_deg = Workspace(m_deg; rules=:dominance)
    cp_deg0 = checkpoint(ws_deg)
    @test apply_dominance!(ws_deg, :d).stop_reason === :applied
    # Before contracting u -> v, adjacency[v] has [u => -8, e => 2, f => -1];
    # contracting u -> v swap-removes u (at pos 1, non-tail!) and cancels (v, f) to 0!
    @test contract_relation!(ws_deg, :u, :v).stop_reason === :applied
    @test eliminate_variable!(ws_deg, :e).stop_reason === :applied
    res_deg = materialize(ws_deg; coefficient_type=Rational{BigInt})
    assert_universal_lifting_and_persistency(
        res_deg, L_deg, Q_deg, 1.0, 0.0, :bool, :min, opt_deg, Rational{BigInt}(-1),
    )
    rollback!(ws_deg, cp_deg0)
    for a in 1:5
        for (pos, (b, _)) in enumerate(ws_deg._state.adjacency[a])
            @test ws_deg._state.adj_pos[a][b] == pos
        end
    end
end


