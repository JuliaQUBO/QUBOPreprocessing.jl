# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

@testset "degree-0/1/2 exact local minimum and Ising -|h_i + sum J_ij s_j| equivalence" begin
    R = Rational{BigInt}
    # Test isolated (d=0), leaf (d=1), and degree-two (d=2) cases with zero and nonzero fields
    # across :bool and :spin domains, :min and :max senses, positive and negative scales, and gauge maps.
    fixtures = (
        # (name, labels, h_spin, J_spin_triples)
        (:isolated_nonzero, [:u, :a], R[3//2, -1//2], Tuple{Int,Int,R}[]),
        (:isolated_zero, [:u, :a], R[0, 1], Tuple{Int,Int,R}[]),
        (:leaf_field_lt_J, [:u, :v, :a], R[1, -1//2, 2], [(1, 2, R(-3))]),
        (:leaf_field_gt_J, [:u, :v, :a], R[4, -1//2, 2], [(1, 2, R(-1))]),
        (:leaf_tie, [:u, :v, :a], R[2, 1//2, -1], [(1, 2, R(-2))]),
        (:deg2_zero_field, [:u, :v, :w], R[0, 1//2, -3//4], [(1, 2, R(-2)), (1, 3, R(3)), (2, 3, R(1//2))]),
        (:deg2_nonzero_field, [:u, :v, :w], R[5//4, -1//2, 3//4], [(1, 2, R(-2)), (1, 3, R(3//2)), (2, 3, R(-1//2))]),
        (:deg2_cancel_edge, [:u, :v, :w], R[0, 1, -1], [(1, 2, R(2)), (1, 3, R(2)), (2, 3, R(-2))]),
    )
    for (_, labels, h_s, J_list) in fixtures
        n = length(labels)
        J_mat = zeros(R, n, n)
        for (i, j, val) in J_list
            J_mat[i, j] = val
        end
        for domain in (:spin, :bool), sense in (:min, :max), scale in (1.0, -2.0), tie_break in (:low, :high)
            dir = (sense === :min ? 1 : -1) * (scale < 0 ? -1 : 1)
            L_f, Q_f, off_f = if domain === :spin
                Float64.(h_s), Float64.(J_mat), 0.25
            else
                Q_b = 4 .* J_mat
                L_b = [2 * h_s[i] - sum((2 * J_mat[min(i, j), max(i, j)] for j in 1:n if j != i); init=R(0)) for i in 1:n]
                c_b = R(1//4) - sum(h_s) + sum((J_mat[i, j] for i in 1:n for j in (i+1):n); init=R(0))
                Float64.(L_b), Float64.(Q_b), Float64(c_b)
            end
            model = fixture(labels, L_f, Q_f; domain, sense, scale, offset=off_f)
            optima = oracle_optima(L_f, Q_f, scale, off_f, domain, sense, ())
            opt_energy = reference(L_f, Q_f, scale, off_f, first(optima), R)

            for use_map in (false, true)
                ws = Workspace(model; rules=:dominance)
                gmap = use_map ? domain_map(ws; domain=(domain === :spin ? :bool : :spin),
                                            gauge=[isodd(k) ? -1 : 1 for k in 1:n]) : nothing
                att = prove_elimination(ws, :u; map=gmap, tie_break)
                @test att.stop_reason === :proved
                @test verify_certificate(ws, att.certificate; map=gmap).valid
                rep = eliminate_variable!(ws, :u; map=gmap, tie_break)
                @test rep.stop_reason === :applied
                @test isempty(deductions(ws))
                @test length(reductions(ws)) == 1

                res = gmap === nothing ? materialize(ws; coefficient_type=R) :
                                         materialize(ws, gmap; coefficient_type=R)
                res_dom = gmap === nothing ? domain : gmap.target_domain
                m = length(res._free)
                L_res = R[res._linear...]
                Q_res = zeros(R, m, m)
                for (i, j, q) in res._quadratic
                    Q_res[i, j] = R(q)
                end
                low_orig = domain === :bool ? 0 : -1

                # Check every boundary assignment against exact local minimum and Ising -|h_u + sum J_uj s_j|
                for y in states(m, res_dom)
                    rec = reconstruct(res, y)
                    e_res = reference(L_res, Q_res, R(res._scale), R(res._constant), y, R)
                    e_lifted = reference(L_f, Q_f, scale, off_f, rec.state, R)
                    @test e_res == e_lifted

                    state_low = copy(rec.state); state_low[1] = low_orig
                    state_high = copy(rec.state); state_high[1] = 1
                    e_low = reference(L_f, Q_f, scale, off_f, state_low, R)
                    e_high = reference(L_f, Q_f, scale, off_f, state_high, R)
                    e_local_opt = sense === :min ? min(e_low, e_high) : max(e_low, e_high)
                    @test e_res == e_local_opt

                    # Verify Ising -|h_1 + sum_j J_{1j} s_j| formula in normalized spin energy:
                    s_vec = [domain === :bool ? (2 * rec.state[k] - 1) : rec.state[k] for k in 1:n]
                    eff_h1 = h_s[1] + sum((J_mat[1, j] * s_vec[j] for j in 2:n); init=R(0))
                    ising_local_min = -abs(dir * eff_h1)
                    actual_spin_contrib = dir * eff_h1 * s_vec[1]
                    @test actual_spin_contrib == ising_local_min
                end

                assert_universal_lifting_and_persistency(
                    res, L_f, Q_f, scale, off_f, domain, sense, optima, opt_energy,
                )
            end
        end
    end
end

@testset "chains, cycles, disconnected models and alternating dominance/elimination cascades" begin
    R = Rational{BigInt}
    # 1. 5-vertex chain with nonzero fields reduced completely to 0 variables via eliminate_low_degree!
    L_chain = [0.5, -1.25, 0.75, -0.5, 1.0]
    Q_chain = zeros(5, 5)
    Q_chain[1, 2] = -2.0; Q_chain[2, 3] = 1.5; Q_chain[3, 4] = -1.0; Q_chain[4, 5] = 2.5
    for domain in (:bool, :spin), sense in (:min, :max)
        m_chain = fixture([:c1, :c2, :c3, :c4, :c5], L_chain, Q_chain; domain, sense, offset=0.5)
        opt_chain = oracle_optima(L_chain, Q_chain, 1.0, 0.5, domain, sense, ())
        opt_e_chain = reference(L_chain, Q_chain, 1.0, 0.5, first(opt_chain), R)
        ws_chain, rep_chain = preprocess(m_chain; rules=:elimination)
        @test rep_chain.stop_reason === :quiescent
        @test rep_chain.deductions == 5
        @test rep_chain.pending == 0
        @test isempty(deductions(ws_chain))
        @test length(reductions(ws_chain)) == 5
        @test verify_certificate(ws_chain, export_certificate(ws_chain)).valid
        res_chain = materialize(ws_chain; coefficient_type=R)
        @test QT.dimension(export_model(res_chain)) == 0
        assert_universal_lifting_and_persistency(
            res_chain, L_chain, Q_chain, 1.0, 0.5, domain, sense, opt_chain, opt_e_chain,
        )
    end

    # 2. 5-vertex cycle with nonzero fields reduced completely to 0 variables via eliminate_low_degree!
    # Eliminating degree-2 vertices around the cycle creates fill edges, merges parallel edges on the final
    # 2-cycle, and reduces the cycle to 0 variables.
    L_cycle = [0.25, -0.75, 1.25, -0.5, 0.5]
    Q_cycle = zeros(5, 5)
    Q_cycle[1, 2] = -1.5; Q_cycle[2, 3] = 2.0; Q_cycle[3, 4] = -1.0; Q_cycle[4, 5] = 1.5; Q_cycle[1, 5] = -2.0
    for domain in (:bool, :spin), sense in (:min, :max)
        m_cycle = fixture([:v1, :v2, :v3, :v4, :v5], L_cycle, Q_cycle; domain, sense)
        opt_cycle = oracle_optima(L_cycle, Q_cycle, 1.0, 0.0, domain, sense, ())
        opt_e_cycle = reference(L_cycle, Q_cycle, 1.0, 0.0, first(opt_cycle), R)
        ws_cycle = Workspace(m_cycle; rules=:elimination)
        g_cycle = domain_map(ws_cycle; domain=(domain === :bool ? :spin : :bool), gauge=[-1, 1, -1, 1, -1])
        rep_cycle = eliminate_low_degree!(ws_cycle; map=g_cycle)
        @test rep_cycle.stop_reason === :quiescent
        @test rep_cycle.deductions == 5
        @test verify_certificate(ws_cycle, export_certificate(ws_cycle)).valid
        @test verify_certificate(ws_cycle, export_certificate(ws_cycle; map=g_cycle); map=g_cycle).valid
        res_cycle = materialize(ws_cycle; coefficient_type=R)
        @test QT.dimension(export_model(res_cycle)) == 0
        assert_universal_lifting_and_persistency(
            res_cycle, L_cycle, Q_cycle, 1.0, 0.0, domain, sense, opt_cycle, opt_e_cycle,
        )
    end

    # 3. Disconnected model: isolate (v1) + 2-vertex leaf edge (v2-v3) + 4-clique K_4 (v4, v5, v6, v7)
    # Degree-<=2 elimination removes v1, v2, v3 while skipping the degree-3 K_4 vertices.
    L_disc = [1.5, -0.5, 0.75, 0.25, -0.5, 0.5, -0.25]
    Q_disc = zeros(7, 7)
    Q_disc[2, 3] = -1.5
    for a in 4:7, b in (a+1):7
        Q_disc[a, b] = (a + b) % 2 == 0 ? 1.0 : -1.0
    end
    m_disc = fixture([:v1, :v2, :v3, :v4, :v5, :v6, :v7], L_disc, Q_disc)
    opt_disc = oracle_optima(L_disc, Q_disc, 1.0, 0.0, :bool, :min, ())
    opt_e_disc = reference(L_disc, Q_disc, 1.0, 0.0, first(opt_disc), R)
    ws_disc = Workspace(m_disc; rules=:elimination)
    rep_disc = eliminate_low_degree!(ws_disc)
    @test rep_disc.stop_reason === :quiescent
    @test rep_disc.deductions == 3
    res_disc = materialize(ws_disc; coefficient_type=R)
    @test QT.variables(export_model(res_disc)) == [:v4, :v5, :v6, :v7]
    assert_universal_lifting_and_persistency(
        res_disc, L_disc, Q_disc, 1.0, 0.0, :bool, :min, opt_disc, opt_e_disc,
    )

    # 4. Alternating dominance/elimination cascade:
    # 5 variables [:leaf, :hub, :t1, :t2, :t3] in spin minimization:
    # - :leaf has degree 1 (coupled only to :hub with J = -4, field h_leaf = 2).
    #   Since |h_leaf| = 2 < |J| = 4, :leaf is NOT strictly dominant!
    #   Eliminating :leaf contributes local minimum -|2 - 4*s_hub|:
    #   at s_hub = -1 -> -|6| = -6; at s_hub = +1 -> -|-2| = -2 -> delta_c = -4, delta_h_hub = +2!
    # - :hub has initial degree 4 (coupled to :leaf and to triangle :t1, :t2, :t3 with J = 1 each, initial field h_hub = 2).
    #   Initially :hub has degree 4 (skipped by degree-<=2 elimination) and derivative bounds 2 - (4+1+1+1) = -5 to +9 (not dominant!).
    #   After :leaf is eliminated, :hub has degree 3 (still > 2!) and new field 2 + 2 = 4 > 1 + 1 + 1 = 3,
    #   so :hub becomes STRICTLY DOMINANT (s_hub = -1)!
    # - Once dominance fixes :hub = -1, the triangle vertices :t1, :t2, :t3 drop from degree 3 to degree 2,
    #   allowing degree-<=2 elimination to eliminate :t1, :t2, :t3 and reduce the entire model to 0 variables!
    L_casc = [2.0, 2.0, 0.5, -0.25, 0.75]
    Q_casc = [
        0.0 -4.0  0.0  0.0  0.0;
        0.0  0.0  1.0  1.0  1.0;
        0.0  0.0  0.0 -1.5  1.0;
        0.0  0.0  0.0  0.0 -2.0;
        0.0  0.0  0.0  0.0  0.0
    ]
    m_casc = fixture([:leaf, :hub, :t1, :t2, :t3], L_casc, Q_casc; domain=:spin)
    opt_casc = oracle_optima(L_casc, Q_casc, 1.0, 0.0, :spin, :min, ())
    opt_e_casc = reference(L_casc, Q_casc, 1.0, 0.0, first(opt_casc), R)

    # Dominance alone fixes 0 variables:
    ws_dom_only = Workspace(m_casc; rules=:dominance)
    @test propagate!(ws_dom_only).deductions == 0

    # Degree-<=2 elimination alone eliminates only :leaf (1 variable):
    ws_elim_only = Workspace(m_casc; rules=:elimination)
    @test eliminate_low_degree!(ws_elim_only; cascade_dominance=false).deductions == 1
    @test degree(ws_elim_only, :hub) == 3

    # Interleaved cascade (cascade_dominance=true) reduces all 5 variables to 0!
    ws_casc = Workspace(m_casc; rules=:dominance)
    rep_casc = eliminate_low_degree!(ws_casc; cascade_dominance=true)
    @test rep_casc.stop_reason === :quiescent
    @test rep_casc.deductions == 5
    @test deductions(ws_casc) == [:hub => -1, :t2 => 1, :t1 => 1]
    @test length(reductions(ws_casc)) == 5
    cert_casc = export_certificate(ws_casc)
    @test [typeof(s) for s in cert_casc.steps] ==
          [EliminationStep, DominanceStep, EliminationStep, DominanceStep, DominanceStep]
    @test verify_certificate(ws_casc, cert_casc).valid
    res_casc = materialize(ws_casc; coefficient_type=R)
    @test QT.dimension(export_model(res_casc)) == 0
    assert_universal_lifting_and_persistency(
        res_casc, L_casc, Q_casc, 1.0, 0.0, :spin, :min, opt_casc, opt_e_casc,
    )
end

@testset "tie-breaking semantics, weak persistency tag, and non-fixing reporting" begin
    R = Rational{BigInt}
    # F(u, v) = u*v + v on binary variables {0, 1}:
    # Unique optimal v is v = 0 (energy 0). When v = 0, u has 0 marginal cost (u=0 and u=1 both give energy 0!).
    # Global optima are [0, 0] and [1, 0].
    L_tie = [0.0, 1.0]
    Q_tie = [0.0 1.0; 0.0 0.0]
    m_tie = fixture([:u, :v], L_tie, Q_tie)
    opt_tie = oracle_optima(L_tie, Q_tie, 1.0, 0.0, :bool, :min, ())
    @test Set(opt_tie) == Set([[0, 0], [1, 0]])

    ws_low = Workspace(m_tie; rules=:elimination)
    @test eliminate_variable!(ws_low, :u; tie_break=:low).stop_reason === :applied
    step_low = only(reductions(ws_low))
    @test !step_low.unique_argmin
    @test persistency(step_low) === :weak
    @test certificate_guarantee(export_certificate(ws_low)) === :exact_elimination
    @test persistency(export_certificate(ws_low)) === :weak
    @test isempty(deductions(ws_low)) # never reported as strongly fixed!
    res_low = materialize(ws_low; coefficient_type=R)
    assert_universal_lifting_and_persistency(
        res_low, L_tie, Q_tie, 1.0, 0.0, :bool, :min, opt_tie, R(0),
    )
    @test reconstruct(res_low, [0]).state == [0, 0]

    ws_high = Workspace(m_tie; rules=:elimination)
    @test eliminate_variable!(ws_high, :u; tie_break=:high).stop_reason === :applied
    step_high = only(reductions(ws_high))
    @test !step_high.unique_argmin
    @test persistency(step_high) === :weak
    @test isempty(deductions(ws_high))
    res_high = materialize(ws_high; coefficient_type=R)
    assert_universal_lifting_and_persistency(
        res_high, L_tie, Q_tie, 1.0, 0.0, :bool, :min, opt_tie, R(0),
    )
    @test reconstruct(res_high, [0]).state == [1, 0]
end

@testset "resumable budget stops, rollback restoration, and local-work isolation" begin
    # 1. Budget stops (max_work, max_deductions, max_exact_work, deadline_ns) on a 4-vertex chain
    L4 = [0.5, -1.0, 0.75, -0.5]
    Q4 = [0.0 -2.0 0.0 0.0; 0.0 0.0 1.5 0.0; 0.0 0.0 0.0 -1.0; 0.0 0.0 0.0 0.0]
    m4 = fixture([:x1, :x2, :x3, :x4], L4, Q4)

    for limit in (:work, :deductions, :exact)
        ws = Workspace(m4; rules=:elimination)
        cp0 = checkpoint(ws)
        r0 = limit === :work ? eliminate_low_degree!(ws; max_work=0) :
             limit === :deductions ? eliminate_low_degree!(ws; max_deductions=0) :
             eliminate_low_degree!(ws; max_exact_work=0)
        @test r0.stop_reason in (:work_limit, :deduction_limit, :verification_limit)
        @test r0.deductions == 0
        @test isempty(reductions(ws))

        # Allow 1 elimination, then checkpoint, then resume to completion
        r1 = limit === :work ? eliminate_low_degree!(ws; max_work=4) :
             limit === :deductions ? eliminate_low_degree!(ws; max_deductions=1) :
             eliminate_low_degree!(ws; max_exact_work=7)
        @test r1.stop_reason in (:work_limit, :deduction_limit, :verification_limit)
        @test r1.deductions == 1
        @test r1.pending > 0
        cp1 = checkpoint(ws)

        r2 = eliminate_low_degree!(ws)
        @test r2.stop_reason === :quiescent
        @test r2.deductions == 3
        @test r2.pending == 0
        @test length(reductions(ws)) == 4
        @test verify_certificate(ws, export_certificate(ws)).valid

        # Rollback to cp1 and re-run remaining 3 eliminations
        rollback!(ws, cp1)
        @test length(reductions(ws)) == 1
        r2_replay = eliminate_low_degree!(ws)
        @test r2_replay.stop_reason === :quiescent
        @test r2_replay.deductions == 3

        # Rollback to root cp0 and verify complete restoration
        rollback!(ws, cp0)
        @test isempty(reductions(ws))
        @test ws._state.elim_heads == [1, 1, 1, 1]
        @test sum(length, ws._state.elim_queues) == 4
        @test all(i -> any(b -> ws._state.elim_queued[b][i], 1:4), 1:4)
    end

    ws_dl = Workspace(m4; rules=:elimination)
    @test eliminate_low_degree!(ws_dl; deadline_ns=UInt64(0)).stop_reason === :deadline
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; max_degree=4)
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; max_degree=-1)
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; max_fill=-1)
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; max_fill=true)
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; tie_break=:none)
    @test_throws ArgumentError eliminate_low_degree!(Workspace(m4; rules=:identity); cascade_dominance=true)

    # Rollback of a reduction that newly queues a degree-4 -> degree-3 neighbor:
    Q_k4_leaf = zeros(5, 5)
    Q_k4_leaf[1, 2] = -1.5
    for i in 2:5, j in (i+1):5
        Q_k4_leaf[i, j] = 1.0
    end
    ws_k4_leaf = Workspace(fixture([:x1, :x2, :x3, :x4, :x5], zeros(5), Q_k4_leaf); rules=:elimination)
    @test !any(b -> ws_k4_leaf._state.elim_queued[b][2], 1:4) # initially degree 4
    cp_k4 = checkpoint(ws_k4_leaf)
    @test eliminate_variable!(ws_k4_leaf, :x1).stop_reason === :applied
    @test ws_k4_leaf._state.elim_queued[4][2] # lowered to degree 3 and queued in bucket 4
    rollback!(ws_k4_leaf, cp_k4)
    @test !any(b -> ws_k4_leaf._state.elim_queued[b][2], 1:4)

    # Direct cancellation-to-queue regression: eliminating degree-2 :x1 cancels
    # existing edge (:x2, :x3), dropping :x2 and :x3 from degree 4 to degree 2,
    # removing the edge from adjacency/adj_pos, and queuing both in elim_queues[3].
    # For x1 in {0, 1}, -2*x1*x2 + 2*x1*x3 with L[1] = 1 gives min_{x1}(x1*(1 - 2*x2 + 2*x3)):
    # (x2,x3)=(0,0)->0, (1,0)->-1, (0,1)->0, (1,1)->0 => delta_Q_{23} = 0 - (-1) - 0 + 0 = +1,
    # cancelling Q[2, 3] = -1.0!
    L_canc = [1.0, 0.25, -0.5, 0.0, 0.0, 0.0]
    Q_canc = zeros(6, 6)
    Q_canc[1, 2] = -2.0
    Q_canc[1, 3] = 2.0
    Q_canc[2, 3] = -1.0
    # Give x2 and x3 two additional neighbors each (from x4, x5, x6) so deg(x2) = deg(x3) = 4
    Q_canc[2, 4] = 1.0; Q_canc[2, 5] = -1.0
    Q_canc[3, 5] = 1.0; Q_canc[3, 6] = -1.0
    Q_canc[4, 5] = 1.0; Q_canc[4, 6] = 1.0; Q_canc[5, 6] = 1.0
    ws_canc = Workspace(fixture([:x1, :x2, :x3, :x4, :x5, :x6], L_canc, Q_canc); rules=:elimination)
    @test degree(ws_canc, :x2) == 4
    @test degree(ws_canc, :x3) == 4
    @test !any(b -> ws_canc._state.elim_queued[b][2], 1:4)
    @test !any(b -> ws_canc._state.elim_queued[b][3], 1:4)
    @test haskey(ws_canc._state.adj_pos[2], 3)
    cp_canc = checkpoint(ws_canc)
    @test eliminate_variable!(ws_canc, :x1).stop_reason === :applied
    @test degree(ws_canc, :x2) == 2
    @test degree(ws_canc, :x3) == 2
    @test !haskey(ws_canc._state.adj_pos[2], 3)
    @test !haskey(ws_canc._state.adj_pos[3], 2)
    @test all(first(p) != 3 for p in ws_canc._state.adjacency[2])
    @test ws_canc._state.elim_queued[3][2]
    @test ws_canc._state.elim_queued[3][3]
    rollback!(ws_canc, cp_canc)
    @test degree(ws_canc, :x2) == 4
    @test degree(ws_canc, :x3) == 4
    @test haskey(ws_canc._state.adj_pos[2], 3)
    @test haskey(ws_canc._state.adj_pos[3], 2)
    @test !any(b -> ws_canc._state.elim_queued[b][2], 1:4)
    @test !any(b -> ws_canc._state.elim_queued[b][3], 1:4)

    # Progressive max_degree cutoff increases (0 -> 1 -> 2 and 1 -> 2) with checkpoints/rollback
    # and strict zero-work / expired-deadline guards:
    m_tri = QT.Model{Int,Float64,Int}(
        Dict(i => 0.25 * i for i in 1:3),
        Dict((1, 2) => 1.0, (1, 3) => -1.5, (2, 3) => 2.0);
        domain=:spin, sense=:min,
    )
    ws_tri = Workspace(m_tri; rules=:elimination)
    cp_tri0 = checkpoint(ws_tri)
    r_cut0 = eliminate_low_degree!(ws_tri; max_degree=0)
    @test r_cut0.stop_reason === :quiescent
    @test r_cut0.deductions == 0
    @test r_cut0.candidates == 0
    @test r_cut0.pending == 0
    @test isempty(ws_tri._state.trail)
    # Repeated call at same cutoff does not scan or mutate trail
    @test eliminate_low_degree!(ws_tri; max_degree=0).candidates == 0
    @test isempty(ws_tri._state.trail)
    cp_tri1 = checkpoint(ws_tri)
    r_cut1 = eliminate_low_degree!(ws_tri; max_degree=1)
    @test r_cut1.stop_reason === :quiescent
    @test r_cut1.deductions == 0
    @test r_cut1.candidates == 0
    @test isempty(ws_tri._state.trail)
    cp_tri2 = checkpoint(ws_tri)
    r_cut2 = eliminate_low_degree!(ws_tri; max_degree=2)
    @test r_cut2.stop_reason === :quiescent
    @test r_cut2.deductions == 3
    @test verify_certificate(ws_tri, export_certificate(ws_tri)).valid
    # Rollback to cp_tri2 (after max_degree=1) and re-run max_degree=2
    rollback!(ws_tri, cp_tri2)
    @test isempty(reductions(ws_tri))
    @test eliminate_low_degree!(ws_tri; max_degree=2).deductions == 3
    # Rollback to cp_tri1 (after max_degree=0) and jump directly 0 -> 2
    rollback!(ws_tri, cp_tri1)
    @test isempty(reductions(ws_tri))
    @test eliminate_low_degree!(ws_tri; max_degree=2).deductions == 3
    # Rollback to root cp_tri0
    rollback!(ws_tri, cp_tri0)
    @test ws_tri._state.elim_heads == [1, 1, 1, 1]

    # 24-vertex spin cycle: max_degree=0 followed by max_degree=2 with max_work=0 or
    # expired deadline performs 0 queue/trail mutations and 0 candidate scans:
    m_c24 = QT.Model{Int,Float64,Int}(
        Dict(i => (isodd(i) ? 0.25 : -0.5) for i in 1:24),
        Dict((min(i, i == 24 ? 1 : i + 1), max(i, i == 24 ? 1 : i + 1)) => 1.0 for i in 1:24);
        domain=:spin, sense=:min,
    )
    ws_c24 = Workspace(m_c24; rules=:elimination)
    @test eliminate_low_degree!(ws_c24; max_degree=0).stop_reason === :quiescent
    @test isempty(ws_c24._state.trail)
    @test length(ws_c24._state.elim_queues[3]) == 24
    r_c24_w0 = eliminate_low_degree!(ws_c24; max_degree=2, max_work=0)
    @test r_c24_w0.stop_reason === :work_limit
    @test r_c24_w0.candidates == 0
    @test r_c24_w0.pending == 24
    @test isempty(ws_c24._state.trail)
    @test length(ws_c24._state.elim_queues[3]) == 24
    r_c24_dl = eliminate_low_degree!(ws_c24; max_degree=2, deadline_ns=UInt64(0))
    @test r_c24_dl.stop_reason === :deadline
    @test r_c24_dl.candidates == 0
    @test r_c24_dl.pending == 24
    @test isempty(ws_c24._state.trail)
    @test length(ws_c24._state.elim_queues[3]) == 24
    # Budgeted partial step, checkpoint, rollback, and full resumption:
    cp_c24 = checkpoint(ws_c24)
    r_c24_step = eliminate_low_degree!(ws_c24; max_degree=2, max_deductions=2)
    @test r_c24_step.stop_reason === :deduction_limit
    @test r_c24_step.deductions == 2
    rollback!(ws_c24, cp_c24)
    @test isempty(ws_c24._state.trail)
    @test eliminate_low_degree!(ws_c24; max_degree=2).deductions == 24

    # Paw graph (leaf 1 attached to triangle 2-3-4) stepping 0 -> 1 -> 2:
    m_paw = QT.Model{Int,Float64,Int}(
        Dict(i => 0.25 * i for i in 1:4),
        Dict((1, 2) => -1.0, (2, 3) => 1.5, (2, 4) => -1.25, (3, 4) => 2.0);
        domain=:spin, sense=:min,
    )
    ws_paw = Workspace(m_paw; rules=:elimination)
    @test eliminate_low_degree!(ws_paw; max_degree=0).deductions == 0
    @test eliminate_low_degree!(ws_paw; max_degree=1).deductions == 1
    @test eliminate_low_degree!(ws_paw; max_degree=2).deductions == 3
    @test verify_certificate(ws_paw, export_certificate(ws_paw)).valid

    # 2. Local work does not scan untouched high-degree graph:
    # Build a 3-vertex chain (degrees 1, 2, 1) plus a disjoint 4-regular circulant graph of size K (all degrees == 4 > 3).
    function chain_plus_4regular(k_reg::Int)
        n_tot = 3 + k_reg
        L_tot = zeros(n_tot)
        L_tot[1:3] = [0.5, -0.75, 1.25]
        I_idx = Int[1, 2]
        J_idx = Int[2, 3]
        V_val = Float64[-1.5, 2.0]
        for idx in 0:(k_reg - 1)
            u = 4 + idx
            for step in (1, 2)
                v = 4 + ((idx + step) % k_reg)
                push!(I_idx, min(u, v))
                push!(J_idx, max(u, v))
                push!(V_val, 1.0)
            end
        end
        Q_sp = sparse(I_idx, J_idx, V_val, n_tot, n_tot)
        return QT.Model{Int,Float64,Int}(
            Dict(i => L_tot[i] for i in 1:n_tot),
            Dict((i, j) => Q_sp[i, j] for (i, j, _) in zip(findnz(Q_sp)...));
            domain=:bool, sense=:min,
        )
    end
    ws_small = Workspace(chain_plus_4regular(8); rules=:elimination)
    ws_large = Workspace(chain_plus_4regular(1000); rules=:elimination)
    cp_s = checkpoint(ws_small)
    cp_l = checkpoint(ws_large)

    function elim_cycle!(ws, cp)
        rep = eliminate_low_degree!(ws)
        rollback!(ws, cp)
        return rep
    end
    for _ in 1:3
        elim_cycle!(ws_small, cp_s)
        elim_cycle!(ws_large, cp_l)
    end
    rep_s = elim_cycle!(ws_small, cp_s)
    rep_l = elim_cycle!(ws_large, cp_l)
    # Neither workspace ever queues or visits any vertex of the 4-regular component!
    @test rep_s.candidates == rep_l.candidates == 5
    @test rep_s.edge_visits == rep_l.edge_visits
    @test rep_s.deductions == rep_l.deductions == 3
    @test rep_s.exact_work == rep_l.exact_work
    bytes_s = @allocated elim_cycle!(ws_small, cp_s)
    bytes_l = @allocated elim_cycle!(ws_large, cp_l)
    @test bytes_l <= bytes_s + 2048
end

@testset "guarded zero-field degree-3 Ising star-triangle reduction" begin
    R = Rational{BigInt}

    # 1. Exact 8-state boundary table & Boettcher-Davidheiser (2008) Rule V Eq. (4) identity
    #    across bounded rational couplings, ties, existing triangle edges, cancellations,
    #    both domains (:spin, :bool), senses (:min, :max), scales, tie_breaks and gauges:
    star_cases = [
        # (name, [J1, J2, J3], [h_w1, h_w2, h_w3], [J12_old, J13_old, J23_old])
        (:generic_strict, R[3//2, -1//1, 5//4], R[1//2, -3//4, 1//4], R[0//1, 0//1, 0//1]),
        (:symmetric_ferro, R[-1//1, -1//1, -1//1], R[1//4, -1//2, 3//4], R[1//2, -1//4, 0//1]),
        (:tie_deg3, R[1//1, 1//1, 2//1], R[-1//2, 1//2, 0//1], R[0//1, 0//1, 0//1]),
        (:dominant_branch_zero_pair, R[1//1, 1//1, 3//1], R[1//4, 1//4, -1//2], R[0//1, 0//1, 0//1]),
        # Exact edge cancellation: for J1=J2=J3=-1 (min, scale>0), ΔJ_ab = -(3 - 1 - 1 + 1)/4 = -1/2,
        # so setting J12_old = +1/2 cancels edge (w1, w2) completely!
        (:exact_edge_cancellation, R[-1//1, -1//1, -1//1], R[1//2, -1//4, 0//1], R[1//2, 0//1, 0//1]),
        # Deterministic pseudo-random bounded dyadic rational draws (including zeros and ties):
        (:seeded_draw_1, R[-3//4, 5//4, -1//2], R[0//1, -3//4, 5//4], R[-1//4, 0//1, 3//4]),
        (:seeded_draw_2, R[3//2, -3//4, -3//4], R[-1//4, 0//1, 1//2], R[0//1, -1//2, 1//4]),
    ]
    for (cname, J_u, h_w, J_tri) in star_cases,
        domain in (:spin, :bool),
        sense in (:min, :max),
        scale in (1.25, -0.75),
        tie_break in (:low, :high)

        offset_val = 0.5
        dir = (sense === :min ? 1 : -1) * (scale > 0 ? 1 : -1)
        # Build 4-variable model on [:u, :w1, :w2, :w3] where :u has zero Ising field h_u == 0:
        h_spin = R[0//1, h_w[1], h_w[2], h_w[3]]
        J_spin = zeros(R, 4, 4)
        J_spin[1, 2] = J_u[1]; J_spin[1, 3] = J_u[2]; J_spin[1, 4] = J_u[3]
        J_spin[2, 3] = J_tri[1]; J_spin[2, 4] = J_tri[2]; J_spin[3, 4] = J_tri[3]
        if domain === :spin
            L_f = Float64.(h_spin)
            Q_f = Float64.(J_spin)
            c_f = offset_val
        else
            # Transform s_i = 2*x_i - 1 so Ising fields/couplings match (h_spin, J_spin) exactly:
            L_r = zeros(R, 4)
            Q_r = zeros(R, 4, 4)
            c_r = R(offset_val)
            for i in 1:4
                L_r[i] += 2 * h_spin[i]
                c_r -= h_spin[i]
            end
            for i in 1:4, j in (i+1):4
                Q_r[i, j] = 4 * J_spin[i, j]
                L_r[i] -= 2 * J_spin[i, j]
                L_r[j] -= 2 * J_spin[i, j]
                c_r += J_spin[i, j]
            end
            L_f = Float64.(L_r)
            Q_f = Float64.(Q_r)
            c_f = Float64(c_r)
        end
        m4 = fixture([:u, :w1, :w2, :w3], L_f, Q_f; scale, offset=c_f, domain, sense)
        ws = Workspace(m4; rules=:elimination)
        @test iszero(QUBOPreprocessing._spin_field(ws, 1))

        # Boettcher-Davidheiser (2008) Rule V Eq. (4) expected Ising deltas:
        eps0 = abs(J_u[1] + J_u[2] + J_u[3])
        eps1 = abs(-J_u[1] + J_u[2] + J_u[3])
        eps2 = abs(J_u[1] - J_u[2] + J_u[3])
        eps3 = abs(J_u[1] + J_u[2] - J_u[3])
        bd_const = -dir * (eps0 + eps1 + eps2 + eps3) // 4
        bd_j12 = -dir * (eps0 - eps1 - eps2 + eps3) // 4
        bd_j13 = -dir * (eps0 - eps1 + eps2 - eps3) // 4
        bd_j23 = -dir * (eps0 + eps1 - eps2 - eps3) // 4

        att = prove_elimination(ws, :u; max_degree=3, tie_break)
        @test att.stop_reason === :proved
        step = only(att.certificate.steps)
        @test step isa EliminationStep
        @test step.neighbors == (2, 3, 4)
        has_tie = (eps0 == 0 || eps1 == 0 || eps2 == 0 || eps3 == 0)
        @test step.unique_argmin == !has_tie
        @test persistency(step) === (has_tie ? :weak : :strong)
        if domain === :spin
            @test isempty(step.linear_deltas)
            @test step.constant_delta == bd_const
            q_dict = Dict((a, b) => dq for (a, b, dq) in step.quadratic_deltas)
            @test get(q_dict, (2, 3), R(0)) == bd_j12
            @test get(q_dict, (2, 4), R(0)) == bd_j13
            @test get(q_dict, (3, 4), R(0)) == bd_j23
        end
        @test verify_certificate(ws, att.certificate).valid
        gmap = domain_map(ws; domain=(domain === :spin ? :bool : :spin), gauge=[-1, 1, -1, 1])
        @test verify_certificate(ws, transport_certificate(ws, att.certificate, gmap); map=gmap).valid

        # Apply via eliminate_variable!(ws, :u; max_degree=3, tie_break) and check all 8 boundary states:
        rep = eliminate_variable!(ws, :u; max_degree=3, tie_break)
        @test rep.stop_reason === :applied && rep.changed == 1
        if cname === :exact_edge_cancellation && dir == 1
            # Edge (w1, w2) was cancelled to 0, so w1 and w2 have degree 1 instead of 2!
            @test degree(ws, :w1) == 1 && degree(ws, :w2) == 1 && degree(ws, :w3) == 2
        end
        res = materialize(ws; coefficient_type=R)
        rmod = export_model(res)
        @test QT.dimension(rmod) == 3
        L_res = R[res._linear...]
        Q_res = zeros(R, 3, 3)
        for (i, j, q) in res._quadratic
            Q_res[i, j] = R(q)
        end
        vals = domain === :bool ? (0, 1) : (-1, 1)
        for v1 in vals, v2 in vals, v3 in vals
            b_state = [v1, v2, v3]
            e_red = reference(L_res, Q_res, R(res._scale), R(res._constant), b_state, R)
            e_0 = reference(L_f, Q_f, scale, c_f, [vals[1], v1, v2, v3], R)
            e_1 = reference(L_f, Q_f, scale, c_f, [vals[2], v1, v2, v3], R)
            e_best = sense === :min ? min(e_0, e_1) : max(e_0, e_1)
            @test e_red == e_best
            rec = reconstruct(res, b_state)
            @test rec.state[2:4] == b_state
            @test reference(L_f, Q_f, scale, c_f, rec.state, R) == e_best
        end
    end

    # 2. Nonzero-field degree-3 rejection, small floating fields, and tampered certificates:
    Q_star = [0.0 1.0 1.0 1.0; 0.0 0.0 1.0 1.0; 0.0 0.0 0.0 1.0; 0.0 0.0 0.0 0.0]
    for h_nz in (0.5, -0.25, 1e-16, -1e-15, nextfloat(0.0), -nextfloat(0.0))
        ws_nz = Workspace(fixture([:u, :w1, :w2, :w3], [h_nz, 0.25, -0.5, 0.75], Q_star; domain=:spin); rules=:elimination)
        @test !iszero(QUBOPreprocessing._spin_field(ws_nz, 1))
        @test prove_elimination(ws_nz, :u; max_degree=3).stop_reason === :nonquadratic_elimination
        @test eliminate_variable!(ws_nz, :u; max_degree=3).stop_reason === :nonquadratic_elimination
        # eliminate_low_degree! skips nonzero-field degree-3 vertices in O(1) with 0 edge/exact work:
        rep_nz = eliminate_low_degree!(ws_nz; max_degree=3)
        @test rep_nz.stop_reason === :quiescent && rep_nz.deductions == 0 && rep_nz.exact_work == 0
    end
    # Nonzero field where |h_u| >= |J1|+|J2|+|J3| (0 fill) or |J3| >= |J1|+|J2|+|h_u| (at most 2 fill edges incident to w_3; alpha_123 == 0) is proved and eliminated:
    for (L_dom, Q_dom) in (
        ([5.0, 0.25, -0.5, 0.75], Q_star),
        ([0.5, 0.25, -0.5, 0.75], [0.0 1.0 1.0 3.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]),
        ([-0.5, 0.25, -0.5, 0.75], [0.0 -1.0 1.0 -2.5; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]),
    )
        ws_dom = Workspace(fixture([:u, :w1, :w2, :w3], L_dom, Q_dom; domain=:spin); rules=:elimination)
        att_dom = prove_elimination(ws_dom, :u; max_degree=3)
        @test att_dom.stop_reason === :proved
        @test verify_certificate(ws_dom, att_dom.certificate).valid
        # Forged EliminationStep on a nonzero-field degree-3 vertex with wrong linear_deltas is rejected by verify_certificate:
        forged_step = EliminationStep(1, (2, 3, 4), (-1, -1, -1, -1, -1, -1, -1, -1),
                                      R(-5), (), (), R(0), 0, 0, true)
        forged_cert = QUBOPreprocessing.DominanceCertificate(
            generation(ws_dom), checkpoint(ws_dom), (), (forged_step,), ws_dom._snapshot,
        )
        @test verify_certificate(ws_dom, forged_cert).stop_reason === :invalid_bound
        # Now eliminate via eliminate_low_degree!(ws_dom; max_degree=3) and verify full ground-state preservation:
        rep_dom = eliminate_low_degree!(ws_dom; max_degree=3)
        @test rep_dom.stop_reason === :quiescent && rep_dom.deductions == 4
        @test verify_certificate(ws_dom, export_certificate(ws_dom)).valid
        res_dom = materialize(ws_dom; coefficient_type=R)
        rec_dom = reconstruct(res_dom, Int[])
        best_dom = minimum(reference(L_dom, Q_dom, 1.0, 0.0, [s1, s2, s3, s4], R)
                           for s1 in (-1, 1), s2 in (-1, 1), s3 in (-1, 1), s4 in (-1, 1))
        @test reference(L_dom, Q_dom, 1.0, 0.0, rec_dom.state, R) == best_dom
    end
    # Regression tests for fill-blocked and deferred degree-3 nonzero-field (alpha_123 == 0) eliminations:
    # 1. Heavy-edge degree-3 vertex with h_u != 0 and actual_fill == 2 deferred at max_fill=0 reports :fill_limit in schedule_reductions!:
    Q_fill_dom = zeros(8, 8)
    Q_fill_dom[1, 2] = 1.0; Q_fill_dom[1, 3] = 1.0; Q_fill_dom[1, 4] = 3.0
    for i in 2:8, j in (i + 1):8
        (i <= 4 && j <= 4) && continue
        Q_fill_dom[i, j] = 1.0
    end
    L_fill_dom = [0.5, 0.25, -0.5, 0.75, 0.1, -0.2, 0.3, -0.4]
    ws_fill_dom = Workspace(fixture([:u, :w1, :w2, :w3, :c1, :c2, :c3, :c4], L_fill_dom, Q_fill_dom; domain=:spin); rules=:mixed)
    rep_fill_dom = schedule_reductions!(ws_fill_dom; enable_dominance=false, enable_elimination=false, enable_relations=false, enable_star_triangle=true, max_fill=0)
    @test rep_fill_dom.stop_reason === :fill_limit
    # 2. Deferred zero-field degree-3 vertex whose neighbor :v is eliminated (replacing edge (u,v) with fill edge (u,w3) and inducing h_u != 0 with alpha_123 != 0 while keeping degree(:u) == 3 and u in elim_deferred[4]) is skipped by _next_deferred_elim / _count_deferred_elim / _has_fill_blocked_elim:
    Q_def_cond = zeros(8, 8)
    # :u (1) connected to :w1 (2), :w2 (3), :v (4) with J = (1.0, -1.5, 2.0) and h_u = 0:
    Q_def_cond[1, 2] = 1.0; Q_def_cond[1, 3] = -1.5; Q_def_cond[1, 4] = 2.0
    # :v (4) also connected to :w3 (5) with J_{v,w3} = 2.0 and h_v = 1.0 (so eliminating :v adds edge (u,w3) with J_{u,w3} = -0.5 and shifts h_u by -0.5):
    Q_def_cond[4, 5] = 2.0
    # Make :w1, :w2, :w3, :c1, :c2, :c3 high degree so only :u is degree 3 and :v is degree 2:
    for i in (2, 3, 5, 6, 7, 8), j in (2, 3, 5, 6, 7, 8)
        i < j || continue
        (i <= 3 && j <= 3) && continue
        Q_def_cond[i, j] = 1.0
    end
    L_def_cond = [0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]
    ws_def_cond = Workspace(fixture([:u, :w1, :w2, :v, :w3, :c1, :c2, :c3], L_def_cond, Q_def_cond; domain=:spin); rules=:mixed)
    # Defer :u in bucket 4 at max_fill = 0:
    rep_def1 = schedule_reductions!(ws_def_cond; enable_dominance=false, enable_elimination=false, enable_relations=false, enable_star_triangle=true, max_fill=0)
    @test rep_def1.stop_reason === :fill_limit
    @test 1 in ws_def_cond._state.elim_deferred[4] && ws_def_cond._state.elim_blocked_fill[4][1] == 3
    @test QUBOPreprocessing._count_deferred_elim(ws_def_cond, 3, 3; min_bucket=4) == 1
    # Now eliminate degree-2 vertex :v, which replaces (u,v) with (u,w3) and shifts h_u to -0.5 so alpha_123(u) != 0 while keeping degree(:u) == 3:
    @test eliminate_variable!(ws_def_cond, :v; max_degree=2).stop_reason === :applied
    @test degree(ws_def_cond, :u) == 3 && !QUBOPreprocessing._is_quadratic_deg3(ws_def_cond, 1)
    @test 1 in ws_def_cond._state.elim_deferred[4] && !ws_def_cond._state.elim_queued[4][1]
    @test QUBOPreprocessing._next_deferred_elim(ws_def_cond, 3, 3; min_bucket=4) == 0
    @test QUBOPreprocessing._count_deferred_elim(ws_def_cond, 3, 3; min_bucket=4) == 0
    @test !QUBOPreprocessing._has_fill_blocked_elim(ws_def_cond, 4, 0)
    @test !(:star_triangle in schedule_reductions!(ws_def_cond; enable_dominance=false, enable_elimination=false, enable_relations=false, enable_star_triangle=false, max_fill=3).optional_passes_disabled)
    # Forged EliminationStep with zero-coupling neighbor or zero delta in linear_deltas/quadratic_deltas is rejected:
    ws_z = Workspace(fixture([:u, :w1, :w2, :w3], zeros(4), [0.0 1.0 1.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]; domain=:spin))
    forged_zero_nbr = EliminationStep(1, (2, 3, 4), (-1, -1, -1, -1, -1, -1, -1, -1), R(0), (), (), R(0), 0, 0, false)
    @test verify_certificate(ws_z, QUBOPreprocessing.DominanceCertificate(generation(ws_z), checkpoint(ws_z), (), (forged_zero_nbr,), ws_z._snapshot)).stop_reason === :invalid_step
    ws_ok3 = Workspace(fixture([:u, :w1, :w2, :w3], zeros(4), Q_star; domain=:spin))
    valid_s3 = only(prove_elimination(ws_ok3, :u; max_degree=3).certificate.steps)
    forged_zlin = EliminationStep(1, (2, 3, 4), valid_s3.table, valid_s3.constant_delta, (2 => R(0),), valid_s3.quadratic_deltas, valid_s3.constant, 0, 0, true)
    @test verify_certificate(ws_ok3, QUBOPreprocessing.DominanceCertificate(generation(ws_ok3), checkpoint(ws_ok3), (), (forged_zlin,), ws_ok3._snapshot)).stop_reason === :invalid_step
    forged_zquad = EliminationStep(1, (2, 3, 4), valid_s3.table, valid_s3.constant_delta, (), ((2, 3, R(0)),), valid_s3.constant, 0, 0, true)
    @test verify_certificate(ws_ok3, QUBOPreprocessing.DominanceCertificate(generation(ws_ok3), checkpoint(ws_ok3), (), (forged_zquad,), ws_ok3._snapshot)).stop_reason === :invalid_step

    # 3. Conditioning can create or cancel a center field on a degree-4 -> degree-3 vertex:
    Q_deg4 = zeros(5, 5)
    Q_deg4[1, 2] = 1.0; Q_deg4[1, 3] = -1.5; Q_deg4[1, 4] = 2.0; Q_deg4[1, 5] = 0.75
    ws_cond = Workspace(fixture([:u, :w1, :w2, :w3, :w4], [0.0, 0.25, -0.5, 0.75, 0.0], Q_deg4; domain=:spin); rules=:elimination)
    @test degree(ws_cond, :u) == 4
    @test prove_elimination(ws_cond, :u; max_degree=3).stop_reason === :degree_too_high
    cp_root4 = checkpoint(ws_cond)
    # Assuming :w4 = 1 drops :u to degree 3, but creates effective field h_u = +0.75 != 0, invalidating eligibility!
    assume!(ws_cond, :w4, 1)
    @test degree(ws_cond, :u) == 3
    @test !iszero(QUBOPreprocessing._spin_field(ws_cond, 1))
    @test prove_elimination(ws_cond, :u; max_degree=3).stop_reason === :nonquadratic_elimination
    @test eliminate_low_degree!(ws_cond; max_degree=3, max_deductions=1).deductions == 1 # eliminates degree-1 :w1, skips :u!
    @test ws_cond._state.fixed[1] == 2 # :u was NOT eliminated at degree 3!
    rollback!(ws_cond, cp_root4)
    @test degree(ws_cond, :u) == 4

    # Conversely, if initial h_u = -0.75, assuming :w4 = 1 cancels the field of :u to 0 and unlocks degree-3 elimination!
    ws_cancel = Workspace(fixture([:u, :w1, :w2, :w3, :w4], [-0.75, 0.25, -0.5, 0.75, 0.0], Q_deg4; domain=:spin); rules=:elimination)
    assume!(ws_cancel, :w4, 1)
    @test degree(ws_cancel, :u) == 3 && iszero(QUBOPreprocessing._spin_field(ws_cancel, 1))
    @test prove_elimination(ws_cancel, :u; max_degree=3).stop_reason === :proved
    @test eliminate_variable!(ws_cancel, :u; max_degree=3).stop_reason === :applied
    @test eliminate_low_degree!(ws_cancel; max_degree=2).deductions == 3
    @test verify_certificate(ws_cancel, export_certificate(ws_cancel)).valid

    # 4. Composition of relations, star-triangle (degree 3) and degree <= 2 eliminations:
    #    Start with a 5-vertex graph where :r1 and :r2 are strongly equivalent (J_{r1,r2} = -5.0),
    #    both coupled to zero-field :u, which is also coupled to :w1 and :w2 (and w1-w2-u have couplings).
    #    Initially :u has degree 3 (neighbors :r1, :w1, :w2) and zero field, plus :r1=:r2 contracts first!
    L_comp = [0.0, 0.0, 0.0, 0.5, -0.75]
    Q_comp = [
        0.0 -5.0  1.0  1.0  0.0; # :r1
        0.0  0.0  1.0  0.0  1.0; # :r2
        0.0  0.0  0.0 -1.5  2.0; # :u (zero field, neighbors :r1, :r2, :w1, :w2 -> degree 4 initially!)
        0.0  0.0  0.0  0.0 -0.5; # :w1
        0.0  0.0  0.0  0.0  0.0  # :w2
    ]
    m_comp = fixture([:r1, :r2, :u, :w1, :w2], L_comp, Q_comp; domain=:spin)
    ws_comp = Workspace(m_comp; rules=:relations)
    @test degree(ws_comp, :u) == 4
    # Contracting :r1 and :r2 drops :u from degree 4 to degree 3 with h_u == 0!
    rep_rel = contract_relations!(ws_comp; max_deductions=1)
    @test rep_rel.deductions >= 1
    @test degree(ws_comp, :u) == 3 && iszero(QUBOPreprocessing._spin_field(ws_comp, 3))
    # Now eliminate_low_degree!(ws_comp; max_degree=3) eliminates :u (degree 3) and cascades the rest to 0 variables!
    rep_el3 = eliminate_low_degree!(ws_comp; max_degree=3)
    @test rep_el3.stop_reason === :quiescent
    @test QT.dimension(export_model(materialize(ws_comp))) == 0
    @test verify_certificate(ws_comp, export_certificate(ws_comp)).valid
    rec_comp = reconstruct(materialize(ws_comp; coefficient_type=R), Int[])
    # Check against brute force over all 32 states:
    best_comp = minimum(reference(L_comp, Q_comp, 1.0, 0.0, [s1, s2, s3, s4, s5], R)
                        for s1 in (-1, 1), s2 in (-1, 1), s3 in (-1, 1), s4 in (-1, 1), s5 in (-1, 1))
    @test reference(L_comp, Q_comp, 1.0, 0.0, rec_comp.state, R) == best_comp

    # 5. Progressive max_degree (0 -> 1 -> 2 -> 3) and progressive max_fill (0 -> 1 -> 2 -> 3) with rollback:
    #    - K_4 with zero field on vertex 1: all 3 neighbor pairs (2,3), (2,4), (3,4) ALREADY exist, so actual_fill == 0!
    Q_k4 = [0.0 1.0 -1.5 2.0; 0.0 0.0 0.5 -0.75; 0.0 0.0 0.0 1.25; 0.0 0.0 0.0 0.0]
    ws_k4 = Workspace(fixture([:u, :w1, :w2, :w3], [0.0, 0.25, -0.5, 0.75], Q_k4; domain=:spin); rules=:elimination)
    @test eliminate_low_degree!(ws_k4; max_degree=2).deductions == 0
    # Even with max_fill=0, :u on K_4 introduces 0 new fill edges, so it IS eliminated and cascades!
    @test eliminate_low_degree!(ws_k4; max_degree=3, max_fill=0).deductions == 4
    @test verify_certificate(ws_k4, export_certificate(ws_k4)).valid

    #    - Star on 4 vertices (no existing triangle edges) with J = [1, 1, 3] (actual_fill == 2 because ΔJ_12 == 0)
    #      and J = [1, 1, 1] (actual_fill == 3):
    Q_star2 = [0.0 1.0 1.0 3.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]
    ws_fill = Workspace(fixture([:u, :w1, :w2, :w3], [0.0, 0.25, -0.5, 0.75], Q_star2; domain=:spin); rules=:elimination)
    # Eliminate leaves :w1, :w2, :w3? Wait: in Q_star2, :w1, :w2, :w3 have degree 1!
    # To make :w1, :w2, :w3 have degree >= 4 so only :u has degree 3, attach :w1, :w2, :w3 to a K_5 core!
    L_sc = zeros(8)
    L_sc[2:8] .= [0.25, -0.5, 0.75, 0.1, -0.2, 0.3, -0.4]
    Q_sc = zeros(8, 8)
    Q_sc[1, 2] = 1.0; Q_sc[1, 3] = 1.0; Q_sc[1, 4] = 3.0 # :u has degree 3, actual_fill == 2 ((2,4) and (3,4))
    for i in 2:4, j in 5:8
        Q_sc[i, j] = 0.5 * ((i + j) % 2 == 0 ? 1 : -1)
    end
    for i in 5:8, j in (i+1):8
        Q_sc[i, j] = 1.0
    end
    ws_sc = Workspace(fixture([Symbol("v$i") for i in 1:8], L_sc, Q_sc; domain=:spin); rules=:elimination)
    @test degree(ws_sc, :v1) == 3 && all(i -> degree(ws_sc, Symbol("v$i")) >= 4, 2:8)
    @test eliminate_low_degree!(ws_sc; max_degree=3, max_fill=0).deductions == 0
    @test eliminate_low_degree!(ws_sc; max_degree=3, max_fill=1).deductions == 0
    cp_sc1 = checkpoint(ws_sc)
    # Check max_work=0 and expired deadline_ns before deferred re-queue:
    rep_sc_w0 = eliminate_low_degree!(ws_sc; max_degree=3, max_fill=2, max_work=0)
    @test rep_sc_w0.stop_reason === :work_limit && rep_sc_w0.pending == 1 && checkpoint(ws_sc) == cp_sc1
    rep_sc_dl = eliminate_low_degree!(ws_sc; max_degree=3, max_fill=2, deadline_ns=UInt64(1))
    @test rep_sc_dl.stop_reason === :deadline && rep_sc_dl.pending == 1 && checkpoint(ws_sc) == cp_sc1
    # Now with max_fill=2, :v1 IS re-queued and eliminated!
    rep_sc2 = eliminate_low_degree!(ws_sc; max_degree=3, max_fill=2)
    @test rep_sc2.stop_reason === :quiescent && rep_sc2.deductions == 1
    @test verify_certificate(ws_sc, export_certificate(ws_sc)).valid
    # Rollback to cp_sc1 undoes both the elimination and the deferred re-queue:
    rollback!(ws_sc, cp_sc1)
    @test degree(ws_sc, :v1) == 3
    @test eliminate_low_degree!(ws_sc; max_degree=3, max_fill=1).deductions == 0
    @test eliminate_low_degree!(ws_sc; max_degree=3, max_fill=2).deductions == 1
    rollback!(ws_sc, cp_sc1)

    # Also test duplicate entries in elim_queues[4][1:(elim_heads[4]-1)] (popped at max_fill=0,
    # re-queued when a degree-2 subdivision vertex on one leg is eliminated, popped again at max_fill=0,
    # and deduplicated by _count_deferred_elim):
    L_dup = zeros(9)
    L_dup[2:9] .= 0.25
    L_dup[9] = 0.0 # degree-2 vertex :v9 between :v1 and :v2
    Q_dup = zeros(9, 9)
    Q_dup[1, 9] = 1.0; Q_dup[2, 9] = 1.0; Q_dup[1, 3] = 1.0; Q_dup[1, 4] = 1.0
    for i in 2:4, j in 5:8
        Q_dup[i, j] = 0.5
    end
    for i in 5:8, j in (i+1):8
        Q_dup[i, j] = 1.0
    end
    ws_dup = Workspace(fixture([Symbol("v$i") for i in 1:9], L_dup, Q_dup; domain=:spin); rules=:elimination)
    # First run with max_degree=3, max_fill=0: :v9 (deg 2, fill 1) and :v1 (deg 3, fill 3) are both popped with blocked_fill > 0:
    @test eliminate_low_degree!(ws_dup; max_degree=3, max_fill=0).deductions == 0
    # Now eliminate :v9 via max_degree=2, max_fill=1: this touches :v1 (keeping :v1 at degree 3!) and pushes :v1 to elim_queues[4] a 2nd time!
    @test eliminate_low_degree!(ws_dup; max_degree=2, max_fill=1).deductions == 1
    # Pop :v1 a 2nd time with max_fill=0:
    @test eliminate_low_degree!(ws_dup; max_degree=3, max_fill=0).deductions == 0
    # Now :v1 appears twice in elim_queues[4][1:(elim_heads[4]-1)]; check deduplicated pending == 1 and re-queue with max_fill=3:
    @test eliminate_low_degree!(ws_dup; max_degree=3, max_fill=3, max_work=0).pending == 1
    @test eliminate_low_degree!(ws_dup; max_degree=3, max_fill=3).deductions == 1
    @test verify_certificate(ws_dup, export_certificate(ws_dup)).valid
end

@testset "0-, 1-, and 2-Separator Biconnected Block Elimination" begin
    R = Rational{BigInt}

    # 1. 0-separator (|S| = 0) K_4 block where every vertex has degree 3 and alpha_123 != 0
    L_k4 = [0.5, -0.25, 0.75, -0.5]
    Q_k4 = [0.0 1.0 1.0 1.0;
            0.0 0.0 1.0 1.0;
            0.0 0.0 0.0 1.0;
            0.0 0.0 0.0 0.0]
    m_k4 = fixture([:x1, :x2, :x3, :x4], L_k4, Q_k4; domain=:spin, sense=:min)
    ws_k4 = Workspace(m_k4; rules=:elimination)
    # Single-vertex degree-3 elimination cannot eliminate any vertex because alpha_123 != 0:
    @test eliminate_low_degree!(ws_k4; max_degree=3).deductions == 0
    att_k4 = prove_elimination(ws_k4, [:x1, :x2, :x3, :x4])
    @test att_k4.stop_reason === :proved
    @test length(att_k4.certificate.steps) == 4
    @test verify_certificate(ws_k4, att_k4.certificate).valid
    @test certificate_guarantee(att_k4.certificate) === :exact_elimination

    rep_k4 = eliminate_low_degree!(ws_k4; enable_blocks=true, max_block_size=4, max_separator=0)
    @test rep_k4.stop_reason === :quiescent
    @test rep_k4.deductions == 4
    @test verify_certificate(ws_k4, export_certificate(ws_k4)).valid
    rec_k4 = reconstruct(materialize(ws_k4; coefficient_type=R), Int[])
    best_k4 = minimum(
        reference(L_k4, Q_k4, 1.0, 0.0, [s1, s2, s3, s4], R)
        for s1 in (-1, 1), s2 in (-1, 1), s3 in (-1, 1), s4 in (-1, 1)
    )
    @test reference(L_k4, Q_k4, 1.0, 0.0, rec_k4.state, R) == best_k4
    @test rec_k4.energy.value == best_k4

    # Helper to convert spin (h, J) to an equivalent (L, Q) in either :spin or :bool domain:
    function spin_to_dom(h::Vector{Float64}, J::Matrix{Float64}, dom::Symbol)
        n = length(h)
        dom === :spin && return (copy(h), copy(J))
        L = zeros(Float64, n)
        Q = 4.0 .* J
        for i in 1:n
            s_row = sum(J[min(i, j), max(i, j)] for j in 1:n if j != i; init=0.0)
            L[i] = 2.0 * h[i] - 2.0 * s_row
        end
        return (L, Q)
    end

    # 2. 1-separator (|S| = 1) articulation-point pendant block B = (:b1, :b2, :b3) attached to :s1
    #    Every vertex in B has degree 3 (two internal edges in B + one edge to :s1) with alpha_123 != 0,
    #    and the core (:s1, :c1, :c2, :c3, :c4) is a 5-clique so all core vertices have degree >= 4.
    #    Test both index orderings: s1 < min(B) and min(B) < s1.
    for labels_1sep in (
        [:s1, :c1, :c2, :c3, :c4, :b1, :b2, :b3],
        [:b1, :b2, :b3, :s1, :c1, :c2, :c3, :c4],
    )
        idx_of = Dict(lbl => i for (i, lbl) in enumerate(labels_1sep))
        h_1 = zeros(8)
        h_1[idx_of[:b1]] = 0.5
        h_1[idx_of[:b2]] = -0.25
        h_1[idx_of[:b3]] = 0.75
        h_1[idx_of[:s1]] = -0.5
        h_1[idx_of[:c1]] = 0.25
        h_1[idx_of[:c2]] = -0.75
        h_1[idx_of[:c3]] = 0.5
        h_1[idx_of[:c4]] = -0.25
        J_1 = zeros(8, 8)
        function add_edge!(Q, u, v, w)
            Q[min(u, v), max(u, v)] = w
        end
        add_edge!(J_1, idx_of[:b1], idx_of[:b2], 1.0)
        add_edge!(J_1, idx_of[:b1], idx_of[:b3], 1.0)
        add_edge!(J_1, idx_of[:b2], idx_of[:b3], 1.0)
        add_edge!(J_1, idx_of[:b1], idx_of[:s1], 1.0)
        add_edge!(J_1, idx_of[:b2], idx_of[:s1], -1.0)
        add_edge!(J_1, idx_of[:b3], idx_of[:s1], 1.0)
        core_1 = [:s1, :c1, :c2, :c3, :c4]
        for i in 1:length(core_1), j in (i + 1):length(core_1)
            add_edge!(J_1, idx_of[core_1[i]], idx_of[core_1[j]], isodd(i + j) ? 1.25 : -0.75)
        end

        for dom in (:bool, :spin), sense in (:min, :max)
            L_1, Q_1 = spin_to_dom(h_1, J_1, dom)
            m_1 = fixture(labels_1sep, L_1, Q_1; domain=dom, sense=sense)
            ws_1 = Workspace(m_1; rules=:mixed)
            # Single-vertex degree-3 elimination cannot eliminate any vertex:
            @test eliminate_low_degree!(ws_1; max_degree=3, cascade_dominance=false).deductions == 0
            att_1 = prove_elimination(ws_1, [:b1, :b2, :b3])
            @test att_1.stop_reason === :proved
            @test verify_certificate(ws_1, att_1.certificate).valid

            cp_1 = checkpoint(ws_1)
            rep_b1 = eliminate_variable!(ws_1, [:b1, :b2, :b3])
            @test rep_b1.stop_reason === :applied
            @test rep_b1.changed == 3
            @test verify_certificate(ws_1, export_certificate(ws_1)).valid

            # Verify exact conditional optimum for all 2^5 = 32 assignments of (:s1, :c1, :c2, :c3, :c4)
            exp_1 = materialize(ws_1; coefficient_type=R)
            res_vars_1 = QT.variables(export_model(exp_1))
            vals_dom = dom === :bool ? (0, 1) : (-1, 1)
            for vs in vals_dom, vc1 in vals_dom, vc2 in vals_dom, vc3 in vals_dom, vc4 in vals_dom
                y_dict = Dict(:s1 => vs, :c1 => vc1, :c2 => vc2, :c3 => vc3, :c4 => vc4)
                y_vec = [y_dict[v] for v in res_vars_1]
                rec = reconstruct(exp_1, y_vec)
                opt_b = (sense === :min ? minimum : maximum)(
                    begin
                        st_vec = zeros(Int, 8)
                        st_vec[idx_of[:s1]] = vs
                        st_vec[idx_of[:c1]] = vc1
                        st_vec[idx_of[:c2]] = vc2
                        st_vec[idx_of[:c3]] = vc3
                        st_vec[idx_of[:c4]] = vc4
                        st_vec[idx_of[:b1]] = vb1
                        st_vec[idx_of[:b2]] = vb2
                        st_vec[idx_of[:b3]] = vb3
                        reference(L_1, Q_1, 1.0, 0.0, st_vec, R)
                    end
                    for vb1 in vals_dom, vb2 in vals_dom, vb3 in vals_dom
                )
                @test reference(L_1, Q_1, 1.0, 0.0, rec.state, R) == opt_b
                @test rec.energy.value == opt_b
            end

            # Rollback and test automatic discovery via schedule_reductions!(enable_blocks=true)
            rollback!(ws_1, cp_1)
            @test isempty(reductions(ws_1))
            srep_1 = schedule_reductions!(
                ws_1;
                enable_dominance=false, enable_elimination=false,
                enable_relations=false, enable_star_triangle=false,
                enable_blocks=true, max_block_size=3, max_separator=1,
            )
            @test srep_1.stop_reason === :quiescent
            @test srep_1.elimination_deductions == 3
            @test any(p -> p.pass === :block_elimination && p.deductions == 3, srep_1.passes)
            @test verify_certificate(ws_1, export_certificate(ws_1)).valid
        end
    end

    # 3. 2-separator (|S| = 2) biconnected block B = (:b1, :b2, :b3) across separator S = (:s1, :s2)
    #    Test all three relative index orderings of B vs (s1, s2):
    #    - s1 < s2 < min(B)
    #    - s1 < min(B) < max(B) < s2
    #    - min(B) < max(B) < s1 < s2
    for labels_2sep in (
        [:s1, :s2, :c1, :c2, :c3, :c4, :b1, :b2, :b3],
        [:s1, :b1, :b2, :b3, :s2, :c1, :c2, :c3, :c4],
        [:b1, :b2, :b3, :s1, :s2, :c1, :c2, :c3, :c4],
    )
        idx_of = Dict(lbl => i for (i, lbl) in enumerate(labels_2sep))
        h_2 = zeros(9)
        h_2[idx_of[:b1]] = 0.5
        h_2[idx_of[:b2]] = -0.25
        h_2[idx_of[:b3]] = 0.5
        h_2[idx_of[:s1]] = 0.25
        h_2[idx_of[:s2]] = -0.5
        h_2[idx_of[:c1]] = 0.75
        h_2[idx_of[:c2]] = -0.25
        h_2[idx_of[:c3]] = 0.5
        h_2[idx_of[:c4]] = -0.5
        J_2 = zeros(9, 9)
        function add_edge2!(Q, u, v, w)
            Q[min(u, v), max(u, v)] = w
        end
        # B is a triangle (:b1, :b2, :b3) where :b1, :b2 couple to :s1 and :b2, :b3 couple to :s2
        add_edge2!(J_2, idx_of[:b1], idx_of[:b2], 1.0)
        add_edge2!(J_2, idx_of[:b1], idx_of[:b3], 1.0)
        add_edge2!(J_2, idx_of[:b2], idx_of[:b3], 1.0)
        add_edge2!(J_2, idx_of[:b1], idx_of[:s1], 1.0)
        add_edge2!(J_2, idx_of[:b2], idx_of[:s1], -1.0)
        add_edge2!(J_2, idx_of[:b2], idx_of[:s2], 1.0)
        add_edge2!(J_2, idx_of[:b3], idx_of[:s2], 1.0)
        # Core (:c1, :c2, :c3, :c4) is a 4-clique coupled to both :s1 and :s2 (so degree 5 each),
        # with NO direct edge between :s1 and :s2 initially (so fill == 1)
        c_vars = [:c1, :c2, :c3, :c4]
        for i in 1:length(c_vars)
            add_edge2!(J_2, idx_of[:s1], idx_of[c_vars[i]], isodd(i) ? 1.0 : -1.0)
            add_edge2!(J_2, idx_of[:s2], idx_of[c_vars[i]], isodd(i) ? -1.0 : 1.0)
            for j in (i + 1):length(c_vars)
                add_edge2!(J_2, idx_of[c_vars[i]], idx_of[c_vars[j]], 1.0)
            end
        end

        for dom in (:bool, :spin)
            L_2, Q_2 = spin_to_dom(h_2, J_2, dom)
            m_2 = fixture(labels_2sep, L_2, Q_2; domain=dom, sense=:min)
            ws_2 = Workspace(m_2; rules=:mixed)
            # Single-vertex degree-3 elimination cannot eliminate B:
            @test eliminate_low_degree!(ws_2; max_degree=3, cascade_dominance=false).deductions == 0
            # With max_separator=1, B is refused with :separator_too_large:
            @test prove_elimination(ws_2, [:b1, :b2, :b3]; max_separator=1).stop_reason === :separator_too_large
            @test eliminate_block!(ws_2, [:b1, :b2, :b3]; max_separator=1).stop_reason === :separator_too_large
            # With max_fill=0, B is refused with :fill_limit because eliminating B creates edge (:s1, :s2):
            @test eliminate_block!(ws_2, [:b1, :b2, :b3]; max_fill=0).stop_reason === :fill_limit
            srep_fill = schedule_reductions!(
                ws_2;
                enable_dominance=false, enable_elimination=false,
                enable_relations=false, enable_star_triangle=false,
                enable_blocks=true, max_block_size=3, max_separator=2, max_fill=0,
            )
            @test srep_fill.stop_reason === :fill_limit
            @test srep_fill.deductions == 0

            # Now run schedule_reductions! with max_fill=1 and enable_blocks=true:
            srep_2 = schedule_reductions!(
                ws_2;
                enable_dominance=false, enable_elimination=false,
                enable_relations=false, enable_star_triangle=false,
                enable_blocks=true, max_block_size=3, max_separator=2, max_fill=1,
            )
            @test srep_2.stop_reason === :quiescent
            @test srep_2.elimination_deductions == 3
            @test srep_2.fill_edges == 1
            cert_2 = export_certificate(ws_2)
            @test verify_certificate(ws_2, cert_2).valid

            # Check DomainGaugeMap transport and witness satisfaction:
            g_vec = [isodd(i) ? -1 : 1 for i in 1:9]
            for target_dom in (:bool, :spin)
                dmap = domain_map(ws_2; domain=target_dom, gauge=g_vec)
                tcert = transport_certificate(ws_2, cert_2, dmap)
                @test verify_certificate(ws_2, tcert; map=dmap).valid
                @test verify_certificate(ws_2, export_certificate(ws_2; map=dmap); map=dmap).valid
            end
            w_coerc = coercive_field_witness(ws_2)
            @test length(w_coerc) == 9

            # Verify exact conditional optimum across all 2^6 = 64 states of (:s1, :s2, :c1, :c2, :c3, :c4)
            exp_2 = materialize(ws_2; coefficient_type=R)
            res_vars_2 = QT.variables(export_model(exp_2))
            vals_dom = dom === :bool ? (0, 1) : (-1, 1)
            for vs1 in vals_dom, vs2 in vals_dom, vc1 in vals_dom, vc2 in vals_dom, vc3 in vals_dom, vc4 in vals_dom
                y_dict = Dict(:s1 => vs1, :s2 => vs2, :c1 => vc1, :c2 => vc2, :c3 => vc3, :c4 => vc4)
                y_vec = [y_dict[v] for v in res_vars_2]
                rec = reconstruct(exp_2, y_vec)
                opt_b = minimum(
                    begin
                        st_vec = zeros(Int, 9)
                        st_vec[idx_of[:s1]] = vs1
                        st_vec[idx_of[:s2]] = vs2
                        st_vec[idx_of[:c1]] = vc1
                        st_vec[idx_of[:c2]] = vc2
                        st_vec[idx_of[:c3]] = vc3
                        st_vec[idx_of[:c4]] = vc4
                        st_vec[idx_of[:b1]] = vb1
                        st_vec[idx_of[:b2]] = vb2
                        st_vec[idx_of[:b3]] = vb3
                        reference(L_2, Q_2, 1.0, 0.0, st_vec, R)
                    end
                    for vb1 in vals_dom, vb2 in vals_dom, vb3 in vals_dom
                )
                @test reference(L_2, Q_2, 1.0, 0.0, rec.state, R) == opt_b
                @test rec.energy.value == opt_b
            end
        end
    end

    # 4. Tied block argmin, tie_break (:low vs :high), require_unique, assume!/rollback!, and tamper rejection:
    L_tie = [0.0, 0.0, 0.25]
    Q_tie = [0.0 0.0 0.0;
             0.0 0.0 0.0;
             0.0 0.0 0.0]
    Q_tie[1, 2] = -1.0 # ferromagnetic pair (:b1, :b2) with zero field -> (-1,-1) and (+1,+1) tied!
    Q_tie[1, 3] = 1.0
    Q_tie[2, 3] = -1.0 # for s3 in {-1, +1}, b1 == b2 has 0 net coupling to s3, so (-1,-1) and (+1,+1) remain tied!
    m_tie = fixture([:b1, :b2, :s3], L_tie, Q_tie; domain=:spin, sense=:min)
    ws_tie_lo = Workspace(m_tie; rules=:elimination)
    @test prove_elimination(ws_tie_lo, [:b1, :b2]; require_unique=true).stop_reason === :not_strict
    @test eliminate_block!(ws_tie_lo, [:b1, :b2]; require_unique=true).stop_reason === :not_strict

    att_tie_lo = prove_elimination(ws_tie_lo, [:b1, :b2]; tie_break=:low)
    att_tie_hi = prove_elimination(ws_tie_lo, [:b1, :b2]; tie_break=:high)
    @test att_tie_lo.stop_reason === :proved && att_tie_hi.stop_reason === :proved
    @test persistency(att_tie_lo.certificate) === :weak
    @test all(==(-1), att_tie_lo.certificate.steps[1].table)
    @test all(==(1), att_tie_hi.certificate.steps[1].table)
    @test verify_certificate(ws_tie_lo, att_tie_lo.certificate).valid
    @test verify_certificate(ws_tie_lo, att_tie_hi.certificate).valid

    # DomainGaugeMap tie_break invariance:
    dmap_tie = domain_map(ws_tie_lo; domain=:bool, gauge=[-1, -1, 1])
    att_tie_map_lo = prove_elimination(ws_tie_lo, [:b1, :b2]; map=dmap_tie, tie_break=:low)
    @test att_tie_map_lo.stop_reason === :proved
    @test verify_certificate(ws_tie_lo, att_tie_map_lo.certificate; map=dmap_tie).valid
    # In gauged bool with gauge -1 on :b1, :b2, target low (0) corresponds to original +1:
    @test all(==(1), att_tie_map_lo.certificate.steps[1].table)

    # Validation & error guards:
    @test_throws ArgumentError prove_elimination(ws_tie_lo, [:b1])
    @test_throws ArgumentError prove_elimination(ws_tie_lo, [:b1, :b2]; max_block_size=1)
    @test_throws ArgumentError prove_elimination(ws_tie_lo, [:b1, :b2]; max_separator=3)
    @test_throws ArgumentError prove_elimination(ws_tie_lo, [:b1, :b1])
    @test prove_elimination(ws_tie_lo, [:b1, :b2, :s3]; max_block_size=2).stop_reason === :block_too_large

    cp_af = checkpoint(ws_tie_lo)
    assume!(ws_tie_lo, :b1, 1)
    @test prove_elimination(ws_tie_lo, [:b1, :b2]).stop_reason === :already_fixed
    rollback!(ws_tie_lo, cp_af)

    m_zs = fixture([:b1, :b2], [0.1, 0.2], [0.0 1.0; 0.0 0.0]; domain=:spin, scale=0.0)
    ws_zs = Workspace(m_zs; rules=:elimination)
    @test prove_elimination(ws_zs, [:b1, :b2]).stop_reason === :zero_scale

    # allow_exact_fallback=false and deduction_limit in eliminate_low_degree! / schedule_reductions!(enable_blocks=true):
    ws_k4_f64 = Workspace(m_k4; rules=:mixed)
    @test eliminate_low_degree!(ws_k4_f64; enable_blocks=true, max_block_size=4, max_separator=0, max_deductions=2).stop_reason === :deduction_limit
    @test schedule_reductions!(ws_k4_f64; enable_blocks=true, max_block_size=4, max_separator=0, allow_exact_fallback=false).deductions == 4

    # Disconnected block rejection:
    m_disc = fixture([:x1, :x2, :x3], [0.1, 0.2, 0.3], [0.0 1.0 0.0; 0.0 0.0 0.0; 0.0 0.0 0.0]; domain=:spin)
    ws_disc = Workspace(m_disc; rules=:elimination)
    @test prove_elimination(ws_disc, [:x1, :x3]).stop_reason === :disconnected_block

    # Tamper rejection in verify_certificate:
    s1_orig = att_tie_lo.certificate.steps[1]::EliminationStep
    s2_orig = att_tie_lo.certificate.steps[2]::EliminationStep
    bw1 = s1_orig.block_witness
    # Tamper block_phi (both steps sharing bad block_phi -> :invalid_bound; mismatched -> :invalid_step):
    bw1_bad_phi = QUBOPreprocessing._BlockEliminationWitness(
        bw1.block_variables, 1, bw1.block_tables, (bw1.block_phi[1] + 1, bw1.block_phi[2]),
    )
    bw2_bad_phi = QUBOPreprocessing._BlockEliminationWitness(
        bw1.block_variables, 2, bw1.block_tables, (bw1.block_phi[1] + 1, bw1.block_phi[2]),
    )
    s1_bad_phi = EliminationStep(
        s1_orig.variable, s1_orig.neighbors, s1_orig.table,
        s1_orig.constant_delta, s1_orig.linear_deltas, s1_orig.quadratic_deltas,
        s1_orig.constant, s1_orig.predecessors, s1_orig.scope_length, s1_orig.unique_argmin, bw1_bad_phi,
    )
    s2_bad_phi = EliminationStep(
        s2_orig.variable, s2_orig.neighbors, s2_orig.table,
        s2_orig.constant_delta, s2_orig.linear_deltas, s2_orig.quadratic_deltas,
        s2_orig.constant, s2_orig.predecessors, s2_orig.scope_length, s2_orig.unique_argmin, bw2_bad_phi,
    )
    cert_bad_phi = DominanceCertificate(
        generation(ws_tie_lo), att_tie_lo.certificate._scope_checkpoint,
        att_tie_lo.certificate.assumptions, (s1_bad_phi, s2_orig),
        att_tie_lo.certificate._source, nothing,
    )
    @test verify_certificate(ws_tie_lo, cert_bad_phi).stop_reason === :invalid_step
    cert_both_bad_phi = DominanceCertificate(
        generation(ws_tie_lo), att_tie_lo.certificate._scope_checkpoint,
        att_tie_lo.certificate.assumptions, (s1_bad_phi, s2_bad_phi),
        att_tie_lo.certificate._source, nothing,
    )
    @test verify_certificate(ws_tie_lo, cert_both_bad_phi).stop_reason === :invalid_bound

    # Tamper final step constant_delta -> :invalid_bound:
    s2_bad_delta = EliminationStep(
        s2_orig.variable, s2_orig.neighbors, s2_orig.table,
        s2_orig.constant_delta + 1, s2_orig.linear_deltas, s2_orig.quadratic_deltas,
        s2_orig.constant, s2_orig.predecessors, s2_orig.scope_length, s2_orig.unique_argmin, s2_orig.block_witness,
    )
    cert_bad_delta = DominanceCertificate(
        generation(ws_tie_lo), att_tie_lo.certificate._scope_checkpoint,
        att_tie_lo.certificate.assumptions, (s1_orig, s2_bad_delta),
        att_tie_lo.certificate._source, nothing,
    )
    @test verify_certificate(ws_tie_lo, cert_bad_delta).stop_reason === :invalid_bound

    # Nested 2-separator sub-block discovery, deduction_limit skip of oversized blocks,
    # and block_fill_blocked reset when a fill-blocked super-block is superseded:
    # Construct B = (1, 2) with 2-separator (3, 4), where 4 is also a degree-2 bridge to core 5,
    # so blocking s1 = 3 alone closes B1 = (1, 2, 4) with 2-separator (3, 5) (which introduces fill (3, 5)),
    # while blocking (s1 = 3, s2 = 4) closes B = (1, 2) with 2-separator (3, 4) where edge (3, 4) ALREADY exists (0 fill!).
    labels_nested = [:b1, :b2, :s1, :s2, :c1, :c2, :c3, :c4, :c5, :c6]
    h_nest = [0.25, -0.5, 0.1, -0.2, 0.3, -0.4, 0.2, -0.1, 0.15, -0.25]
    J_nest = zeros(10, 10)
    J_nest[1, 2] = 1.0
    J_nest[1, 3] = 1.0; J_nest[2, 3] = -1.0
    J_nest[1, 4] = 1.0; J_nest[2, 4] = 1.0
    J_nest[3, 4] = 1.0 # existing edge between :s1 (3) and :s2 (4), so eliminating B = (:b1, :b2) has 0 fill!
    J_nest[4, 5] = 1.0 # :s2 (4) only connects to :b1, :b2, :s1, :c1 -> so B1 = (:b1, :b2, :s2) has 2-separator (:s1, :c1) with NO edge (:s1, :c1) (fill = 1)!
    # Make (:c1..:c6) a 6-clique (degree >= 5 > D_max = 4) and connect :s1 (3) to :c2..:c6 (with NO edge between :s1 and :c1 so B1 has fill = 1):
    for u in 6:10
        J_nest[3, u] = isodd(u) ? 1.0 : -1.0
    end
    for u in 5:10, v in (u + 1):10
        J_nest[u, v] = 1.0
    end
    m_nest = fixture(labels_nested, h_nest, J_nest; domain=:spin, sense=:min)
    ws_nest = Workspace(m_nest; rules=:mixed)
    # 1. Both B1 = [1, 2, 4] (size 3, fill 1) and B = [1, 2] (size 2, fill 0) are discovered:
    blocks_nest, r_nest, _ = QUBOPreprocessing._find_separator_blocks(ws_nest; max_block_size=3, max_separator=2)
    @test r_nest === :ok
    @test [1, 2, 4] in blocks_nest && [1, 2] in blocks_nest
    # 2. With max_deductions=2, B1 (size 3) is skipped and B (size 2) is eliminated:
    ws_nest_ded = Workspace(m_nest; rules=:mixed)
    rep_nest_ded = eliminate_low_degree!(
        ws_nest_ded; max_degree=1, cascade_dominance=false,
        enable_blocks=true, max_block_size=3, max_separator=2, max_deductions=2,
    )
    @test rep_nest_ded.stop_reason === :deduction_limit
    @test rep_nest_ded.deductions == 2
    # 3. With max_fill=0 in schedule_reductions!, B1 (fill=1) is skipped (setting fblocked=true),
    #    B (fill=0) is applied (resetting block_fill_blocked=false), and since only :s2 remains in is_cand,
    #    the next block pass finds 0 blocks and finishes with :quiescent!
    srep_nest = schedule_reductions!(
        ws_nest;
        enable_dominance=false, enable_elimination=false,
        enable_relations=false, enable_star_triangle=false,
        enable_blocks=true, max_block_size=3, max_separator=2, max_fill=0,
    )
    @test srep_nest.stop_reason === :quiescent
    @test srep_nest.elimination_deductions == 2
    @test verify_certificate(ws_nest, export_certificate(ws_nest)).valid

    # Tamper unique_argmin:
    s1_bad_ua = EliminationStep(
        s1_orig.variable, s1_orig.neighbors, s1_orig.table,
        s1_orig.constant_delta, s1_orig.linear_deltas, s1_orig.quadratic_deltas,
        s1_orig.constant, s1_orig.predecessors, s1_orig.scope_length, true, s1_orig.block_witness,
    )
    s2_bad_ua = EliminationStep(
        s2_orig.variable, s2_orig.neighbors, s2_orig.table,
        s2_orig.constant_delta, s2_orig.linear_deltas, s2_orig.quadratic_deltas,
        s2_orig.constant, s2_orig.predecessors, s2_orig.scope_length, true, s2_orig.block_witness,
    )
    cert_bad_ua = DominanceCertificate(
        generation(ws_tie_lo), att_tie_lo.certificate._scope_checkpoint,
        att_tie_lo.certificate.assumptions, (s1_bad_ua, s2_bad_ua),
        att_tie_lo.certificate._source, nothing,
    )
    @test verify_certificate(ws_tie_lo, cert_bad_ua).stop_reason === :invalid_bound

    # Tamper step table vs block_tables and incomplete batch:
    s2_bad_tbl = EliminationStep(
        s2_orig.variable, s2_orig.neighbors, (1, 1),
        s2_orig.constant_delta, s2_orig.linear_deltas, s2_orig.quadratic_deltas,
        s2_orig.constant, s2_orig.predecessors, s2_orig.scope_length, s2_orig.unique_argmin, s2_orig.block_witness,
    )
    cert_bad_tbl = DominanceCertificate(
        generation(ws_tie_lo), att_tie_lo.certificate._scope_checkpoint,
        att_tie_lo.certificate.assumptions, (s1_orig, s2_bad_tbl),
        att_tie_lo.certificate._source, nothing,
    )
    @test verify_certificate(ws_tie_lo, cert_bad_tbl).stop_reason === :invalid_step

    cert_incomplete = DominanceCertificate(
        generation(ws_tie_lo), att_tie_lo.certificate._scope_checkpoint,
        att_tie_lo.certificate.assumptions, (s1_orig,),
        att_tie_lo.certificate._source, nothing,
    )
    @test verify_certificate(ws_tie_lo, cert_incomplete).stop_reason === :invalid_step
end



