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
    @test deductions(ws_casc) == [:hub => -1, :t2 => 1, :t3 => 1]
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
        @test ws._state.elim_head == 1
        @test length(ws._state.elim_queue) == 4
        @test all(ws._state.elim_queued)
    end

    ws_dl = Workspace(m4; rules=:elimination)
    @test eliminate_low_degree!(ws_dl; deadline_ns=UInt64(0)).stop_reason === :deadline
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; max_degree=3)
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; max_degree=-1)
    @test_throws ArgumentError eliminate_low_degree!(ws_dl; tie_break=:none)
    @test_throws ArgumentError eliminate_low_degree!(Workspace(m4; rules=:identity); cascade_dominance=true)

    # Rollback of a reduction that newly queues a degree-4 -> degree-3 neighbor:
    Q_k4_leaf = zeros(5, 5)
    Q_k4_leaf[1, 2] = -1.5
    for i in 2:5, j in (i+1):5
        Q_k4_leaf[i, j] = 1.0
    end
    ws_k4_leaf = Workspace(fixture([:x1, :x2, :x3, :x4, :x5], zeros(5), Q_k4_leaf); rules=:elimination)
    @test !ws_k4_leaf._state.elim_queued[2] # initially degree 4
    cp_k4 = checkpoint(ws_k4_leaf)
    @test eliminate_variable!(ws_k4_leaf, :x1).stop_reason === :applied
    @test ws_k4_leaf._state.elim_queued[2] # lowered to degree 3 and queued
    rollback!(ws_k4_leaf, cp_k4)
    @test !ws_k4_leaf._state.elim_queued[2]

    # Direct cancellation-to-queue regression: eliminating degree-2 :x1 cancels
    # existing edge (:x2, :x3), dropping :x2 and :x3 from degree 4 to degree 2,
    # removing the edge from adjacency/adj_pos, and queuing both in elim_queue.
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
    @test !ws_canc._state.elim_queued[2]
    @test !ws_canc._state.elim_queued[3]
    @test haskey(ws_canc._state.adj_pos[2], 3)
    cp_canc = checkpoint(ws_canc)
    @test eliminate_variable!(ws_canc, :x1).stop_reason === :applied
    @test degree(ws_canc, :x2) == 2
    @test degree(ws_canc, :x3) == 2
    @test !haskey(ws_canc._state.adj_pos[2], 3)
    @test !haskey(ws_canc._state.adj_pos[3], 2)
    @test all(first(p) != 3 for p in ws_canc._state.adjacency[2])
    @test ws_canc._state.elim_queued[2]
    @test ws_canc._state.elim_queued[3]
    rollback!(ws_canc, cp_canc)
    @test degree(ws_canc, :x2) == 4
    @test degree(ws_canc, :x3) == 4
    @test haskey(ws_canc._state.adj_pos[2], 3)
    @test haskey(ws_canc._state.adj_pos[3], 2)
    @test !ws_canc._state.elim_queued[2]
    @test !ws_canc._state.elim_queued[3]

    # Progressive max_degree cutoff increases (0 -> 1 -> 2 and 1 -> 2) with checkpoints/rollback:
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
    @test r_cut0.pending == 0
    # Repeated call at same cutoff does not re-scan deferred vertices
    @test eliminate_low_degree!(ws_tri; max_degree=0).candidates == 0
    cp_tri1 = checkpoint(ws_tri)
    r_cut1 = eliminate_low_degree!(ws_tri; max_degree=1)
    @test r_cut1.stop_reason === :quiescent
    @test r_cut1.deductions == 0
    @test r_cut1.candidates == 0 # degree-2 vertices remain deferred without re-popping at max_degree=1
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
    @test isempty(ws_tri._state.elim_deferred)
    @test !any(ws_tri._state.elim_in_deferred)
    @test all(==(Int8(4)), ws_tri._state.elim_deferred_cutoff)

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
    @test rep_s.candidates == rep_l.candidates == 3
    @test rep_s.edge_visits == rep_l.edge_visits
    @test rep_s.deductions == rep_l.deductions == 3
    @test rep_s.exact_work == rep_l.exact_work
    bytes_s = @allocated elim_cycle!(ws_small, cp_s)
    bytes_l = @allocated elim_cycle!(ws_large, cp_l)
    @test bytes_l <= bytes_s + 2048
end

