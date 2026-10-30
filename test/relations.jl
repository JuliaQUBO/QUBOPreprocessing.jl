# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

@testset "certified pair relations, GLK cross-endpoint rule and reversible contractions" begin
    function rel_fixture(labels, linear, quadratic; sense=:min, domain=:bool, scale=1.0, offset=0.0)
        n = length(labels)
        V = eltype(labels)
        vm = QT.VariableMap{V}(Dict{V,Int}(v => i for (i, v) in enumerate(labels)), collect(labels))
        f = QT.Form{Float64}(
            n,
            QT.DenseLinearForm{Float64}(Float64.(linear)),
            QT.DenseQuadraticForm{Float64}(UpperTriangular(Float64.(quadratic))),
            Float64(scale),
            Float64(offset);
            sense=sense,
            domain=domain,
        )
        return QT.Model{V,Float64,Int}(vm, f)
    end

    function all_states(n::Int, dom::Symbol)
        low = dom === :bool ? 0 : -1
        states = Vector{Vector{Int}}(undef, 1 << n)
        for mask in 0:((1 << n) - 1)
            s = Vector{Int}(undef, n)
            for i in 1:n
                s[i] = ((mask >> (i - 1)) & 1) == 1 ? 1 : low
            end
            states[mask + 1] = s
        end
        return states
    end

    function optimal_value_and_states(model, dom::Symbol, sense::Symbol)
        n = QT.dimension(model)
        f = QT.form(model)
        states = all_states(n, dom)
        vals = [QT.value(s, f) for s in states]
        best = sense === :min ? minimum(vals) : maximum(vals)
        opt_states = [states[i] for i in eachindex(states) if vals[i] == best]
        return best, opt_states
    end

    @testset "Glover-Lewis-Kochenberger (:glk_pair) certifies relations without unary dominance or single-endpoint Rule 1" begin
        # Spin triangle [:u, :v, :w] where neither :u, :v, nor :w is unary-dominant,
        # and neither :u nor :v alone satisfies single-endpoint Rule 1 (-σ J_uv - |h| - R = 3 - 2 - 2 = -1 < 0),
        # but GLK cross-endpoint pair rule certifies s_u = σ s_v with strict margin +3 > 0.
        for σ_target in (1, -1), sense in (:min, :max), scale in (1.0, -2.0), dom in (:spin, :bool)
            eff_dir = (sense === :min ? 1 : -1) * (scale > 0 ? 1 : -1)
            # Desired normalized spin coefficients:
            # h_u = 2, h_v = 2 * σ_target, h_w = 0
            # J_uv = -3 * σ_target, J_uw = 2, J_vw = 2
            h_spin = [2.0 * eff_dir, 2.0 * σ_target * eff_dir, 0.0]
            J_spin = [
                0.0 (-3.0 * σ_target * eff_dir) (2.0 * eff_dir);
                0.0 0.0 (2.0 * eff_dir);
                0.0 0.0 0.0
            ]
            lin, quad, off = if dom === :spin
                h_spin, J_spin, 1.5
            else
                # s_i = 2 x_i - 1 => E(s) = sum h_i (2 x_i - 1) + sum J_ij (4 x_i x_j - 2 x_i - 2 x_j + 1)
                l_b = zeros(Float64, 3)
                q_b = zeros(Float64, 3, 3)
                c_b = 1.5 - sum(h_spin)
                for i in 1:3
                    l_b[i] += 2.0 * h_spin[i]
                end
                for i in 1:3, j in (i + 1):3
                    q_b[i, j] = 4.0 * J_spin[i, j]
                    l_b[i] -= 2.0 * J_spin[i, j]
                    l_b[j] -= 2.0 * J_spin[i, j]
                    c_b += J_spin[i, j]
                end
                l_b, q_b, c_b
            end
            model = rel_fixture([:u, :v, :w], lin, quad; sense=sense, domain=dom, scale=scale, offset=off)
            ws = Workspace(model; rules=:relations)

            # 1. No variable has derivative-bound unary dominance:
            for lbl in (:u, :v, :w)
                @test prove_dominance(ws, lbl; allow_weak=false).stop_reason === :not_strict
            end

            # 2. Prove relation via :glk_pair (and verify wrong sign is rejected):
            @test prove_relation(ws, :u, :v; sign=-σ_target, allow_weak=true).stop_reason === :not_strict
            @test contract_relation!(ws, :u, :v; sign=-σ_target, allow_weak=true).stop_reason === :not_strict
            att = prove_relation(ws, :u, :v)
            @test att.stop_reason === :proved
            @test att.method === :glk_pair
            step = only(att.certificate.steps)
            @test step isa RelationStep
            @test step.method === :glk_pair
            @test step.sign == σ_target
            @test step.orig_sign == σ_target
            @test step.lower == 3 // 1
            @test step.upper == 3 // 1
            @test persistency(step) === :strong
            @test verify_certificate(ws, att.certificate).valid

            # 3. Also test under nontrivial DomainGaugeMaps (including gauge[v] == -1 which swaps GLK branches A and B):
            for target_d in (:spin, :bool), g in ([-1, 1, 1], [1, -1, 1], [-1, -1, 1])
                gmap = domain_map(ws; domain=target_d, gauge=g)
                att_m = prove_relation(ws, :u, :v; map=gmap)
                @test att_m.stop_reason === :proved
                @test att_m.method === :glk_pair
                sm = only(att_m.certificate.steps)
                @test sm.sign == g[1] * g[2] * σ_target
                @test sm.orig_sign == σ_target
                @test sm.lower == 3 // 1 && sm.upper == 3 // 1
                @test verify_certificate(ws, att_m.certificate).valid
                @test verify_certificate(ws, att_m.certificate; map=gmap).valid

                t_cert = transport_certificate(ws, att.certificate, gmap)
                @test verify_certificate(ws, t_cert; map=gmap).valid
            end

            # 4. Contract via contract_relations! and verify against brute-force enumeration:
            cp0 = checkpoint(ws)
            rep = contract_relations!(ws)
            @test rep.stop_reason === :quiescent
            @test rep.deductions >= 1
            ru = relation_map(ws, :u)
            rv = relation_map(ws, :v)
            @test ru.first == rv.first && ru.second == σ_target * rv.second
            mat = materialize(ws)
            @test verify_certificate(ws, mat.certificate.proof).valid
            red_model = export_model(mat)
            red_form = QT.form(red_model)
            orig_opt, orig_opt_states = optimal_value_and_states(model, dom, sense)
            # Every original optimal state satisfies the certified relation:
            for s in orig_opt_states
                su = dom === :bool ? (2 * s[1] - 1) : s[1]
                sv = dom === :bool ? (2 * s[2] - 1) : s[2]
                @test su == σ_target * sv
            end
            # Every residual state lifts with exact energy equality, and optimal residual state lifts to original optimum:
            rem_dim = QT.dimension(red_model)
            for y in all_states(rem_dim, dom)
                rec = reconstruct(mat, y)
                @test rec.energy.value ≈ QT.value(y, red_form) atol = 1e-12
            end
            red_opt, red_opt_states = optimal_value_and_states(red_model, dom, sense)
            @test red_opt ≈ orig_opt atol = 1e-12
            for y in red_opt_states
                rec = reconstruct(mat, y)
                @test rec.energy.value ≈ orig_opt atol = 1e-12
                @test rec.state in orig_opt_states
            end

            # 5. Rollback restores exact initial state and relation_map:
            rollback!(ws, cp0)
            @test relation_map(ws) == [:u => 1, :v => 1, :w => 1]
            @test degree(ws, :u) == 2 && degree(ws, :v) == 2 && degree(ws, :w) == 2
        end
    end

    @testset "transitive signed contractions, relation_map without path compression, and parallel-edge cancellation" begin
        # 4-variable chain/cycle where:
        # :x1 == -:x2, :x2 == -:x3, and :x1, :x2 both couple to :x4 such that contracting :x1 -> :x2 -> :x3
        # merges and then cancels the edge to :x4!
        # Spin model:
        # J_{12} = +10 (forces s_1 = -s_2), J_{14} = +2
        # J_{23} = +20 (forces s_2 = -s_3), J_{24} = +2
        # When s_1 = -s_2 is contracted into s_2:
        # J'_{24} = J_{24} + (-1) * J_{14} = 2 - 2 = 0 (exact cancellation of edge (2, 4)!)
        model = rel_fixture(
            [:x1, :x2, :x3, :x4],
            [0.0, 0.0, 1.0, -2.0],
            [
                0.0 10.0 0.0 2.0;
                0.0 0.0 20.0 2.0;
                0.0 0.0 0.0 -5.0;
                0.0 0.0 0.0 0.0
            ];
            domain=:spin,
        )
        ws = Workspace(model; rules=:relations)
        cp_root = checkpoint(ws)

        @test relation_map(ws) == [:x1 => 1, :x2 => 1, :x3 => 1, :x4 => 1]
        @test degree(ws, :x2) == 3
        @test degree(ws, :x4) == 3

        # Step 1: contract :x1 -> :x2 with sign = -1
        r1 = contract_relation!(ws, :x1, :x2)
        @test r1.stop_reason === :applied
        cp_after_1 = checkpoint(ws)
        # Edge (:x2, :x4) cancelled to 0!
        @test degree(ws, :x2) == 1
        @test degree(ws, :x4) == 1
        @test isempty( filter(p -> p.first == :x4, incident_couplings(ws, :x2)) )
        @test relation_map(ws, :x1) == (:x2 => -1)
        @test relation_map(ws, :x2) == (:x2 => 1)

        # Step 2: contract :x2 -> :x3 with sign = -1 (transitively :x1 == +:x3)
        r2 = contract_relation!(ws, :x2, :x3)
        @test r2.stop_reason === :applied
        @test relation_map(ws) == [:x3 => 1, :x3 => -1, :x3 => 1, :x4 => 1]
        @test relation_map(ws, :x1) == (:x3 => 1)
        @test relation_map(ws, :x2) == (:x3 => -1)

        # Check relation_map with DomainGaugeMap:
        gmap = domain_map(ws; domain=:bool, gauge=[-1, 1, 1, -1])
        @test relation_map(ws; map=gmap) == [:x3 => -1, :x3 => -1, :x3 => 1, :x4 => 1]
        @test relation_map(ws, :x1; map=gmap) == (:x3 => -1)

        # Rollback to cp_after_1: because relation_map did not path-compress :x1 -> :x3,
        # :x1's representative is still :x2 => -1!
        rollback!(ws, cp_after_1)
        @test relation_map(ws) == [:x2 => -1, :x2 => 1, :x3 => 1, :x4 => 1]
        @test degree(ws, :x2) == 1 && degree(ws, :x4) == 1

        # Rollback to cp_root: cancelled edge (:x2, :x4) is restored!
        rollback!(ws, cp_root)
        @test relation_map(ws) == [:x1 => 1, :x2 => 1, :x3 => 1, :x4 => 1]
        @test degree(ws, :x2) == 3 && degree(ws, :x4) == 3
        @test Dict(incident_couplings(ws, :x2))[:x4] == 2 // 1

        # Now run automatic queue-driven preprocess(model; rules=:relations, cascade_dominance=true):
        ws_auto, rep_auto = preprocess(model; rules=:relations, cascade_dominance=true)
        @test rep_auto.stop_reason === :quiescent
        @test rep_auto.deductions == 4
        mat_auto = materialize(ws_auto)
        @test verify_certificate(ws_auto, mat_auto.certificate.proof).valid
        @test QT.dimension(export_model(mat_auto)) == 0
        rec_auto = reconstruct(mat_auto, Int[])
        orig_opt, orig_states = optimal_value_and_states(model, :spin, :min)
        @test rec_auto.energy.value ≈ orig_opt atol = 1e-12
        @test rec_auto.state in orig_states
    end

    @testset "max_fill guard, reverse-direction fallback, cascade_dominance and resumable budgets" begin
        # Hub :h connected to :a, :b, :c, and :l strongly coupled to :h and :d.
        # (:a, :b, :c) have fields and couplings so none of them is unary-dominant or pair-contractible,
        # and :d also has a neighbor :e so :d and :e are not pair-contractible.
        # :h has degree 4 (:l, :a, :b, :c), while :l has degree 2 (:h, :d) where :d is not adjacent to :h.
        # Contracting :h -> :l has fill 3 (:a, :b, :c not adjacent to :l).
        # Contracting :l -> :h has fill 1 (:d not adjacent to :h).
        # Under GLK (:glk_pair), the relation between :h and :l holds symmetrically:
        # h_h = 3, h_l = 3, J_hl = -6, J_ha = 1, J_hb = 1, J_hc = 1 (R_h = 3), J_ld = 5 (R_l = 5).
        # Check Rule 1 on :h: 6 - 3 - 3 = 0 (not strict!).
        # Check Rule 1 on :l: 6 - 3 - 5 = -2 < 0 (fails!).
        # Check GLK on (:h, :l) with σ = +1:
        # m_h(V_2) = 6 + 3 - 3 = 6 > 0, m_l(V_1) = 6 + 3 - 5 = 4 > 0 => lo_glk = 4 > 0!
        labels = [:h, :l, :a, :b, :c, :d, :e, :f]
        lin = [3.0, 3.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
        quad = [
            0.0 -6.0 1.0 1.0 1.0 0.0 0.0 0.0;
            0.0  0.0 0.0 0.0 0.0 5.0 0.0 0.0;
            0.0  0.0 0.0 2.0 2.0 0.0 0.0 0.0;
            0.0  0.0 0.0 0.0 2.0 0.0 0.0 0.0;
            0.0  0.0 0.0 0.0 0.0 0.0 0.0 0.0;
            0.0  0.0 0.0 0.0 0.0 0.0 5.0 5.0;
            0.0  0.0 0.0 0.0 0.0 0.0 0.0 5.0;
            0.0  0.0 0.0 0.0 0.0 0.0 0.0 0.0
        ]
        model = rel_fixture(labels, lin, quad; domain=:spin)

        # 1. With max_fill=0, neither :h -> :l (fill 3) nor :l -> :h (fill 1) is allowed:
        ws0 = Workspace(model; rules=:relations)
        rep0 = contract_relations!(ws0; max_fill=0)
        @test rep0.stop_reason === :quiescent
        @test rep0.deductions == 0
        @test rep0.pending == 0

        # 2. Progressive max_fill increase on the SAME workspace ws0:
        #    First check that max_work=0 and expired deadline_ns do NOT mutate trail or drop deferred vertices:
        cp_after_0 = checkpoint(ws0)
        rep_w0 = contract_relations!(ws0; max_fill=1, max_work=0)
        @test rep_w0.stop_reason === :work_limit && rep_w0.candidates == 0 && rep_w0.pending == 8
        @test checkpoint(ws0) == cp_after_0
        rep_dl = contract_relations!(ws0; max_fill=1, deadline_ns=UInt64(1))
        @test rep_dl.stop_reason === :deadline && rep_dl.candidates == 0 && rep_dl.pending == 8
        @test checkpoint(ws0) == cp_after_0
        #    Now run max_fill=1 on ws0: re-queues deferred vertices and contracts :l -> :h!
        rep_prog = contract_relations!(ws0; max_fill=1, max_deductions=1)
        @test rep_prog.stop_reason === :deduction_limit
        @test rep_prog.deductions == 1
        @test relation_map(ws0, :l) == (:h => 1)
        @test verify_certificate(ws0, export_certificate(ws0)).valid
        #    Rollback to cp_after_0 undoes both the contraction and the deferred re-queue,
        #    and calling contract_relations!(ws0; max_fill=1) again succeeds identically!
        rollback!(ws0, cp_after_0)
        @test relation_map(ws0, :l) == (:l => 1)
        @test contract_relations!(ws0; max_fill=0).deductions == 0
        rep_prog2 = contract_relations!(ws0; max_fill=1, max_deductions=1)
        @test rep_prog2.deductions == 1 && relation_map(ws0, :l) == (:h => 1)
        rollback!(ws0, cp_after_0)

        #    Also test duplicate entries in rel_queue[1:(rel_head - 1)] (vertex popped, dirtied/requeued, popped again):
        cp_dup = checkpoint(ws0)
        assume!(ws0, :a, 1) # dirties and re-queues :h, :b, :c
        @test contract_relations!(ws0; max_fill=0).deductions == 0 # pops :h, :b, :c a second time with blocked_fill=1
        @test contract_relations!(ws0; max_fill=1, max_work=0).pending == 7 # deduplicates :h, :b, :c in _count_deferred_rel
        @test contract_relations!(ws0; max_fill=1, max_deductions=1).deductions == 1
        rollback!(ws0, cp_dup)

        # 2b. Fresh workspace with max_fill=1: when :h is popped first from rel_queue, :h -> :l is skipped (fill 3 > 1),
        #     and Pass 2 contracts :l -> :h (fill 1 <= 1)!
        ws1 = Workspace(model; rules=:relations)
        rep1 = contract_relations!(ws1; max_fill=1, max_deductions=1)
        @test rep1.stop_reason === :deduction_limit
        @test rep1.deductions == 1
        @test relation_map(ws1, :l) == (:h => 1)
        @test verify_certificate(ws1, export_certificate(ws1)).valid

        # 3. Budget and deadline interruptions preserve a resumable queue:
        ws_b = Workspace(model; rules=:relations)
        @test contract_relations!(ws_b; max_work=0).stop_reason === :work_limit
        @test isempty(reductions(ws_b))
        @test contract_relations!(ws_b; deadline_ns=UInt64(1)).stop_reason === :deadline
        @test isempty(reductions(ws_b))
        # Tight max_work / max_exact_work during witness and application (both Pass 1 and max_fill Pass 2):
        @test contract_relations!(ws_b; max_work=3).stop_reason === :work_limit
        @test contract_relations!(ws_b; max_exact_work=2).stop_reason === :verification_limit
        @test contract_relations!(Workspace(model; rules=:relations); max_fill=1, max_exact_work=29).stop_reason === :verification_limit
        # Enough exact work for witness (1 + 4 + 1 + 2 = 8), but not enough for apply (1 + 3*4 = 13):
        ws_apply_lim = Workspace(model; rules=:relations)
        @test contract_relations!(ws_apply_lim; max_exact_work=9).stop_reason === :verification_limit
        @test isempty(reductions(ws_apply_lim))
        ws_work_lim = Workspace(model; rules=:relations)
        # Witness uses 2*4 + 2 = 10 visits + 1 candidate = 11; apply needs 4 + 2*3 = 10 more visits:
        @test contract_relations!(ws_work_lim; max_work=12).stop_reason === :work_limit
        @test isempty(reductions(ws_work_lim))
        # Resuming with full budget completes cleanly:
        rep_resume = contract_relations!(ws_work_lim)
        @test rep_resume.stop_reason === :quiescent
        @test rep_resume.deductions >= 1
        @test verify_certificate(ws_work_lim, export_certificate(ws_work_lim)).valid

        # 4. Validation errors on invalid arguments:
        @test_throws ArgumentError contract_relations!(ws0; max_fill=-1)
        @test_throws ArgumentError contract_relations!(ws0; max_fill=true)
        ws_id = Workspace(model; rules=:identity)
        @test_throws ArgumentError contract_relations!(ws_id; cascade_dominance=true)
    end

    @testset "exploratory branch-and-bound: assume! + contract_relations! + rollback! scaling" begin
        function chain_with_pair_gadget(n::Int)
            labels = [Symbol(:v, i) for i in 1:n]
            # Gadget on v1, v2, v3, v4:
            # At the root, h_2 = +3, h_3 = -5 have opposite signs and J_{12} = +5, J_{13} = -3, J_{14} = +6,
            # so every edge fails single-endpoint Rule 1, :glk_pair, and :coflip_pair (0 contractions at root).
            # When v1 is fixed to -1, edges (v1, v2) and (v1, v3) shift fields to h'_2 = -2 and h'_3 = -2,
            # unlocking GLK Rule 2 (:glk_pair) and :coflip_pair on (v2, v3) with margin +3 > 0!
            I_idx = [1, 1, 1, 2, 2, 3, 4]
            J_idx = [2, 3, 4, 3, 4, 4, n]
            V_val = [5.0, -3.0, 6.0, -5.0, 4.0, 4.0, 9.0]
            for k in 4:(n - 1)
                push!(I_idx, k)
                push!(J_idx, k + 1)
                push!(V_val, 9.0)
            end
            vm = QT.VariableMap{Symbol}(Dict{Symbol,Int}(v => i for (i, v) in enumerate(labels)), labels)
            lin_s = spzeros(Float64, n)
            lin_s[2] = 3.0
            lin_s[3] = -5.0
            f = QT.Form{Float64}(
                n,
                QT.SparseLinearForm{Float64}(lin_s),
                QT.SparseQuadraticForm{Float64}(sparse(I_idx, J_idx, V_val, n, n)),
                1.0,
                0.0;
                sense=:min,
                domain=:spin,
            )
            return QT.Model{Symbol,Float64,Int}(vm, f)
        end

        ws_small = Workspace(chain_with_pair_gadget(10); rules=:relations)
        ws_large = Workspace(chain_with_pair_gadget(2000); rules=:relations)
        # Drain initial quiescent relation queue once:
        @test contract_relations!(ws_small).deductions == 0
        @test contract_relations!(ws_large).deductions == 0

        function branch_cycle!(ws::Workspace)
            cp = checkpoint(ws)
            assume!(ws, :v1, -1)
            rep = contract_relations!(ws)
            rel = relation_map(ws, :v2)
            rollback!(ws, cp)
            return rep.deductions, rep.candidates, rep.edge_visits, rel
        end

        d_s, c_s, e_s, r_s = branch_cycle!(ws_small)
        d_l, c_l, e_l, r_l = branch_cycle!(ws_large)
        @test d_s == 2 && d_l == 2
        @test c_s == c_l && e_s == e_l
        @test r_s == (:v4 => -1) && r_l == (:v4 => -1)
        @test relation_map(ws_small, :v2) == (:v2 => 1)
        @test relation_map(ws_large, :v2) == (:v2 => 1)

        bytes_s = @allocated branch_cycle!(ws_small)
        bytes_l = @allocated branch_cycle!(ws_large)
        @test bytes_l <= bytes_s + 2048
    end

    @testset "verifier rejects tampered :glk_pair RelationStep certificates" begin
        model = rel_fixture(
            [:u, :v, :w],
            [2.0, 2.0, 0.0],
            [0.0 -3.0 2.0; 0.0 0.0 2.0; 0.0 0.0 0.0];
            domain=:spin,
        )
        ws = Workspace(model; rules=:relations)
        att = prove_relation(ws, :u, :v)
        @test att.stop_reason === :proved && att.method === :glk_pair
        rs = only(att.certificate.steps)
        @test verify_certificate(ws, att.certificate).valid

        # Tampered bounds on :glk_pair step:
        bad_bounds = RelationStep(rs.eliminated, rs.representative, rs.sign, rs.orig_sign,
                                  rs.lower + 1, rs.upper, rs.constant, 0, :glk_pair, 0, :strong)
        vr1 = verify_certificate(ws, DominanceCertificate(generation(ws), checkpoint(ws), (), (bad_bounds,), ws._snapshot))
        @test !vr1.valid && vr1.stop_reason === :invalid_bound

        # Forged :glk_pair step when h_u == 0:
        ws_zero_h = Workspace(rel_fixture([:u, :v], [0.0, 0.0], [0.0 -3.0; 0.0 0.0]; domain=:spin))
        forged_glk = RelationStep(1, 2, 1, 1, 3 // 1, 3 // 1, 0 // 1, 0, :glk_pair, 0, :strong)
        vr2 = verify_certificate(ws_zero_h, DominanceCertificate(generation(ws_zero_h), checkpoint(ws_zero_h), (), (forged_glk,), ws_zero_h._snapshot))
        @test !vr2.valid && vr2.stop_reason === :invalid_bound

        # Wrong-sign :glk_pair when endpoints have strong unary fields (center_exact < 0):
        # Here J_uv = +1 (anti-ferromagnetic, favors s_u = -s_v), while h_u = -10, h_v = -10
        # independently push s_u = +1 and s_v = +1. Requesting sign=+1 has center = -1 < 0 and MUST be refused!
        ws_unary_pair = Workspace(rel_fixture([:u, :v], [-10.0, -10.0], [0.0 1.0; 0.0 0.0]; domain=:spin))
        @test prove_relation(ws_unary_pair, :u, :v; sign=1, allow_weak=true).stop_reason === :not_strict
        @test contract_relation!(ws_unary_pair, :u, :v; sign=1, allow_weak=true).stop_reason === :not_strict
        forged_neg_center = RelationStep(1, 2, 1, 1, 9 // 1, 9 // 1, 0 // 1, 0, :glk_pair, 0, :strong)
        vr3 = verify_certificate(ws_unary_pair, DominanceCertificate(generation(ws_unary_pair), checkpoint(ws_unary_pair), (), (forged_neg_center,), ws_unary_pair._snapshot))
        @test !vr3.valid && vr3.stop_reason === :invalid_bound
    end

    @testset "GLK equality ties, allow_weak transition, non-zero parallel-edge merge, disconnected components and unfix!" begin
        # 1. GLK equality tie (lo_glk == 0) with frustrated second neighbor :z so L_coflip < 0:
        # h_u = 3, h_v = 3, h_w = 2, h_z = 2, J_uv = -4, J_uw = 3, J_vw = 3, J_uz = 4, J_vz = -4 =>
        # center = 4, R_u = R_v = 7, m_u(V_2) = 4 + 3 - 7 = 0, m_v(V_1) = 4 + 3 - 7 = 0, rad_coflip = (0 + 0 + 8)/2 = 4!
        m_tie = rel_fixture(
            [:u, :v, :w, :z],
            [3.0, 3.0, 2.0, 2.0],
            [0.0 -4.0 3.0 4.0; 0.0 0.0 3.0 -4.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0];
            domain=:spin,
        )
        ws_tie = Workspace(m_tie; rules=:relations)
        @test prove_relation(ws_tie, :u, :v; allow_weak=false).stop_reason === :not_strict
        att_weak = prove_relation(ws_tie, :u, :v; allow_weak=true)
        @test att_weak.stop_reason === :proved && att_weak.method === :glk_pair
        @test persistency(only(att_weak.certificate.steps)) === :weak
        @test verify_certificate(ws_tie, att_weak.certificate).valid
        # Progressive allow_weak=false -> allow_weak=true on the same workspace:
        @test contract_relations!(ws_tie; allow_weak=false).deductions == 0
        rep_w = contract_relations!(ws_tie; allow_weak=true, max_deductions=1)
        @test rep_w.deductions == 1
        @test relation_map(ws_tie, :u) == (:v => 1)
        # Non-zero parallel-edge merge: J'_{vw} = J_{vw} + (+1)*J_{uw} = 3 + 3 = 6 != 0!
        @test Dict(incident_couplings(ws_tie, :v))[:w] == 6 // 1

        # 2. Disconnected components and LIFO + non-LIFO unfix! restoration:
        # Component 1: [:a1, :a2, :a3], Component 2: [:b1, :b2]
        m_disc = rel_fixture(
            [:a1, :a2, :a3, :b1, :b2],
            [0.0, -6.0, 8.0, 0.0, 0.0],
            [
                0.0 7.0 -7.0  0.0 0.0;
                0.0 0.0 -4.0  0.0 0.0;
                0.0 0.0  0.0  0.0 0.0;
                0.0 0.0  0.0  0.0 4.0;
                0.0 0.0  0.0  0.0 0.0
            ];
            domain=:spin,
        )
        ws_disc = Workspace(m_disc; rules=:relations)
        # Initially :b1 == -:b2 contracts in Component 2, while Component 1 has |J| <= R:
        @test contract_relations!(ws_disc).deductions == 1
        @test relation_map(ws_disc, :b1) == (:b2 => -1)
        @test relation_map(ws_disc, :a2) == (:a2 => 1)

        # Now assume :a1 = 1 and :b2 = 1, then contract :a2 -> :a3:
        @test assume!(ws_disc, :a1, 1).stop_reason === :applied
        @test assume!(ws_disc, :b2, 1).stop_reason === :applied
        @test contract_relations!(ws_disc).deductions == 1
        @test relation_map(ws_disc, :a2) == (:a3 => 1)

        # LIFO unfix! of :b2 rolls back locally (undoing later deduction :a2 -> :a3 and :b2 assumption):
        @test unfix!(ws_disc, :b2).stop_reason === :applied
        @test assumptions(ws_disc) == [:a1 => 1]
        @test relation_map(ws_disc, :a2) == (:a2 => 1)

        # Re-apply :b2 = 1 and contract, then non-LIFO unfix! of :a1 rebuilds and replays only retained caller :b2 = 1:
        @test assume!(ws_disc, :b2, 1).stop_reason === :applied
        @test contract_relations!(ws_disc).deductions == 1
        @test relation_map(ws_disc, :a2) == (:a3 => 1)
        @test unfix!(ws_disc, :a1; max_work=0).stop_reason === :work_limit
        @test unfix!(ws_disc, :a1).stop_reason === :applied
        @test assumptions(ws_disc) == [:b2 => 1]
        @test relation_map(ws_disc) == [:a1 => 1, :a2 => 1, :a3 => 1, :b1 => 1, :b2 => 1]
        @test degree(ws_disc, :a2) == 2 && degree(ws_disc, :a3) == 2
    end

    @testset "shared-neighborhood co-flip pair dominance (:coflip_pair) and twin/clique contraction (#58)" begin
        function spin_to_bool_coeffs(h_spin, J_spin, c_spin)
            n = length(h_spin)
            l_b = zeros(Float64, n)
            q_b = zeros(Float64, n, n)
            c_b = Float64(c_spin) - sum(h_spin)
            for i in 1:n
                l_b[i] += 2.0 * h_spin[i]
            end
            for i in 1:n, j in (i + 1):n
                q_b[i, j] = 4.0 * J_spin[i, j]
                l_b[i] -= 2.0 * J_spin[i, j]
                l_b[j] -= 2.0 * J_spin[i, j]
                c_b += J_spin[i, j]
            end
            return l_b, q_b, c_b
        end

        function check_exhaustive_relation!(ws::Workspace, model, dom::Symbol, sense::Symbol; allow_weak::Bool=false)
            cp0 = checkpoint(ws)
            rep = contract_relations!(ws; allow_weak=allow_weak)
            @test rep.stop_reason === :quiescent
            @test rep.deductions >= 1
            mat = materialize(ws)
            @test verify_certificate(ws, mat.certificate.proof).valid
            red_model = export_model(mat)
            red_form = QT.form(red_model)
            orig_opt, orig_opt_states = optimal_value_and_states(model, dom, sense)
            rem_dim = QT.dimension(red_model)
            for y in all_states(rem_dim, dom)
                rec = reconstruct(mat, y)
                @test rec.energy.value ≈ QT.value(y, red_form) atol = 1e-12
            end
            red_opt, red_opt_states = optimal_value_and_states(red_model, dom, sense)
            @test red_opt ≈ orig_opt atol = 1e-12
            for y in red_opt_states
                rec = reconstruct(mat, y)
                @test rec.energy.value ≈ orig_opt atol = 1e-12
                @test rec.state in orig_opt_states
            end
            rollback!(ws, cp0)
        end

        # 1. Adjacent shared-neighborhood co-flip pair where both Rule 1 (:interval/:exact) and :glk_pair fail:
        # Zero fields (h = 0), J_uv = -3, shared neighbors w (J_uw = J_vw = 4) and z (J_uz = J_vz = -4).
        # Single-endpoint Rule 1 has center - R_u = 3 - 8 = -5 < 0; GLK has lo_glk = 3 - 0 - 8 = -5 < 0.
        # Under joint co-flip (:coflip_pair, sigma = +1), shared external couplings cancel:
        # rad_coflip = (|0 - 0| + |4 - 4| + |-4 - (-4)|) / 2 = 0, so L_coflip = 3 > 0 (:strong)!
        for sense in (:min, :max), scale in (1.5, -2.0)
            eff_dir = (sense === :min ? 1.0 : -1.0) * sign(scale)
            s_quad = eff_dir .* [
                0.0 -3.0  4.0 -4.0;
                0.0  0.0  4.0 -4.0;
                0.0  0.0  0.0  1.0;
                0.0  0.0  0.0  0.0
            ]
            s_lin = eff_dir .* [0.0, 0.0, 1.0, -1.0]
            m_spin = rel_fixture([:u, :v, :w, :z], s_lin, s_quad; sense=sense, domain=:spin, scale=scale, offset=1.25)
            ws_spin = Workspace(m_spin; rules=:relations)
            @test prove_dominance(ws_spin, :u).stop_reason === :not_strict
            @test prove_dominance(ws_spin, :v).stop_reason === :not_strict
            att = prove_relation(ws_spin, :u, :v)
            @test att.stop_reason === :proved && att.method === :coflip_pair
            step = only(att.certificate.steps)
            @test step isa RelationStep && step.method === :coflip_pair
            @test step.sign == 1 && step.orig_sign == 1
            @test persistency(step) === :strong
            @test step.lower == 3 // 1
            @test verify_certificate(ws_spin, att.certificate).valid
            check_exhaustive_relation!(ws_spin, m_spin, :spin, sense; allow_weak=false)

            # Equivalent Boolean model and gauge transport:
            b_lin, b_quad, b_off = spin_to_bool_coeffs(s_lin, s_quad, 1.25)
            m_bool = rel_fixture([:u, :v, :w, :z], b_lin, b_quad; sense=sense, domain=:bool, scale=scale, offset=b_off)
            ws_bool = Workspace(m_bool; rules=:relations)
            att_b = prove_relation(ws_bool, :u, :v)
            @test att_b.stop_reason === :proved && att_b.method === :coflip_pair
            @test only(att_b.certificate.steps).sign == 1
            @test verify_certificate(ws_bool, att_b.certificate).valid
            dmap = domain_map(ws_bool; domain=:spin, gauge=[-1, 1, -1, 1])
            att_map = prove_relation(ws_bool, :u, :v; map=dmap)
            @test att_map.stop_reason === :proved && att_map.method === :coflip_pair
            @test only(att_map.certificate.steps).sign == -1 # flipped because g_u * g_v = -1
            @test only(att_map.certificate.steps).orig_sign == 1
            @test verify_certificate(ws_bool, att_map.certificate).valid
            @test verify_certificate(ws_bool, att_map.certificate; map=dmap).valid
            t_cert = transport_certificate(ws_bool, att_b.certificate, dmap)
            @test verify_certificate(ws_bool, t_cert; map=dmap).valid
            check_exhaustive_relation!(ws_bool, m_bool, :bool, sense; allow_weak=false)
        end

        # 2. Opposite-sign fields where GLK penalizes both branches but :coflip_pair succeeds:
        # h_u = 2, h_v = -2, J_uv = -4, J_uw = 5, J_vw = 5, J_uz = -3, J_vz = -2 =>
        # rad_coflip(+1) = (|2 - (-2)| + |5 - 5| + |-3 - (-2)|) / 2 = 5/2 < 4 => L_coflip = 3/2 > 0!
        m_opp = rel_fixture(
            [:u, :v, :w, :z],
            [2.0, -2.0, 1.0, -1.0],
            [0.0 -4.0 5.0 -3.0; 0.0 0.0 5.0 -2.0; 0.0 0.0 0.0 1.0; 0.0 0.0 0.0 0.0];
            domain=:spin,
        )
        ws_opp = Workspace(m_opp; rules=:relations)
        att_opp = prove_relation(ws_opp, :u, :v)
        @test att_opp.stop_reason === :proved && att_opp.method === :coflip_pair
        @test only(att_opp.certificate.steps).lower == 3 // 2
        @test verify_certificate(ws_opp, att_opp.certificate).valid
        check_exhaustive_relation!(ws_opp, m_opp, :spin, :min; allow_weak=false)

        # 3. Weak :coflip_pair equality tie (L_coflip == 0 with center > 0):
        # h_u = 2, h_v = -2, J_uv = -2, J_uw = 5, J_vw = 5 => center = 2, rad_coflip = 4/2 = 2 => L_coflip = 0
        m_coflip_tie = rel_fixture(
            [:u, :v, :w],
            [2.0, -2.0, 1.0],
            [0.0 -2.0 5.0; 0.0 0.0 5.0; 0.0 0.0 0.0];
            domain=:spin,
        )
        ws_coflip_tie = Workspace(m_coflip_tie; rules=:relations)
        @test prove_relation(ws_coflip_tie, :u, :v; allow_weak=false).stop_reason === :not_strict
        att_coflip_w = prove_relation(ws_coflip_tie, :u, :v; allow_weak=true)
        @test att_coflip_w.stop_reason === :proved && att_coflip_w.method === :coflip_pair
        @test persistency(only(att_coflip_w.certificate.steps)) === :weak
        @test verify_certificate(ws_coflip_tie, att_coflip_w.certificate).valid
        check_exhaustive_relation!(ws_coflip_tie, m_coflip_tie, :spin, :min; allow_weak=true)

        # 4. Non-adjacent exact signed twin contraction (J_uv == 0, sigma in {+1, -1}):
        # Ferromagnetic non-adjacent twin (sigma = +1): J_uv = 0, h_u = h_v = 1, J_uw1 = J_vw1 = 3, J_uw2 = J_vw2 = -3
        m_twin_pos = rel_fixture(
            [:u, :v, :w1, :w2],
            [1.0, 1.0, 5.0, -5.0],
            [
                0.0 0.0  3.0 -3.0;
                0.0 0.0  3.0 -3.0;
                0.0 0.0  0.0  0.0;
                0.0 0.0  0.0  0.0
            ];
            domain=:spin,
        )
        ws_twin_pos = Workspace(m_twin_pos; rules=:relations)
        cp_twin_pos = checkpoint(ws_twin_pos)
        @test prove_relation(ws_twin_pos, :u, :v; allow_weak=false).stop_reason === :not_strict
        att_twin_pos = prove_relation(ws_twin_pos, :u, :v; allow_weak=true)
        @test att_twin_pos.stop_reason === :proved && att_twin_pos.method === :coflip_pair
        @test only(att_twin_pos.certificate.steps).sign == 1
        @test persistency(only(att_twin_pos.certificate.steps)) === :weak
        @test verify_certificate(ws_twin_pos, att_twin_pos.certificate).valid
        @test contract_relations!(ws_twin_pos; allow_weak=false).deductions == 0
        rep_twin_pos = contract_relations!(ws_twin_pos; allow_weak=true, max_deductions=1)
        @test rep_twin_pos.deductions == 1
        @test relation_map(ws_twin_pos, :u) == (:v => 1)
        @test verify_certificate(ws_twin_pos, export_certificate(ws_twin_pos)).valid
        rollback!(ws_twin_pos, cp_twin_pos)
        check_exhaustive_relation!(ws_twin_pos, m_twin_pos, :spin, :min; allow_weak=true)

        # Anti-ferromagnetic non-adjacent twin (sigma = -1): J_uv = 0, h_u = -h_v = 1, J_uw1 = -J_vw1 = 3, J_uw2 = -J_vw2 = -3
        m_twin_neg = rel_fixture(
            [:u, :v, :w1, :w2],
            [1.0, -1.0, 5.0, -5.0],
            [
                0.0 0.0  3.0 -3.0;
                0.0 0.0 -3.0  3.0;
                0.0 0.0  0.0  0.0;
                0.0 0.0  0.0  0.0
            ];
            domain=:spin,
        )
        ws_twin_neg = Workspace(m_twin_neg; rules=:relations)
        @test prove_relation(ws_twin_neg, :u, :v; allow_weak=false).stop_reason === :not_strict
        att_twin_neg = prove_relation(ws_twin_neg, :u, :v; allow_weak=true)
        @test att_twin_neg.stop_reason === :proved && att_twin_neg.method === :coflip_pair
        @test only(att_twin_neg.certificate.steps).sign == -1
        @test persistency(only(att_twin_neg.certificate.steps)) === :weak
        @test verify_certificate(ws_twin_neg, att_twin_neg.certificate).valid
        # Also test discovery via schedule_reductions!(ws; allow_weak_relations=true):
        ws_sched_twin = Workspace(m_twin_neg; rules=:mixed)
        srep = schedule_reductions!(ws_sched_twin; enable_dominance=false, enable_elimination=false, allow_weak_relations=true, max_fill=0)
        @test srep.relation_deductions >= 1 && srep.fill_edges == 0
        @test verify_certificate(ws_sched_twin, export_certificate(ws_sched_twin)).valid
        check_exhaustive_relation!(ws_twin_neg, m_twin_neg, :spin, :min; allow_weak=true)

        # 5. Uniform ferromagnetic clique K_4 contraction:
        # Every vertex has h_i = 1 and J_ij = -2 (so R_u = 4 > |J_uv| = 2; neither unary dominance nor Rule 1 nor GLK fires),
        # yet :coflip_pair contracts all 3 pairs down to 1 single representative with :strong persistency!
        m_clique = rel_fixture(
            [:c1, :c2, :c3, :c4],
            [1.0, 1.0, 1.0, 1.0],
            [
                0.0 -2.0 -2.0 -2.0;
                0.0  0.0 -2.0 -2.0;
                0.0  0.0  0.0 -2.0;
                0.0  0.0  0.0  0.0
            ];
            domain=:spin,
        )
        ws_clique = Workspace(m_clique; rules=:relations)
        cp_clique = checkpoint(ws_clique)
        rep_clique = contract_relations!(ws_clique; cascade_dominance=false)
        @test rep_clique.deductions == 3
        @test QT.dimension(export_model(materialize(ws_clique))) == 1
        @test certificate_guarantee(export_certificate(ws_clique)) === :optimum_preserving_restriction
        @test persistency(export_certificate(ws_clique)) === :strong
        @test verify_certificate(ws_clique, export_certificate(ws_clique)).valid
        rollback!(ws_clique, cp_clique)
        check_exhaustive_relation!(ws_clique, m_clique, :spin, :min; allow_weak=false)

        # 6. Verifier rejects tampered :coflip_pair RelationStep certificates:
        ws_tamper = Workspace(m_opp; rules=:relations)
        valid_coflip = only(prove_relation(ws_tamper, :u, :v).certificate.steps)
        # Forged tighter lower bound (lower = 2 // 1 > exact 3 // 2):
        forged_lo = RelationStep(
            valid_coflip.eliminated, valid_coflip.representative,
            valid_coflip.sign, valid_coflip.orig_sign,
            2 // 1, valid_coflip.upper, valid_coflip.constant,
            0, :coflip_pair, 0, :strong,
        )
        vr_lo = verify_certificate(ws_tamper, DominanceCertificate(generation(ws_tamper), checkpoint(ws_tamper), (), (forged_lo,), ws_tamper._snapshot))
        @test !vr_lo.valid && vr_lo.stop_reason === :invalid_bound

        # Forged :strong persistency on a :weak L_coflip == 0 tie:
        ws_tie_t = Workspace(m_coflip_tie; rules=:relations)
        weak_coflip = only(prove_relation(ws_tie_t, :u, :v; allow_weak=true).certificate.steps)
        forged_strong = RelationStep(
            weak_coflip.eliminated, weak_coflip.representative,
            weak_coflip.sign, weak_coflip.orig_sign,
            weak_coflip.lower, weak_coflip.upper, weak_coflip.constant,
            0, :coflip_pair, 0, :strong,
        )
        vr_strong = verify_certificate(ws_tie_t, DominanceCertificate(generation(ws_tie_t), checkpoint(ws_tie_t), (), (forged_strong,), ws_tie_t._snapshot))
        @test !vr_strong.valid && vr_strong.stop_reason === :invalid_bound

        # Forged :strong persistency on a non-adjacent twin (center == 0):
        ws_twin_t = Workspace(m_twin_pos; rules=:relations)
        twin_step = only(prove_relation(ws_twin_t, :u, :v; allow_weak=true).certificate.steps)
        forged_twin_strong = RelationStep(
            twin_step.eliminated, twin_step.representative,
            twin_step.sign, twin_step.orig_sign,
            twin_step.lower, twin_step.upper, twin_step.constant,
            0, :coflip_pair, 0, :strong,
        )
        vr_twin = verify_certificate(ws_twin_t, DominanceCertificate(generation(ws_twin_t), checkpoint(ws_twin_t), (), (forged_twin_strong,), ws_twin_t._snapshot))
        @test !vr_twin.valid && vr_twin.stop_reason === :invalid_bound

        # 7. allow_weak=true does not downgrade :strong persistency when :exact or :glk_pair ties at 0:
        # (a) :exact ties at 0 (center - R_u = 1 - 1 = 0) while :coflip_pair has lo_cf = 1//2 > 0:
        ws_up_exact = Workspace(rel_fixture(
            [:a, :b, :c], [0.0, 0.0, 0.0], [0.0 -1.0 1.0; 0.0 0.0 0.0; 0.0 0.0 0.0]; domain=:spin
        ); rules=:relations)
        att_up_ex = prove_relation(ws_up_exact, :a, :b; allow_weak=true)
        @test att_up_ex.stop_reason === :proved && att_up_ex.method === :coflip_pair
        @test persistency(only(att_up_ex.certificate.steps)) === :strong
        @test only(att_up_ex.certificate.steps).lower == 1 // 2
        # (b) :glk_pair ties at 0 (lo_glk = 4 + 3 - 7 = 0) while :coflip_pair has lo_cf = 4 > 0:
        ws_up_glk = Workspace(rel_fixture(
            [:u, :v, :w], [3.0, 3.0, 2.0], [0.0 -4.0 7.0; 0.0 0.0 7.0; 0.0 0.0 0.0]; domain=:spin
        ); rules=:relations)
        att_up_glk = prove_relation(ws_up_glk, :u, :v; allow_weak=true)
        @test att_up_glk.stop_reason === :proved && att_up_glk.method === :coflip_pair
        @test persistency(only(att_up_glk.certificate.steps)) === :strong
        @test only(att_up_glk.certificate.steps).lower == 4 // 1
    end

    @testset "2-SAT pair equivalences from double probing (:probing_pair) and roof SCCs (:roof_scc_pair) (#60)" begin
        # 1. Two-branch probing pair equivalence (:probing_pair) on a pair (u, v) where
        # single-endpoint, :glk_pair, and :coflip_pair all fail on (u, v) directly,
        # but 2-round trial dominance from v cascades through mediator m to force s_u = +s_v:
        # Variables [:u, :v, :m, :z1, :z2, :z3], zero fields:
        # J_{u,v} = -0.5, J_{u,m} = -3.0, J_{u,z1} = 2.0 (so on (u, v), |J_{u,v}| = 0.5 < R_u^{other} = 5.0),
        # J_{v,m} = -6.0, J_{v,z2} = 4.0, J_{v,z3} = 4.0, J_{z2,z3} = 4.0 (so R_v^{other} = 14.0),
        # and R_coflip(u, v) = 0.5 * (|-3 - (-6)| + 2 + 4 + 4) = 6.5 > 0.5 (so :coflip_pair fails on (u, v)).
        # Yet conditioning v = ±1 forces m = ±1 (|-6| = 6 > |J_{u,m}| = 3), which then forces u = ±1
        # (|-3 - 0.5| = 3.5 > |J_{u,z1}| = 2.0)!
        Q_pp = zeros(6, 6)
        Q_pp[1, 2] = -0.5; Q_pp[1, 3] = -3.0; Q_pp[1, 4] = 2.0
        Q_pp[2, 3] = -6.0; Q_pp[2, 5] = 4.0; Q_pp[2, 6] = 4.0
        Q_pp[5, 6] = 4.0
        m_pp = rel_fixture([:u, :v, :m, :z1, :z2, :z3], zeros(6), Q_pp; domain=:spin, sense=:min)
        ws_pp = Workspace(m_pp; rules=:relations)
        @test prove_relation(ws_pp, :u, :v; allow_weak=true).stop_reason === :not_strict
        @test prove_relation(ws_pp, :v, :u; allow_weak=true).stop_reason === :not_strict

        function check_materialized_optima(ws::Workspace, model, dom::Symbol, sense::Symbol)
            mat = materialize(ws)
            @test verify_certificate(ws, mat.certificate.proof).valid
            red_model = export_model(mat)
            red_form = QT.form(red_model)
            orig_opt, orig_opt_states = optimal_value_and_states(model, dom, sense)
            rem_dim = QT.dimension(red_model)
            for y in all_states(rem_dim, dom)
                rec = reconstruct(mat, y)
                @test rec.energy.value ≈ QT.value(y, red_form) atol = 1e-12
            end
            red_opt, red_opt_states = optimal_value_and_states(red_model, dom, sense)
            @test red_opt ≈ orig_opt atol = 1e-12
            for y in red_opt_states
                rec = reconstruct(mat, y)
                @test rec.energy.value ≈ orig_opt atol = 1e-12
                @test rec.state in orig_opt_states
            end
        end

        att_pp = prove_relation(ws_pp, :u, :v; enable_probing=true, max_rounds=2)
        @test att_pp.stop_reason === :proved
        @test att_pp.method === :probing_pair
        s_pp = only(att_pp.certificate.steps)::RelationStep
        @test s_pp.sign == 1
        @test s_pp.method === :probing_pair
        @test persistency(s_pp) === :strong
        @test 0 < s_pp.lower <= 3 // 2 && s_pp.lower == s_pp.upper
        @test verify_certificate(ws_pp, att_pp.certificate).valid

        # DomainGaugeMap invariance and transport_certificate on :probing_pair:
        dmap_pp = domain_map(ws_pp; domain=:bool, gauge=[-1, 1, -1, 1, -1, 1])
        att_pp_m = prove_relation(ws_pp, :u, :v; enable_probing=true, max_rounds=2, map=dmap_pp)
        @test att_pp_m.stop_reason === :proved
        @test att_pp_m.method === :probing_pair
        s_pp_m = only(att_pp_m.certificate.steps)::RelationStep
        @test s_pp_m.sign == -1
        @test verify_certificate(ws_pp, att_pp_m.certificate; map=dmap_pp).valid
        tcert_pp = transport_certificate(ws_pp, att_pp.certificate, dmap_pp)
        @test verify_certificate(ws_pp, tcert_pp; map=dmap_pp).valid

        # contract_relation!(..., enable_probing=true) and exhaustive optimum preservation:
        upd_pp = contract_relation!(ws_pp, :u, :v; enable_probing=true, max_rounds=2)
        @test upd_pp.stop_reason === :applied && upd_pp.changed == 1
        @test verify_certificate(ws_pp, export_certificate(ws_pp)).valid
        check_materialized_optima(ws_pp, m_pp, :spin, :min)

        # Scope sensitivity: assume! rolls back marginal :probing_pair contractions
        ws_pp_sc = Workspace(m_pp; rules=:relations)
        @test contract_relation!(ws_pp_sc, :u, :v; enable_probing=true, max_rounds=2).stop_reason === :applied
        @test relation_map(ws_pp_sc, :u) == (:v => 1)
        assume!(ws_pp_sc, :z1, 1)
        @test relation_map(ws_pp_sc, :u) == (:u => 1)

        # Tampering rejection on :probing_pair RelationStep:
        ws_pp_t = Workspace(m_pp; rules=:relations)
        s_pp_t = only(prove_relation(ws_pp_t, :u, :v; enable_probing=true, max_rounds=2).certificate.steps)::RelationStep
        bad_pp_bound = RelationStep(
            s_pp_t.eliminated, s_pp_t.representative, s_pp_t.sign, s_pp_t.orig_sign,
            2 // 1, 2 // 1, s_pp_t.constant, 0, :probing_pair, 0, :strong, s_pp_t.witness,
        )
        @test verify_certificate(
            ws_pp_t,
            DominanceCertificate(generation(ws_pp_t), checkpoint(ws_pp_t), (), (bad_pp_bound,), ws_pp_t._snapshot),
        ).stop_reason === :invalid_bound

        # 2. contract_relations!(ws; enable_probing=true) and contract_relations!(ws; enable_roof_scc=true):
        ws_cr_prob = Workspace(m_pp; rules=:relations)
        rep_cr_prob = contract_relations!(ws_cr_prob; enable_probing=true, max_rounds=2)
        @test rep_cr_prob.stop_reason === :quiescent
        @test rep_cr_prob.deductions >= 2

        # Two-mediator fixture [:u, :v, :m1, :m2, :z1, :z2, :z3] where NO pair has a cheap 1-round
        # relation (m1 is only forced on v = -1, m2 is only forced on v = +1), so contract_relations!(ws)
        # finds 0 deductions without enable_probing=true, while enable_probing=true contracts :u => :v:
        Q_pp2 = zeros(7, 7)
        Q_pp2[1, 2] = -3.0; Q_pp2[1, 3] = -4.0; Q_pp2[1, 4] = -4.0; Q_pp2[1, 5] = 2.0
        Q_pp2[2, 3] = -5.0; Q_pp2[2, 4] = -5.0; Q_pp2[2, 6] = 10.0; Q_pp2[2, 7] = 10.0
        Q_pp2[5, 6] = 4.0;  Q_pp2[5, 7] = 4.0;  Q_pp2[6, 7] = 10.0
        m_pp2 = rel_fixture(
            [:u, :v, :m1, :m2, :z1, :z2, :z3],
            [0.0, 0.0, 5.0, -5.0, 0.0, 0.0, 0.0],
            Q_pp2;
            domain=:spin, sense=:min,
        )
        ws_pp2_cheap = Workspace(m_pp2; rules=:relations)
        @test contract_relations!(ws_pp2_cheap).deductions == 0
        ws_pp2_prob = Workspace(m_pp2; rules=:relations)
        rep_pp2_prob = contract_relations!(ws_pp2_prob; enable_probing=true, max_rounds=2)
        @test rep_pp2_prob.stop_reason === :quiescent
        @test rep_pp2_prob.deductions >= 1
        @test relation_map(ws_pp2_prob, :u) == (:v => 1)
        @test verify_certificate(ws_pp2_prob, export_certificate(ws_pp2_prob)).valid
        @test verify_certificate(ws_cr_prob, export_certificate(ws_cr_prob)).valid
        check_materialized_optima(ws_cr_prob, m_pp, :spin, :min)

        Q_k33_rel = zeros(6, 6)
        for u in 1:3, v in 4:6
            Q_k33_rel[u, v] = -2.0
        end
        m_k33_rel = rel_fixture([:a1, :a2, :a3, :b1, :b2, :b3], zeros(6), Q_k33_rel; domain=:spin, sense=:min)
        ws_cr_scc = Workspace(m_k33_rel; rules=:relations)
        @test contract_relations!(ws_cr_scc).deductions == 0
        rep_cr_scc = contract_relations!(ws_cr_scc; enable_roof_scc=true)
        @test rep_cr_scc.stop_reason === :quiescent
        @test rep_cr_scc.deductions == 5
        @test length(unique(first.(relation_map(ws_cr_scc)))) == 1
        @test verify_certificate(ws_cr_scc, export_certificate(ws_cr_scc)).valid
        check_materialized_optima(ws_cr_scc, m_k33_rel, :spin, :min)

        # 3. Budget atomicity, max_fill + max_deductions interaction, and upfront witness validation
        # in contract_relations!(ws; enable_roof_scc=true):
        ws_budget_102 = Workspace(m_k33_rel; rules=:relations)
        rep_b102 = contract_relations!(ws_budget_102; enable_roof_scc=true, max_work=102)
        @test rep_b102.stop_reason === :work_limit
        @test rep_b102.deductions == 0
        @test length(unique(first.(relation_map(ws_budget_102)))) == 6
        @test isempty(reductions(ws_budget_102))

        ws_budget_108 = Workspace(m_k33_rel; rules=:relations)
        rep_b108 = contract_relations!(ws_budget_108; enable_roof_scc=true, max_work=108)
        @test rep_b108.candidates + rep_b108.edge_visits <= 108
        @test isempty(reductions(ws_budget_108)) || verify_certificate(ws_budget_108, export_certificate(ws_budget_108)).valid

        # On K_{3,3} with labels [:b1, :a1, :a2, :a3, :b2, :b3], :b1 (index 1) is the SCC representative;
        # specs (:a1 -> :b1), (:a2 -> :b1), (:a3 -> :b1) have fill = 2 > 0, whereas (:b2 -> :b1) and (:b3 -> :b1)
        # have fill = 0! With max_fill=0 and max_deductions=2, the 3 fill-rejected specs do NOT consume max_deductions,
        # so (:b2 -> :b1) and (:b3 -> :b1) are both contracted (deductions == 2 rather than 0):
        Q_k33_ord = zeros(6, 6)
        for u in (2, 3, 4), v in (1, 5, 6)
            Q_k33_ord[min(u, v), max(u, v)] = -2.0
        end
        m_k33_ord = rel_fixture([:b1, :a1, :a2, :a3, :b2, :b3], zeros(6), Q_k33_ord; domain=:spin, sense=:min)
        ws_fill_ded = Workspace(m_k33_ord; rules=:relations)
        rep_fd0 = contract_relations!(ws_fill_ded; enable_roof_scc=true, max_fill=0, max_deductions=2)
        @test rep_fd0.stop_reason === :deduction_limit
        @test rep_fd0.deductions == 2
        @test verify_certificate(ws_fill_ded, export_certificate(ws_fill_ded)).valid
        rep_fd2 = contract_relations!(ws_fill_ded; enable_roof_scc=true, max_fill=9, max_deductions=2)
        @test rep_fd2.stop_reason === :deduction_limit
        @test rep_fd2.deductions == 2
        @test verify_certificate(ws_fill_ded, export_certificate(ws_fill_ded)).valid

        # Malformed witness rejected upfront at entry of prove_relation, contract_relation!, and contract_relations!:
        @test_throws ArgumentError prove_relation(ws_cr_scc, :a1, :a2; enable_roof_scc=true, witness=[1, 1])
        @test_throws ArgumentError contract_relation!(ws_cr_scc, :a1, :a2; enable_roof_scc=true, witness=[1, 1])
        @test_throws ArgumentError contract_relations!(Workspace(m_k33_rel; rules=:relations); enable_roof_scc=true, witness=[1, 1])

        # Anti-aligned (:probing_pair with sign = -1):
        Q_pp_neg = copy(Q_pp)
        Q_pp_neg[1, 2] = 0.5
        Q_pp_neg[1, 3] = 3.0
        m_pp_neg = rel_fixture([:u, :v, :m, :z1, :z2, :z3], zeros(6), Q_pp_neg; domain=:spin, sense=:min)
        ws_pp_neg = Workspace(m_pp_neg; rules=:relations)
        att_pp_neg = prove_relation(ws_pp_neg, :u, :v; sign=-1, enable_probing=true, max_rounds=2)
        @test att_pp_neg.stop_reason === :proved
        @test only(att_pp_neg.certificate.steps).sign == -1
        @test verify_certificate(ws_pp_neg, att_pp_neg.certificate).valid
    end
end

