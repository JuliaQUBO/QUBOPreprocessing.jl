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

            # 2. Prove relation via :glk_pair:
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

        # 2. With max_fill=1, when :h is popped first from rel_queue, :h -> :l is skipped (fill 3 > 1),
        #    and Pass 2 contracts :l -> :h (fill 1 <= 1)!
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
        @test contract_relations!(Workspace(model; rules=:relations); max_fill=1, max_exact_work=2).stop_reason === :verification_limit
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
            # Gadget on v1, v2, v3:
            # All linear fields are 0 at the root, and every edge has |J| <= R at both endpoints,
            # so 0 contractions apply at the root.
            # When v1 is fixed to -1, edges (v1, v2) and (v1, v3) become fields h'_2 = -2 and h'_3 = -2,
            # unlocking GLK Rule 2 (:glk_pair) on (v2, v3) with margin 5 + 2 - 4 = +3 > 0!
            I_idx = [1, 1, 2, 2, 3, 4]
            J_idx = [2, 3, 3, 4, 4, n]
            V_val = [2.0, 2.0, -5.0, 4.0, 4.0, 9.0]
            for k in 4:(n - 1)
                push!(I_idx, k)
                push!(J_idx, k + 1)
                push!(V_val, 9.0)
            end
            vm = QT.VariableMap{Symbol}(Dict{Symbol,Int}(v => i for (i, v) in enumerate(labels)), labels)
            f = QT.Form{Float64}(
                n,
                QT.SparseLinearForm{Float64}(spzeros(Float64, n)),
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
    end
end

