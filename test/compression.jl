using Test
using QUBOPreprocessing
import QUBOTools as QT

@testset "Coefficient compression and sparsification audit (#21)" begin
    cex = compression_counterexamples()

    @testset "1. Closed-endpoint linear tie counterexample (F(x) = x -> F'(x) = 0)" begin
        rep = cex.endpoint_tie.report
        @test rep.stop_reason === :audited
        @test rep.relation === :introduced_suboptimal_tie
        @test !rep.residual_to_original_valid
        @test !rep.constant_energy_shift
        @test rep.optimal_energy_shift === nothing
        @test rep.original_optimal_value == 0 // 1
        @test rep.transformed_optimal_value == 0 // 1
        @test rep.worst_lifted_original_value == 1 // 1
        @test rep.original_optima_count == 1
        @test rep.transformed_optima_count == 2
        @test rep.shared_optima_count == 1
        @test rep.introduced_suboptimal_witness == [1]
        @test rep.lost_optimum_witness === nothing
        @test rep.decision === :defer
        @test rep.missing_proof === :endpoint_introduces_suboptimal_ties
        @test length(rep.candidates) == 1
        c = rep.candidates[1]
        @test c.kind === :linear
        @test c.rule === :qubolite_linear_closed
        @test c.original_coeff == 1 // 1
        @test c.compressed_coeff == 0 // 1
        @test rep.metrics.initial_nnz_linear == 1
        @test rep.metrics.transformed_nnz_linear == 0
    end

    @testset "2. Closed-endpoint quadratic tie counterexample (Q12: 3 -> 1)" begin
        rep = cex.quadratic_endpoint_tie.report
        @test rep.stop_reason === :audited
        @test rep.relation === :introduced_suboptimal_tie
        @test !rep.residual_to_original_valid
        @test !rep.constant_energy_shift
        @test rep.original_optimal_value == -1 // 1
        @test rep.transformed_optimal_value == -1 // 1
        @test rep.worst_lifted_original_value == 1 // 1
        @test rep.original_optima_count == 2
        @test rep.transformed_optima_count == 3
        @test rep.shared_optima_count == 2
        @test rep.introduced_suboptimal_witness == [1, 1]
        @test rep.lost_optimum_witness === nothing
        @test rep.decision === :defer
        @test rep.missing_proof === :endpoint_introduces_suboptimal_ties
        @test rep.metrics.initial_dynamic_range == 3 // 1
        @test rep.metrics.transformed_dynamic_range == 1 // 1
    end

    @testset "3. Open-endpoint negative quadratic lost-optimum counterexample (disjoint optima)" begin
        rep = cex.negative_quadratic_lost_optimum.report
        @test rep.stop_reason === :audited
        @test rep.relation === :disjoint_optimum_sets
        @test !rep.residual_to_original_valid
        @test !rep.constant_energy_shift
        @test rep.original_optimal_value == -1 // 1
        @test rep.transformed_optimal_value == 0 // 1
        @test rep.worst_lifted_original_value == 0 // 1
        @test rep.original_optima_count == 1
        @test rep.transformed_optima_count == 1
        @test rep.shared_optima_count == 0
        @test rep.introduced_suboptimal_witness == [0, 0]
        @test rep.lost_optimum_witness == [1, 1]
        @test rep.valid_lower_bound_shift == -29 // 10
        @test rep.decision === :defer
        @test rep.missing_proof === :lost_all_original_optima
    end

    @testset "4. Strict interior compression is subsumed by #14 exact unary dominance elimination" begin
        m_sub = cex.strict_interior_subsumed.model
        rep = cex.strict_interior_subsumed.report
        @test rep.stop_reason === :audited
        @test rep.relation === :exact_optimum_set
        @test rep.residual_to_original_valid
        @test !rep.constant_energy_shift
        @test rep.optimal_energy_shift == -1 // 2
        @test rep.subsumed_by_dominance
        @test rep.subsuming_rule === :unary_dominance
        @test rep.decision === :adopt_via_exact_elimination
        @test rep.missing_proof === :subsumed_by_exact_unary_elimination
        # Open-interval compression reduces L1 from 5 to 3/2, L2 from -1 to -1/2, and zeroes Q13 = 2 -> 0,
        # but leaves L1, L2, L3 != 0 and Q12, Q23 != 0 active:
        @test rep.metrics.initial_nnz_linear == 3
        @test rep.metrics.transformed_nnz_linear == 3
        @test rep.metrics.initial_nnz_quadratic == 3
        @test rep.metrics.transformed_nnz_quadratic == 2

        # Exact unary dominance (#14) fixes :x1 => 0, :x2 => 1 and eliminates :x1 and BOTH Q12, Q13
        # with an exact constant-shift certificate:
        ws = Workspace(m_sub; rules=:dominance)
        att = prove_dominance(ws, :x1)
        @test att.stop_reason === :proved
        @test att.certificate.steps[end].value == 0
        @test persistency(att.certificate.steps[end]) === :strong
        apply_dominance!(ws, :x1)
        @test deductions(ws) == [:x1 => 0]
        res_model = export_model(materialize(ws; coefficient_type=Rational{BigInt}))
        dom_metrics = compression_metrics(m_sub, res_model)
        @test dom_metrics.transformed_nnz_linear == 2
        @test dom_metrics.transformed_nnz_quadratic == 1
        @test verify_certificate(ws, export_certificate(ws)).valid
    end

    @testset "5. Maximization sense, spin domain, and exact finite-float rationalization" begin
        rep_closed = cex.max_sense_float_exact.closed_report
        rep_open = cex.max_sense_float_exact.open_report
        @test rep_closed.stop_reason === :audited
        @test rep_closed.relation === :introduced_suboptimal_tie
        @test !rep_closed.residual_to_original_valid
        @test rep_closed.decision === :defer
        @test rep_closed.missing_proof === :endpoint_introduces_suboptimal_ties

        @test rep_open.stop_reason === :audited
        @test rep_open.relation === :exact_optimum_set
        @test rep_open.residual_to_original_valid
        @test rep_open.subsumed_by_dominance
        @test rep_open.subsuming_rule === :unary_dominance
        @test rep_open.decision === :adopt_via_exact_elimination

        # Negative scale under :min and :max senses and zero scale:
        m_neg_min = QT.Model(Dict(:x1 => 1.0), Dict{Tuple{Symbol,Symbol},Float64}(); scale=-1.0, offset=0.5, sense=:min, domain=:bool)
        ws_neg = Workspace(m_neg_min)
        @test prove_dominance(ws_neg, :x1).certificate.steps[1].value == 1
        rep_neg_open = audit_compression(m_neg_min; endpoint=:open, epsilon=1 // 2)
        @test rep_neg_open.relation === :exact_optimum_set
        @test rep_neg_open.original_optimal_value == -3 // 2
        @test rep_neg_open.subsumed_by_dominance
        rep_neg_closed = audit_compression(m_neg_min; endpoint=:closed)
        @test rep_neg_closed.relation === :introduced_suboptimal_tie
        @test !rep_neg_closed.residual_to_original_valid
        @test rep_neg_closed.introduced_suboptimal_witness == [0]

        m_neg_max = QT.Model(Dict(:x1 => 1.0), Dict{Tuple{Symbol,Symbol},Float64}(); scale=-2.0, offset=0.0, sense=:max, domain=:bool)
        rep_neg_max = audit_compression(m_neg_max; endpoint=:open, epsilon=1 // 2)
        @test rep_neg_max.relation === :exact_optimum_set
        @test rep_neg_max.original_optimal_value == 0 // 1
        @test rep_neg_max.subsumed_by_dominance

        m_zero_scale = QT.Model(Dict(:x1 => 1.0), Dict{Tuple{Symbol,Symbol},Float64}(); scale=0.0, offset=2.0, sense=:min, domain=:bool)
        rep_zero = audit_compression(m_zero_scale)
        @test rep_zero.relation === :exact_optimum_set
        @test rep_zero.original_optima_count == 2
        @test rep_zero.decision === :noop
    end

    @testset "6. Positive coupling compression without unary dominance cannot sparsify (Q12' > 0)" begin
        # L1 = -1, L2 = -1, Q12 = 5, Q13 = -1, Q23 = -1, L3 = 4:
        # Neither x1 nor x2 is unary-fixable to 0 (L1 + c1^- = -1 - 1 = -2 <= 0),
        # yet L1 + c_{1,-2}^- + Q12 = -1 - 1 + 5 = +3 > 0.
        # Theorem B: open-interval positive quadratic compression can only reduce Q12
        # down to -L1 - c_{1,-2}^- + eps = 2 + 1/2 = 5/2 > 0 (zero sparsification!).
        m_pos = QT.Model(
            Dict(:x1 => -1.0, :x2 => -1.0, :x3 => 4.0),
            Dict((:x1, :x2) => 5.0, (:x1, :x3) => -1.0, (:x2, :x3) => -1.0);
            sense=:min,
            domain=:bool,
        )
        ws_pos = Workspace(m_pos; rules=:mixed)
        @test prove_dominance(ws_pos, :x1).stop_reason === :not_strict
        @test prove_dominance(ws_pos, :x2).stop_reason === :not_strict

        rep_pos = audit_compression(m_pos; endpoint=:open, epsilon=1 // 2)
        @test rep_pos.stop_reason === :audited
        @test rep_pos.relation === :exact_optimum_set
        @test rep_pos.residual_to_original_valid
        @test !rep_pos.constant_energy_shift
        # Q12 is reduced from 5 to 5//2 > 0, so nnz_quadratic is NOT reduced for (:x1, :x2):
        q12_cand = only(filter(c -> c.kind === :quadratic && c.variables == (:x1, :x2), rep_pos.candidates))
        @test q12_cand.original_coeff == 5 // 1
        @test q12_cand.compressed_coeff == 5 // 2
        @test q12_cand.compressed_coeff > 0
        @test q12_cand.subsuming_rule === :pair_dominance
    end

    @testset "7. Partial overlap and optimum-preserving subset custom transformations" begin
        # Original F(x1, x2) = -x1 - x2 + x1 x2 has 3 optimal states: (1,0), (0,1), (1,1).
        # Transformed F'(x1, x2) = -x1 - x2 + 2 x1 x2 narrows optima to (1,0) and (0,1) (2 states < 3 states):
        m0 = QT.Model(Dict(:x1 => -1.0, :x2 => -1.0), Dict((:x1, :x2) => 1.0); sense=:min, domain=:bool)
        m_sub_opt = QT.Model(Dict(:x1 => -1.0, :x2 => -1.0), Dict((:x1, :x2) => 2.0); sense=:min, domain=:bool)
        rep_subset = audit_compression(m0, m_sub_opt)
        @test rep_subset.relation === :optimum_preserving_subset
        @test rep_subset.residual_to_original_valid
        @test rep_subset.original_optima_count == 3
        @test rep_subset.transformed_optima_count == 2
        @test rep_subset.shared_optima_count == 2
        @test rep_subset.introduced_suboptimal_witness === nothing
        @test rep_subset.lost_optimum_witness == [1, 1]
        @test rep_subset.decision === :defer
        @test rep_subset.missing_proof === :state_dependent_energy_shift_without_branch_exclusion

        # Partial overlap: F(x1, x2) = (x1 - x2)^2 = x1 + x2 - 2 x1 x2 (optima: (0,0) and (1,1))
        # vs F'(x1, x2) = x1 + x1 x2 (optima: (0,0) and (0,1)) -> shares (0,0), loses (1,1), introduces (0,1)!
        m_orig_po = QT.Model(Dict(:x1 => 1.0, :x2 => 1.0), Dict((:x1, :x2) => -2.0); sense=:min, domain=:bool)
        m_trans_po = QT.Model(Dict(:x1 => 1.0), Dict((:x1, :x2) => 1.0); sense=:min, domain=:bool)
        rep_po = audit_compression(m_orig_po, m_trans_po)
        @test rep_po.relation === :partial_overlap_with_suboptimal
        @test !rep_po.residual_to_original_valid
        @test rep_po.shared_optima_count == 1
        @test rep_po.introduced_suboptimal_witness == [0, 1]
        @test rep_po.lost_optimum_witness == [1, 1]
        @test rep_po.decision === :defer
        @test rep_po.missing_proof === :partial_overlap_introduces_suboptimal_optima
    end

    @testset "8. Workspace input, chained updates, budgets, and validation" begin
        m = cex.strict_interior_subsumed.model
        ws = Workspace(m)
        rep_ws = audit_compression(ws; endpoint=:open, epsilon=1 // 2, chain=true)
        @test rep_ws.stop_reason === :audited
        @test rep_ws.relation === :exact_optimum_set
        @test rep_ws.total_work == rep_ws.bound_work + rep_ws.verification_work + rep_ws.reconstruction_work

        # Variable cap prevents exponential enumeration:
        rep_vcap = audit_compression(m; max_vars=2)
        @test rep_vcap.stop_reason === :variable_limit_exceeded
        @test rep_vcap.relation === :unverified
        @test !rep_vcap.residual_to_original_valid
        @test rep_vcap.states_evaluated == 0
        @test rep_vcap.decision === :defer
        @test rep_vcap.missing_proof === :audit_budget_exceeded

        # Work cap during candidate generation or state verification:
        rep_wcap1 = audit_compression(m; max_work=1)
        @test rep_wcap1.stop_reason === :work_limit_exceeded
        @test rep_wcap1.states_evaluated == 0
        rep_wcap2 = audit_compression(m; max_work=10)
        @test rep_wcap2.stop_reason === :work_limit_exceeded
        @test rep_wcap2.states_evaluated == 0

        @test_throws ArgumentError qubolite_compression_candidates(m; endpoint=:invalid)
        @test_throws ArgumentError qubolite_compression_candidates(m; endpoint=:open, epsilon=0)
        @test_throws ArgumentError audit_compression(m; max_vars=17)
        @test_throws ArgumentError audit_compression(m; max_work=-1)
    end

    @testset "9. Large-instance scalability and certified fast rejection" begin
        # 1. Unique large (n, m) tuple length without O(N^2) deepcopy/specialization latency:
        n_lg = 223
        L_lg = Dict{Int,Float64}(i => (i == 1 ? 500.0 : 0.1 * ((i % 7) - 3)) for i in 1:n_lg)
        Q_lg = Dict{Tuple{Int,Int},Float64}()
        for i in 1:n_lg, j in (i + 1):min(n_lg, i + 20)
            Q_lg[(i, j)] = ((i + j) % 2 == 0) ? 1.0 : -1.0
        end
        m_lg = QT.Model(L_lg, Q_lg; sense=:min, domain=:bool)
        ws_lg = Workspace(m_lg; rules=:mixed)
        r_lg = schedule_reductions!(ws_lg; enable_star_triangle=true)
        @test r_lg.dominance_deductions >= 1
        @test r_lg.exact_fallbacks == 0
        t_cert0 = time()
        cert_lg = export_certificate(ws_lg)
        mat_lg = materialize(ws_lg; coefficient_type=Float64)
        elapsed_cert = time() - t_cert0
        @test cert_lg !== nothing
        @test verify_certificate(ws_lg, cert_lg).valid
        @test QT.dimension(export_model(mat_lg)) == n_lg - length(ws_lg._state.fixes)
        @test elapsed_cert < 5.0

        # 2. O(1) _ws_mc_total_abs_weight exact match with _poly_mc_total_abs_weight across domains:
        for dom in (:bool, :spin)
            m_mc = QT.Model(
                Dict(1 => 1.5, 2 => -2.25, 3 => 0.75, 4 => -0.5),
                Dict((1, 2) => -3.0, (1, 3) => 2.5, (2, 3) => 1.25, (2, 4) => -1.75, (3, 4) => 0.5);
                sense=:min,
                domain=dom,
            )
            ws_mc = Workspace(m_mc; rules=:mixed)
            assume!(ws_mc, 4, 1)
            p_mc = QUBOPreprocessing._init_poly_state(ws_mc._snapshot)
            QUBOPreprocessing._poly_fix!(p_mc, 4, 1)
            dir_mc = QUBOPreprocessing._direction(ws_mc._snapshot)
            for u in 1:3
                w_fast = QUBOPreprocessing._ws_mc_total_abs_weight(ws_mc, u, dir_mc)
                w_poly = QUBOPreprocessing._poly_mc_total_abs_weight(p_mc, u, dir_mc)
                @test w_fast[1] && w_fast[2] === :ok && w_fast[3] == w_poly
            end
        end
    end
end
