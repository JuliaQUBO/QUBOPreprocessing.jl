@testset "certified probing with reversible branch bounds and feasible witnesses (#11)" begin
    # Helper: guarded exhaustive enumeration for tiny test models (n <= 6)
    function exact_optima(model::QT.Model, scope::Dict{Int,Int}=Dict{Int,Int}())
        n = QT.dimension(model)
        n <= 6 || throw(ArgumentError("exhaustive test helper guarded to n <= 6"))
        dom = QT.domain(model)
        sense = QT.sense(model)
        low = dom === QT.BoolDomain ? 0 : -1
        best_val = sense === QT.Min ? Inf : -Inf
        opt_states = Vector{Int}[]
        state = Vector{Int}(undef, n)
        for mask in 0:((1 << n) - 1)
            ok = true
            for j in 1:n
                v = ((mask >> (j - 1)) & 1) == 1 ? 1 : low
                if haskey(scope, j) && scope[j] != v
                    ok = false
                    break
                end
                state[j] = v
            end
            ok || continue
            e = QT.value(state, QT.form(model))
            if (sense === QT.Min && e < best_val - 1e-12) || (sense === QT.Max && e > best_val + 1e-12)
                best_val = e
                empty!(opt_states)
                push!(opt_states, copy(state))
            elseif abs(e - best_val) <= 1e-12
                push!(opt_states, copy(state))
            end
        end
        return best_val, opt_states
    end

    @testset "safe fixing missed by cheap dominance and exhaustive tiny branch check" begin
        # E(s) = 4.0*s1 + 1.5*s2 + 1.5*s3 + 2.5*s1*s2 + 2.5*s1*s3 - 1.0*s2*s3
        # Cheap unary dominance derivatives:
        #   s1: 4.0 - (2.5 + 2.5) = -1.0 <= dE/ds1 <= 9.0 (sign-indefinite)
        #   s2: 1.5 - (2.5 + 1.0) = -2.0 <= dE/ds2 <= 5.0 (sign-indefinite)
        #   s3: 1.5 - (2.5 + 1.0) = -2.0 <= dE/ds3 <= 5.0 (sign-indefinite)
        # Trial branch s1 = +1 shifts fields of s2, s3 to 1.5 + 2.5 = 4.0 > 1.0,
        # fixing s2 = -1, s3 = -1 by trial dominance and yielding branch energy
        # E(+1, -1, -1) = 4.0 - 4.0 - 4.0 - 1.0 = -5.0 > E(-1, +1, +1) = -7.0.
        L = Dict(1 => 4.0, 2 => 1.5, 3 => 1.5)
        Q = Dict((1, 2) => 2.5, (1, 3) => 2.5, (2, 3) => -1.0)
        model = QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
        ws = Workspace(model; rules=:dominance)

        # Cheap dominance fixes 0 variables
        cheap_rep = propagate!(ws)
        @test cheap_rep.stop_reason === :quiescent
        @test cheap_rep.deductions == 0
        @test isempty(deductions(ws))

        # Exhaustive check of true optimum
        best_e, opt_states = exact_optima(model)
        @test best_e == -7.0
        @test opt_states == [[-1, 1, 1]]

        # Read-only prove_probing on s1 with witness w = [-1, 1, 1]
        w = [-1, 1, 1]
        cp_before = checkpoint(ws)
        att = prove_probing(ws, 1, w)
        @test att isa ProbingAttempt
        @test att.stop_reason === :proved
        @test att.method in (:interval, :exact)
        @test att.edge_visits > 0
        @test att.certificate !== nothing
        # Read-only prove_probing does not mutate ws
        @test checkpoint(ws) == cp_before
        @test isempty(deductions(ws))

        cert1 = att.certificate
        @test step_guarantee(cert1.steps[1]) === :optimum_preserving_restriction
        @test persistency(cert1.steps[1]) === :strong
        @test certificate_guarantee(cert1) === :optimum_preserving_restriction
        @test persistency(cert1) === :strong
        pstep = cert1.steps[1]::ProbingStep
        @test pstep.variable == 1
        @test pstep.value == -1
        @test pstep.probed_value == 1
        @test pstep.witness_upper == -7 // 1
        @test pstep.branch_lower > pstep.witness_upper
        @test pstep.branch_lower == -5 // 1
        @test pstep.witness_state == (-1, 1, 1)
        @test length(pstep.branch_steps) == 2
        @test verify_certificate(ws, cert1).valid

        # Inconclusive probe with poor heuristic witness w_bad = [1, 1, 1] (E = 11.0 >= -5.0)
        att_bad = prove_probing(ws, 1, [1, 1, 1])
        @test att_bad.stop_reason === :not_strict
        @test att_bad.certificate === nothing
        @test checkpoint(ws) == cp_before
        @test isempty(deductions(ws))

        # Inconclusive probe when max_rounds=0 on a 3-spin model where round-1 trial dominance is required:
        # On s1 = +1, h2 = 2.5 + 4.0 = 6.5 > |-3.0| fixes s2 = -1 in round 1, shifting h3 from -1.0 to +2.0
        # and raising the branch lower bound from L = -11.0 == U (not strict at max_rounds=0) to L = -9.0 > U = -11.0!
        m_chain = QT.Model{Int,Float64,Int}(
            Dict(1 => -0.5, 2 => 2.5, 3 => -4.0),
            Dict((1, 2) => 4.0, (1, 3) => 3.0, (2, 3) => -3.0);
            domain=:spin, sense=:min,
        )
        ws_chain = Workspace(m_chain; rules=:dominance)
        @test propagate!(ws_chain).deductions == 0
        w_chain = [-1, 1, 1] # E(-1, 1, 1) = 0.5 + 2.5 - 4.0 - 4.0 - 3.0 - 3.0 = -11.0
        att_no_cascade = prove_probing(ws_chain, 1, w_chain; max_rounds=0)
        @test att_no_cascade.stop_reason === :not_strict
        @test att_no_cascade.certificate === nothing
        att_with_cascade = prove_probing(ws_chain, 1, w_chain; max_rounds=1)
        @test att_with_cascade.stop_reason === :proved
        @test verify_certificate(ws_chain, att_with_cascade.certificate).valid

        # Commit probing across all variables via probe_variables!
        p_rep = probe_variables!(ws, w)
        @test p_rep isa ProbingReport
        @test generation(p_rep) == generation(ws)
        @test p_rep.stop_reason === :quiescent
        @test p_rep.candidates == 3
        @test p_rep.deductions == 3
        @test p_rep.pending == 0
        @test Dict(deductions(ws)) == Dict(1 => -1, 2 => 1, 3 => 1)
        # Every emitted fixing holds in all parent-scope optima
        for (lbl, val) in deductions(ws)
            @test all(st[lbl] == val for st in opt_states)
        end
        full_cert = export_certificate(ws)
        @test verify_certificate(ws, full_cert).valid
        cond = materialize(ws)
        rec = reconstruct(cond, Int[])
        @test rec.state == [-1, 1, 1]
        @test rec.energy.value == -7.0
    end

    @testset "inconclusive probe preserves both branches when optima exist on both" begin
        # Symmetric model E(s1, s2) = -s1*s2 has optima (-1, -1) and (+1, +1) with E = -1.0
        model_sym = QT.Model{Int,Float64,Int}(
            Dict(1 => 0.0, 2 => 0.0),
            Dict((1, 2) => -1.0);
            domain=:spin, sense=:min,
        )
        ws_sym = Workspace(model_sym; rules=:dominance)
        _, sym_opts = exact_optima(model_sym)
        @test length(sym_opts) == 2

        # Even given an optimal witness [1, 1] (U = -1), probing s1 = -1 finds L = -1 == U,
        # which is NOT strictly greater than U, so probing must abstain!
        att_sym = prove_probing(ws_sym, 1, [1, 1])
        @test att_sym.stop_reason === :not_strict
        @test att_sym.certificate === nothing
        upd_sym = apply_probing!(ws_sym, 1, [1, 1])
        @test upd_sym.stop_reason === :not_strict
        @test upd_sym.changed == 0
        rep_sym = probe_variables!(ws_sym, [1, 1])
        @test rep_sym.stop_reason === :quiescent
        @test rep_sym.deductions == 0
        @test isempty(deductions(ws_sym))
    end

    @testset "near-equality rounding fallback from interval to exact" begin
        # Construct a 3-variable boolean model where x1=0 gives 0, and on trial branch x1=1
        # (with max_rounds=0), constant is 1.0 and fields of x2, x3 are -0.5 and -prevfloat(0.5),
        # so exact L_bpos = 1.0 - 0.5 - (0.5 - 2^-53) = 2^-53 > 0 = U_exact, while outward
        # prevfloat interval addition rounds to prevfloat(0.0) < 0 and triggers exact fallback!
        L_near = Dict(1 => 1.0, 2 => 0.0, 3 => 0.0)
        Q_near = Dict((1, 2) => -0.5, (1, 3) => -prevfloat(0.5))
        model_near = QT.Model{Int,Float64,Int}(L_near, Q_near; domain=:bool, sense=:min)
        ws_near = Workspace(model_near; rules=:dominance)

        att_near = prove_probing(ws_near, 1, [0, 0, 0]; max_rounds=0)
        @test att_near.stop_reason === :proved
        @test att_near.method === :exact
        @test att_near.exact_fallbacks == 1
        @test att_near.exact_work > 0
        @test att_near.certificate !== nothing
        @test verify_certificate(ws_near, att_near.certificate).valid

        # When max_exact_work is capped so the exact fallback is disallowed, interval alone abstains:
        att_capped = prove_probing(ws_near, 1, [0, 0, 0]; max_rounds=0, max_exact_work=4)
        @test att_capped.stop_reason === :verification_limit
        @test att_capped.certificate === nothing
    end

    @testset "domains, senses, scales, offsets, and witness input formats" begin
        # Base spin minimization model where probing fixes variable 1 -> -1
        L_base = Dict(:x1 => 4.0, :x2 => 1.5, :x3 => 1.5)
        Q_base = Dict((:x1, :x2) => 2.5, (:x1, :x3) => 2.5, (:x2, :x3) => -1.0)
        for dom in (:spin, :bool)
            for sense in (:min, :max)
                for scale in (1.0, 2.5, -3.0)
                    for offset in (0.0, -4.25, 7.5)
                        # Direction sign relative to standard Min with positive scale:
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
                        w_val = dom === :spin ? [-1, 1, 1] : [0, 1, 1]
                        expected_v1 = dom === :spin ? -1 : 0

                        # Test Dict witness format
                        w_dict = Dict(:x1 => w_val[1], :x2 => w_val[2], :x3 => w_val[3])
                        att = prove_probing(ws, :x1, w_dict)
                        @test att.stop_reason === :proved
                        @test verify_certificate(ws, att.certificate).valid

                        # Test Reconstruction witness format
                        id_exp = materialize(ws)
                        w_rec = reconstruct(id_exp, w_val)
                        upd = apply_probing!(ws, :x1, w_rec; value=expected_v1)
                        @test upd.stop_reason === :applied
                        @test upd.changed == 1
                        @test Dict(deductions(ws))[:x1] == expected_v1
                        cert = export_certificate(ws)
                        @test verify_certificate(ws, cert).valid
                    end
                end
            end
        end

        # Zero scale abstains cleanly with :zero_scale (even under tight max_work)
        m_zero = QT.Model{Int,Float64,Int}(Dict(1 => 4.0, 2 => 1.5), Dict((1, 2) => 2.5); scale=0.0, domain=:spin, sense=:min)
        ws_zero = Workspace(m_zero)
        @test prove_probing(ws_zero, 1, [-1, 1]).stop_reason === :zero_scale
        @test apply_probing!(ws_zero, 1, [-1, 1]).stop_reason === :zero_scale
        @test apply_probing!(ws_zero, 1, [-1, 1]; max_work=0).stop_reason === :zero_scale
        @test probe_variables!(ws_zero, [-1, 1]).stop_reason === :zero_scale
    end

    @testset "QUBO-Ising metamorphic equivalence and DomainGaugeMap transport" begin
        L_spin = Dict(1 => 4.0, 2 => 1.5, 3 => 1.5)
        Q_spin = Dict((1, 2) => 2.5, (1, 3) => 2.5, (2, 3) => -1.0)
        m_spin = QT.Model{Int,Float64,Int}(L_spin, Q_spin; offset=1.25, scale=2.0, domain=:spin, sense=:min)
        ws_spin = Workspace(m_spin; rules=:dominance)
        m_bool = export_model(materialize(ws_spin, domain_map(ws_spin; domain=:bool)))
        ws_bool = Workspace(m_bool; rules=:dominance)

        att_spin = prove_probing(ws_spin, 1, [-1, 1, 1])
        att_bool = prove_probing(ws_bool, 1, [0, 1, 1])
        @test att_spin.stop_reason === :proved
        @test att_bool.stop_reason === :proved

        step_s = att_spin.certificate.steps[1]::ProbingStep
        step_b = att_bool.certificate.steps[1]::ProbingStep
        # Exact normalized witness upper bound and exact trial branch lower bound match across QUBO <-> Ising
        @test step_s.witness_upper == step_b.witness_upper
        @test step_s.branch_lower == step_b.branch_lower
        @test length(step_s.branch_steps) == length(step_b.branch_steps) == 2

        # Gauge-transformed coordinate map on ws_bool
        dmap = domain_map(ws_bool; domain=:spin, gauge=[-1, 1, -1])
        # Mapped witness in gauged spin coordinates: t_i = g_i * (2*x_i - 1)
        w_mapped = map_state(dmap, [0, 1, 1])
        att_mapped = prove_probing(ws_bool, 1, w_mapped; map=dmap)
        @test att_mapped.stop_reason === :proved
        @test verify_certificate(ws_bool, att_mapped.certificate; map=dmap).valid

        # Transport unmapped certificate into dmap and back
        cert_transported = transport_certificate(ws_bool, att_bool.certificate, dmap)
        @test verify_certificate(ws_bool, cert_transported; map=dmap).valid

        # Commit on ws_bool with dmap and export conditioned model + reconstruct
        upd_m = apply_probing!(ws_bool, 1, w_mapped; map=dmap)
        @test upd_m.stop_reason === :applied
        @test apply_probing!(ws_bool, 1, w_mapped; map=dmap, max_work=0).stop_reason === :already_fixed
        @test verify_certificate(ws_bool, export_certificate(ws_bool; map=dmap); map=dmap).valid
        cond_m = materialize(ws_bool, dmap)
        rec_m = reconstruct(cond_m, [w_mapped[2], w_mapped[3]])
        @test rec_m.state == [0, 1, 1]

        # Non-identity gauged binary map on ws_spin must not corrupt dmap._cursor constant cache across probe rollback
        ws_spin_g = Workspace(m_spin; rules=:dominance)
        dmap_bool_g = domain_map(ws_spin_g; domain=:bool, gauge=[-1, 1, -1])
        w_bool_g = map_state(dmap_bool_g, [-1, 1, 1])
        att_bg = prove_probing(ws_spin_g, 1, w_bool_g; map=dmap_bool_g)
        @test att_bg.stop_reason === :proved
        ws_spin_ref = Workspace(m_spin; rules=:dominance)
        dmap_bool_ref = domain_map(ws_spin_ref; domain=:bool, gauge=[-1, 1, -1])
        assume!(ws_spin_g, 1, -1)
        assume!(ws_spin_ref, 1, -1)
        @test conditioned_constant(ws_spin_g; map=dmap_bool_g) ==
              conditioned_constant(ws_spin_ref; map=dmap_bool_ref)
    end

    @testset "witness validation, tampered certificates, wrong scope, and stale generation" begin
        L = Dict(1 => 4.0, 2 => 1.5, 3 => 1.5, 4 => 0.5)
        Q = Dict((1, 2) => 2.5, (1, 3) => 2.5, (2, 3) => -1.0, (3, 4) => 0.25)
        model = QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
        ws = Workspace(model; rules=:dominance)

        # Invalid witness shapes, types, and out-of-domain values
        @test_throws ArgumentError prove_probing(ws, 1, [-1, 1])
        @test_throws ArgumentError prove_probing(ws, 1, [-1, 1, 0, 1])
        @test_throws ArgumentError prove_probing(ws, 1, Dict(1 => -1, 2 => 1, 3 => 1))
        @test_throws ArgumentError prove_probing(ws, 1, "not_a_witness")

        # Stale Reconstruction witness from another workspace generation
        ws_other = Workspace(model)
        rec_other = reconstruct(materialize(ws_other), [-1, 1, 1, -1])
        @test_throws ArgumentError prove_probing(ws, 1, rec_other)

        # Caller assumption scope compatibility: assume x4 = -1, then pass witness with x4 = +1
        assume!(ws, 4, -1)
        @test_throws ArgumentError prove_probing(ws, 1, [-1, 1, 1, 1])
        @test_throws ArgumentError apply_probing!(ws, 1, [-1, 1, 1, 1])
        @test_throws ArgumentError probe_variables!(ws, [-1, 1, 1, 1])

        # Compatible witness with x4 = -1 succeeds
        w_valid = [-1, 1, 1, -1]
        att = prove_probing(ws, 1, w_valid)
        @test att.stop_reason === :proved
        cert = att.certificate
        @test verify_certificate(ws, cert).valid
        s0 = cert.steps[1]::ProbingStep

        # Tamper with certificate fields and check verify_certificate rejects each one
        bad_pred = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 2, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_pred,), cert._source, cert._map)).stop_reason === :invalid_predecessors

        bad_var = ProbingStep(4, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_var,), cert._source, cert._map)).stop_reason === :invalid_step

        bad_val = ProbingStep(s0.variable, 1, 1, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_val,), cert._source, cert._map)).stop_reason === :invalid_value

        bad_method = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, :heuristic, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_method,), cert._source, cert._map)).stop_reason === :invalid_method

        bad_pers = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, s0.method, s0.scope_length, :weak)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_pers,), cert._source, cert._map)).stop_reason === :invalid_method

        bad_const = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant + 1, 0, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_const,), cert._source, cert._map)).stop_reason === :invalid_constant

        # Tampered witness state: violating assumption x4 = -1
        bad_w_scope = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            (-1, 1, 1, 1), s0.branch_steps, s0.constant, 0, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_w_scope,), cert._source, cert._map)).stop_reason === :invalid_witness

        # Tampered witness upper bound scalar
        bad_w_upper = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper - 1,
            s0.witness_state, s0.branch_steps, s0.constant, 0, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_w_upper,), cert._source, cert._map)).stop_reason === :invalid_witness

        # Tampered branch lower bound (inflated above L_exact or <= witness_upper)
        bad_blo_high = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower + 100, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, s0.method, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_blo_high,), cert._source, cert._map)).stop_reason === :invalid_bound

        bad_blo_le = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.witness_upper, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, :interval, s0.scope_length, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_blo_le,), cert._source, cert._map)).stop_reason === :invalid_bound

        # Wrong scope_length (0 instead of 1 when 1 caller assumption exists)
        bad_scope_len = ProbingStep(s0.variable, s0.value, s0.probed_value, s0.branch_lower, s0.witness_upper,
            s0.witness_state, s0.branch_steps, s0.constant, 0, s0.method, 0, s0.persistency)
        @test verify_certificate(ws, DominanceCertificate(cert.generation, cert._scope_checkpoint,
            cert.assumptions, (bad_scope_len,), cert._source, cert._map)).stop_reason === :invalid_scope

        # Stale scope after new caller assumption
        cp_pre_assume = checkpoint(ws)
        assume!(ws, 2, 1)
        @test verify_certificate(ws, cert).stop_reason === :stale_scope
        rollback!(ws, cp_pre_assume)
        @test verify_certificate(ws, cert).valid

        # Stale generation after reset!
        reset!(ws, model)
        @test verify_certificate(ws, cert).stop_reason === :stale_generation
    end

    @testset "interrupted probes restore state/queues/provenance and preserve prior deductions" begin
        # Variable 4 is strictly dominated (field = 10.0 > 0.25), while variables 1..3 require probing
        L = Dict(1 => 4.0, 2 => 1.5, 3 => 1.5, 4 => 10.0)
        Q = Dict((1, 2) => 2.5, (1, 3) => 2.5, (2, 3) => -1.0, (3, 4) => 0.25)
        model = QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
        ws = Workspace(model; rules=:dominance)

        # Commit variable 4 = -1 via cheap dominance first
        @test apply_dominance!(ws, 4).stop_reason === :applied
        @test deductions(ws) == [4 => -1]
        cp_prior = checkpoint(ws)
        cert_prior = export_certificate(ws)
        @test verify_certificate(ws, cert_prior).valid
        f_before = [effective_field(ws, u) for u in 1:3]
        c_before = conditioned_constant(ws)

        w = [-1, 1, 1, -1]

        # 1. Interrupted by expired deadline_ns
        att_dl = prove_probing(ws, 1, w; deadline_ns=UInt64(1))
        @test att_dl.stop_reason === :deadline
        @test att_dl.certificate === nothing
        @test checkpoint(ws) == cp_prior
        @test verify_certificate(ws, cert_prior).valid

        # 2. Interrupted mid-probe by tight max_work (enough to fix x1=+1 on trial branch, not enough to finish)
        rep_wl = probe_variables!(ws, w; candidates=[1, 2], max_work=8)
        @test rep_wl.stop_reason === :work_limit
        @test rep_wl.candidates == 1
        @test rep_wl.edge_visits > 0
        @test rep_wl.deductions == 0
        @test rep_wl.totals.candidates >= 1
        @test rep_wl.totals.edge_visits >= rep_wl.edge_visits
        # Workspace state, fields, constant, and prior certificate are 100% intact
        @test checkpoint(ws) == cp_prior
        @test deductions(ws) == [4 => -1]
        @test [effective_field(ws, u) for u in 1:3] == f_before
        @test conditioned_constant(ws) == c_before
        @test verify_certificate(ws, cert_prior).valid
        @test verify_certificate(ws, export_certificate(ws)).valid

        # 3. Bounded by max_candidates=1
        rep_cl = probe_variables!(ws, w; candidates=[1, 2, 3], max_candidates=1)
        @test rep_cl.stop_reason === :candidate_limit
        @test rep_cl.candidates == 1
        @test rep_cl.deductions == 1
        @test rep_cl.pending == 2
        @test deductions(ws) == [4 => -1, 1 => -1]
        @test verify_certificate(ws, export_certificate(ws)).valid

        # Rollback the probing deduction back to cp_prior; prior deduction remains intact
        rollback!(ws, cp_prior)
        @test deductions(ws) == [4 => -1]
        @test verify_certificate(ws, cert_prior).valid
    end

    @testset "break-even comparison vs cheap dominance and no preprocessing" begin
        # Build a family of 4-spin frustrated blocks (scaled by 8^-b) where cheap dominance fixes 0 variables
        # and certified probing + cheap dominance cascade fixes all variables.
        L = Dict{Int,Float64}()
        Q = Dict{Tuple{Int,Int},Float64}()
        n_blocks = 4
        w_full = Vector{Int}(undef, 4 * n_blocks)
        for b in 0:(n_blocks - 1)
            scale_b = ldexp(1.0, -3 * b)
            r = 4 * b + 1
            u1, u2, u3 = r + 1, r + 2, r + 3
            L[r] = 5.0 * scale_b
            L[u1] = 0.5 * scale_b
            L[u2] = 0.5 * scale_b
            L[u3] = 0.5 * scale_b
            Q[(r, u1)] = 2.0 * scale_b
            Q[(r, u2)] = 2.0 * scale_b
            Q[(r, u3)] = 2.0 * scale_b
            Q[(u1, u2)] = -0.8 * scale_b
            Q[(u1, u3)] = -0.8 * scale_b
            Q[(u2, u3)] = -0.8 * scale_b
            w_full[r] = -1
            w_full[u1] = 1
            w_full[u2] = 1
            w_full[u3] = 1
        end
        m_bench = QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)

        # 1. No preprocessing (:identity): 0 reductions, 16 residual variables
        ws_id, rep_id = preprocess(m_bench; rules=:identity)
        @test rep_id isa IdentityReport
        @test isempty(deductions(ws_id))

        # 2. Cheap dominance only (:dominance): 0 reductions on frustrated blocks, 16 residual variables
        ws_dom, rep_dom = preprocess(m_bench; rules=:dominance)
        @test rep_dom.stop_reason === :quiescent
        @test rep_dom.deductions == 0
        @test isempty(deductions(ws_dom))
        # Confirm default pass never invokes ProbingStep
        @test all(!(s isa ProbingStep) for s in reductions(ws_dom))

        # 3. Optional bounded probing across all candidates: fixes all 16 variables!
        alloc_probe = @allocated begin
            rep_probe = probe_variables!(ws_dom, w_full; max_rounds=1)
        end
        @test rep_probe.stop_reason === :quiescent
        @test rep_probe.candidates == 4 * n_blocks
        @test rep_probe.deductions == 4 * n_blocks
        @test length(deductions(ws_dom)) == 4 * n_blocks
        @test alloc_probe > 0
        cert_bench = export_certificate(ws_dom)
        @test verify_certificate(ws_dom, cert_bench).valid

        # 4. Witness-free probing (witness = nothing) with coercive_field_witness fixes all 16 variables!
        ws_auto = Workspace(m_bench; rules=:dominance)
        @test propagate!(ws_auto).deductions == 0
        @test coercive_field_witness(ws_auto) == w_full
        rep_auto = probe_variables!(ws_auto; order=:coercive, max_rounds=1)
        @test rep_auto.stop_reason === :quiescent
        @test rep_auto.deductions == 4 * n_blocks
        @test verify_certificate(ws_auto, export_certificate(ws_auto)).valid
    end

    @testset "conditioned coercive-field diagnostics, deterministic witness, and probing orderings (#49)" begin
        # 1. Conditioned coercive-field diagnostics on :bool and :spin workspaces
        L_b = Dict(1 => 2.0, 2 => -4.0, 3 => 0.0, 4 => 6.0)
        Q_b = Dict((1, 2) => 8.0, (2, 3) => -4.0)
        m_b = QT.Model{Int,Float64,Int}(Set(1:4), L_b, Q_b; domain=:bool, sense=:min)
        ws_b = Workspace(m_b; rules=:mixed)

        # h_1 = 2/2 + 8/4 = 3//1, ||J_1||_1 = 2//1
        # h_2 = -4/2 + (8 - 4)/4 = -1//1, ||J_2||_1 = 3//1
        # h_3 = 0/2 - 4/4 = -1//1, ||J_3||_1 = 1//1
        # h_4 = 6/2 = 3//1 (isolated), ||J_4||_1 = 0//1
        @test coercive_fields(ws_b) == Rational{BigInt}[3 // 1, -1 // 1, -1 // 1, 3 // 1]
        @test !is_gauge_invariant(ws_b)
        @test is_gauge_invariant(ws_b; atol=3)
        @test is_gauge_invariant(ws_b; atol=Inf)
        @test zero_field_fraction(ws_b) == 0.0
        @test zero_field_fraction(ws_b; atol=1) == 0.5
        @test trivial_dominance_fraction(ws_b) == 0.5
        @test trivial_dominance_fraction(ws_b; atol=Inf) == 0.0

        r1 = coercive_field_ratios(ws_b; norm=1)
        @test r1[1:3] ≈ [1.5, 1 / 3, 1.0]
        @test isinf(r1[4])
        @test coercive_field_ratio(ws_b; norm=1) ≈ (1.5 + 1 / 3 + 1.0) / 3

        r2 = coercive_field_ratios(ws_b; norm=2)
        @test r2[1:3] ≈ [1.5, 1 / sqrt(5.0), 1.0]
        @test isinf(r2[4])
        @test coercive_field_ratio(ws_b; norm=2) ≈ (1.5 + 1 / sqrt(5.0) + 1.0) / 3

        rinf = coercive_field_ratios(ws_b; norm=Inf)
        @test rinf[1:3] ≈ [1.5, 0.5, 1.0]

        r3 = coercive_field_ratios(ws_b; norm=3)
        @test r3[2] ≈ 1.0 / (2.0^3 + 1.0^3)^(1 / 3)

        # Gauge map transforms coercive_fields signs while preserving ratios
        dmap_g = domain_map(ws_b; domain=:spin, gauge=[-1, 1, -1, 1])
        @test coercive_fields(ws_b; map=dmap_g) == Rational{BigInt}[-3 // 1, -1 // 1, 1 // 1, 3 // 1]
        @test coercive_field_ratio(ws_b; norm=1, map=dmap_g) ≈ (1.5 + 1 / 3 + 1.0) / 3

        # Conditioning updates coercive_fields dynamically, and fixing all variables yields empty/NaN
        cp_b = checkpoint(ws_b)
        for v in 1:4
            assume!(ws_b, v, 0)
        end
        @test isempty(coercive_fields(ws_b))
        @test isempty(coercive_field_ratios(ws_b))
        @test isnan(coercive_field_ratio(ws_b))
        @test is_gauge_invariant(ws_b)
        @test isnan(zero_field_fraction(ws_b))
        @test isnan(trivial_dominance_fraction(ws_b))
        rollback!(ws_b, cp_b)

        # 2. Reverse-trail lifting in coercive_field_witness across caller assumptions, eliminations, relations, and dominance
        m_lift = QT.Model{Int,Float64,Int}(
            Dict(1 => 0.0, 2 => 0.0, 3 => 4.0, 4 => 1.5, 5 => 1.5),
            Dict((1, 2) => -2.0, (2, 3) => -4.0, (3, 4) => 2.5, (3, 5) => 2.5, (4, 5) => -1.0);
            domain=:spin, sense=:min,
        )
        ws_lift = Workspace(m_lift; rules=:mixed)
        # Eliminate degree-1 variable 1 into 2, then contract 2 into 3
        @test eliminate_variable!(ws_lift, 1).stop_reason === :applied
        @test contract_relation!(ws_lift, 2, 3).stop_reason === :applied
        w_lift = coercive_field_witness(ws_lift)
        @test w_lift == [-1, -1, -1, 1, 1]
        # Witness-free prove_probing, apply_probing!, and probe_variables! work directly after reductions
        att_lift = prove_probing(ws_lift, 3)
        @test att_lift.stop_reason === :proved
        @test verify_certificate(ws_lift, att_lift.certificate).valid
        upd_lift = apply_probing!(ws_lift, 3)
        @test upd_lift.stop_reason === :applied
        rep_lift = probe_variables!(ws_lift)
        @test rep_lift.stop_reason === :quiescent
        @test verify_certificate(ws_lift, export_certificate(ws_lift)).valid

        # Mapped witness round-trip with DomainGaugeMap
        ws_map_test = Workspace(
            QT.Model{Int,Float64,Int}(
                Dict(1 => 4.0, 2 => 1.5, 3 => 1.5),
                Dict((1, 2) => 2.5, (1, 3) => 2.5, (2, 3) => -1.0);
                domain=:spin, sense=:min,
            );
            rules=:dominance,
        )
        dmap_bool = domain_map(ws_map_test; domain=:bool, gauge=[-1, 1, -1])
        w_mapped = coercive_field_witness(ws_map_test; map=dmap_bool)
        @test prove_probing(ws_map_test, 1, w_mapped; map=dmap_bool).stop_reason === :proved
        @test prove_probing(ws_map_test, 1; map=dmap_bool).stop_reason === :proved

        # 3. Candidate ordering (:coercive and :extremal vs :index) under max_candidates=1
        # Variables 1, 2 form a zero-field symmetric pair E(s1, s2) = -s1*s2 (coercive ratio 0, unprovable),
        # while variables 3, 4, 5 form a frustrated block where root 3 has the highest coercive ratio (4.0 / 5.0 = 0.8).
        # Under max_candidates=1, :index probes variable 1 first (0 deductions), whereas :coercive and :extremal
        # probe variable 3 first and immediately certify 3 => -1!
        m_order_star = QT.Model{Int,Float64,Int}(
            Dict(1 => 0.0, 2 => 0.0, 3 => 4.0, 4 => 1.5, 5 => 1.5),
            Dict(
                (1, 2) => -1.0,
                (3, 4) => 2.5, (3, 5) => 2.5, (4, 5) => -1.0,
            );
            domain=:spin, sense=:min,
        )
        ws_idx = Workspace(m_order_star; rules=:dominance)
        rep_idx = probe_variables!(ws_idx; order=:index, max_candidates=1)
        @test rep_idx.stop_reason === :candidate_limit
        @test rep_idx.candidates == 1
        @test rep_idx.deductions == 0

        for ord in (:coercive, :extremal)
            ws_ord = Workspace(m_order_star; rules=:dominance)
            rep_ord = probe_variables!(ws_ord; order=ord, max_candidates=1)
            @test rep_ord.stop_reason === :candidate_limit
            @test rep_ord.candidates == 1
            @test rep_ord.deductions == 1
            @test Dict(deductions(ws_ord)) == Dict(3 => -1)
        end

        # 4. Validation errors
        @test_throws ArgumentError coercive_field_ratios(ws_b; norm=0)
        @test_throws ArgumentError coercive_field_ratios(ws_b; norm=-1)
        @test_throws ArgumentError coercive_field_ratios(ws_b; norm=NaN)
        @test_throws ArgumentError coercive_field_ratios(ws_b; norm=true)
        @test_throws ArgumentError is_gauge_invariant(ws_b; atol=-1)
        @test_throws ArgumentError is_gauge_invariant(ws_b; atol=NaN)
        @test_throws ArgumentError is_gauge_invariant(ws_b; atol=false)
        @test_throws ArgumentError zero_field_fraction(ws_b; atol=-1)
        @test_throws ArgumentError trivial_dominance_fraction(ws_b; atol=-1)
        @test_throws ArgumentError coercive_field_witness(ws_b; max_flips=-1)
        @test_throws ArgumentError coercive_field_witness(ws_b; max_flips=true)
        @test_throws ArgumentError coercive_field_witness(ws_b; tie_break=:middle)
        @test_throws ArgumentError probe_variables!(ws_b; order=:random)
    end
end
