function exact_spin_oracle(L, Q, offset, domain)
    R = Rational{BigInt}
    n = length(L)
    if domain === :spin
        h = R.(L)
        J = [i < j ? R(Q[i,j]) : R(0) for i in 1:n, j in 1:n]
        return h, J, R(offset)
    end
    J = [i < j ? R(Q[i,j]) // 4 : R(0) for i in 1:n, j in 1:n]
    h = [R(L[i]) // 2 + sum((R(Q[min(i,j),max(i,j)]) // 4 for j in 1:n if j != i); init=R(0)) for i in 1:n]
    c = R(offset) + sum(R.(L); init=R(0)) // 2 + sum(J; init=R(0))
    return h, J, c
end

function exact_mapped_oracle(L, Q, offset, src_domain, target_domain, gauge)
    R = Rational{BigInt}
    n = length(L)
    h, J, c_spin = exact_spin_oracle(L, Q, offset, src_domain)
    h_g = [gauge[i] * h[i] for i in 1:n]
    J_g = [i < j ? gauge[i] * gauge[j] * J[i,j] : R(0) for i in 1:n, j in 1:n]
    if target_domain === :spin
        return h_g, J_g, c_spin
    end
    b_g = 4 .* J_g
    a_g = [2 * h_g[i] - 2 * sum((J_g[min(i,j),max(i,j)] for j in 1:n if j != i); init=R(0)) for i in 1:n]
    c_bool = c_spin - sum(h_g; init=R(0)) + sum(J_g; init=R(0))
    return a_g, b_g, c_bool
end

@testset "domain and gauge bijections across all states and conditioned scopes" begin
    labels = [(4, "d"), (1, "a"), (3, "c"), (2, "isolate")]
    L = [0.75, -1.25, 0.5, 0.0]
    Q = [0.0 -1.5 0.5 0.0; 0.0 0.0 1.0 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]
    gauges = ([1, 1, 1, 1], [-1, 1, -1, 1], [-1, -1, -1, -1], Dict(labels[1] => -1, labels[3] => -1))
    R = Rational{BigInt}
    for kind in (:sparse, :dense, :dict), src_dom in (:bool, :spin),
        dst_dom in (:bool, :spin), sense in (:min, :max),
        scale in (-2.0, 0.0, 0.5), gspec in gauges
        model = fixture(labels, L, Q; kind, domain=src_dom, sense, scale, offset=0.375)
        ws = Workspace(model; rules=:dominance)
        m = domain_map(ws; domain=dst_dom, gauge=gspec)
        @test generation(m) == generation(ws)
        @test original_variables(m) == labels
        @test m.source_domain === src_dom
        @test m.target_domain === dst_dom
        @test m.sense === sense
        @test m.scale == scale
        @test m.offset == 0.375
        g = collect(m.gauge)
        exp_L, exp_Q, exp_c = exact_mapped_oracle(L, Q, 0.375, src_dom, dst_dom, g)
        @test conditioned_constant(ws; map=m) == exp_c
        for i in 1:4
            @test effective_field(ws, labels[i]; map=m) == exp_L[i]
            couplings = Dict(incident_couplings(ws, labels[i]; map=m))
            for j in 1:4
                i == j && continue
                expected_q = exp_Q[min(i,j), max(i,j)]
                if iszero(expected_q)
                    @test !haskey(couplings, labels[j])
                else
                    @test couplings[labels[j]] == expected_q
                end
            end
        end
        for x in states(4, src_dom)
            y = map_state(m, x)
            @test lift_state(m, y) == x
            for i in 1:4
                @test map_value(m, labels[i], x[i]) == y[i]
                @test lift_value(m, labels[i], y[i]) == x[i]
            end
            @test reference(exp_L, exp_Q, scale, exp_c, y, R) ==
                  reference(L, Q, scale, 0.375, x, R)
        end
        # Check conditioned export + lifting in mapped coordinates.
        root = checkpoint(ws)
        low_src = src_dom === :bool ? 0 : -1
        assume!(ws, labels[2], low_src)
        propagate!(ws; map=m)
        res = materialize(ws, m; coefficient_type=R)
        out = export_model(res)
        @test QT.domain(out) == (dst_dom === :bool ? QT.BoolDomain : QT.SpinDomain)
        @test QT.sense(out) == (sense === :min ? QT.Min : QT.Max)
        free = [i for i in 1:4 if ws._state.fixed[i] == 2]
        @test QT.variables(out) == labels[free]
        for y_free in states(length(free), dst_dom)
            rec = reconstruct(res, y_free)
            energy = R(QT.offset(out))
            for j in eachindex(y_free)
                energy += R(linear(out)[j]) * y_free[j]
                for k in j+1:length(y_free)
                    energy += R(quadratic(out)[j,k]) * y_free[j] * y_free[k]
                end
            end
            energy *= R(QT.scale(out))
            @test energy == reference(L, Q, scale, 0.375, rec.state, R)
        end
        rollback!(ws, root)
        @test conditioned_constant(ws; map=m) == exp_c
    end
end

@testset "floating cast abstention, exact fallback and subnormal/overflow bounds" begin
    R = Rational{BigInt}
    # 1. Accumulation during bool -> spin: h_1 = 1/2 + 2^-54 rounds in Float64.
    m_acc = fixture([:x, :y], [1.0, 0.0], [0.0 2.0^-52; 0.0 0.0]; domain=:bool)
    ws_acc = Workspace(m_acc)
    spin_map = domain_map(ws_acc; domain=:spin)
    @test effective_field(ws_acc, :x; map=spin_map) == 1//2 + big(1)//big(2)^54
    @test_throws ArgumentError materialize(ws_acc, spin_map)
    exact_res = materialize(ws_acc, spin_map; coefficient_type=R)
    @test linear(export_model(exact_res))[1] == 1//2 + big(1)//big(2)^54

    # 2. Subnormal underflow during bool -> spin: b_12 = nextfloat(0.0) => J_12 = b_12/4 underflows Float64.
    tiny = nextfloat(0.0)
    m_sub = fixture([:x, :y], [0.0, 0.0], [0.0 tiny; 0.0 0.0]; domain=:bool)
    ws_sub = Workspace(m_sub)
    sub_map = domain_map(ws_sub; domain=:spin)
    @test Float64(tiny / 4) == 0.0
    @test_throws ArgumentError materialize(ws_sub, sub_map)
    sub_exact = export_model(materialize(ws_sub, sub_map; coefficient_type=R))
    @test quadratic(sub_exact)[1,2] == R(tiny) // 4

    # 3. Overflow during spin -> bool: J_12 = floatmax(Float64)/2 => b_12 = 4*J_12 overflows Float64.
    big_val = floatmax(Float64) / 2
    m_ovf = fixture([:x, :y], [0.0, 0.0], [0.0 big_val; 0.0 0.0]; domain=:spin)
    ws_ovf = Workspace(m_ovf)
    bool_map = domain_map(ws_ovf; domain=:bool)
    @test_throws ArgumentError materialize(ws_ovf, bool_map)
    ovf_exact = export_model(materialize(ws_ovf, bool_map; coefficient_type=R))
    @test quadratic(ovf_exact)[1,2] == 4 * R(big_val)

    # 4. Mapped dominance witness handles subnormal underflow and exact fallback.
    m_dom = fixture([:x, :y], [tiny, 0.0], [0.0 tiny; 0.0 0.0]; domain=:bool)
    ws_dom = Workspace(m_dom)
    dmap = domain_map(ws_dom; domain=:spin, gauge=[-1, 1])
    @test prove_dominance(ws_dom, :x; map=dmap, max_exact_work=0).stop_reason === :verification_limit
    attempt = prove_dominance(ws_dom, :x; map=dmap)
    @test attempt.stop_reason === :proved
    @test attempt.method === :exact
    @test only(attempt.certificate.steps).value == 0
    @test verify_certificate(ws_dom, attempt.certificate; map=dmap).valid
end

@testset "domain-transported proof verification and rejection of wrong gauge, stale map or ordering" begin
    labels = [:x, :y, :z]
    L = [3.0, 1.0, 0.0]
    Q = [0.0 -2.0 0.0; 0.0 0.0 0.5; 0.0 0.0 0.0]
    model = fixture(labels, L, Q; domain=:bool, offset=0.25)
    ws = Workspace(model; rules=:dominance)
    smap = domain_map(ws; domain=:spin, gauge=[-1, 1, -1])
    bmap_g = domain_map(ws; domain=:bool, gauge=[-1, 1, -1])
    bmap_id = domain_map(ws; domain=:bool)

    attempt = prove_dominance(ws, :x; map=smap)
    @test attempt.stop_reason === :proved
    cert_spin = attempt.certificate
    @test verify_certificate(ws, cert_spin).valid
    @test verify_certificate(ws, cert_spin; map=smap).valid

    # Transport certificate across domain and gauge representations.
    cert_bool_g = transport_certificate(ws, cert_spin, bmap_g)
    @test verify_certificate(ws, cert_bool_g).valid
    @test verify_certificate(ws, cert_bool_g; map=bmap_g).valid
    cert_bool_id = transport_certificate(ws, cert_bool_g, bmap_id)
    @test verify_certificate(ws, cert_bool_id).valid
    @test verify_certificate(ws, cert_bool_id; map=bmap_id).valid

    # Reject wrong gauge or wrong domain map.
    wrong_gauge = domain_map(ws; domain=:spin, gauge=[1, 1, -1])
    @test verify_certificate(ws, cert_spin; map=wrong_gauge).stop_reason === :invalid_gauge
    @test verify_certificate(ws, cert_spin; map=bmap_g).stop_reason === :invalid_map
    raw_cert = prove_dominance(ws, :x).certificate
    @test verify_certificate(ws, raw_cert; map=smap).stop_reason === :invalid_map
    @test verify_certificate(ws, raw_cert; map=bmap_g).stop_reason === :invalid_gauge

    # Tampered gauge inside certificate map is rejected by polynomial verification.
    forged_map = DomainGaugeMap(smap.generation, smap.source_domain, smap.target_domain,
        smap.sense, smap.scale, smap.offset, (1, 1, -1), smap._label_map, smap._source)
    forged_cert = DominanceCertificate(cert_spin.generation, cert_spin._scope_checkpoint,
        cert_spin.assumptions, cert_spin.steps, cert_spin._source, forged_map)
    @test verify_certificate(ws, forged_cert).stop_reason === :invalid_bound

    # Mismatched variable ordering / labels or stale generation is rejected.
    reordered = Workspace(fixture([:y, :x, :z], L, Q; domain=:bool, offset=0.25))
    reordered_map = DomainGaugeMap(generation(ws), :bool, :spin, :min, 1.0, 0.25,
        (-1, 1, -1), reordered._state.labels, reordered._snapshot)
    @test_throws ArgumentError prove_dominance(ws, :x; map=reordered_map)
    @test_throws ArgumentError transport_certificate(ws, cert_spin, reordered_map)
    @test verify_certificate(ws, cert_spin; map=reordered_map).stop_reason === :different_source

    other_ws = Workspace(model; rules=:dominance)
    other_map = domain_map(other_ws; domain=:spin, gauge=[-1, 1, -1])
    @test_throws ArgumentError prove_dominance(ws, :x; map=other_map)
    @test_throws ArgumentError propagate!(ws; map=other_map)
    @test_throws ArgumentError materialize(ws, other_map)
    @test verify_certificate(ws, cert_spin; map=other_map).stop_reason === :stale_generation

    # Multi-step cascade export and verification in mapped coordinates.
    root = checkpoint(ws)
    assume!(ws, :z, 1)
    propagate!(ws; map=smap)
    casc_cert = export_certificate(ws; map=smap)
    @test length(casc_cert.steps) == 2
    @test verify_certificate(ws, casc_cert; map=smap).valid
    rollback!(ws, root)
    @test verify_certificate(ws, casc_cert; map=smap).stop_reason === :stale_scope

    # Invalid domain/gauge construction refusals.
    @test_throws ArgumentError domain_map(ws; domain=:ising)
    @test_throws ArgumentError domain_map(ws; gauge=[1, -1])
    @test_throws ArgumentError domain_map(ws; gauge=[1, 0, 1])
    @test_throws ArgumentError domain_map(ws; gauge=[true, false, true])
    @test_throws ArgumentError domain_map(ws; gauge=Dict(:unknown => -1))
    @test_throws ArgumentError domain_map(ws; gauge=Dict(:x => 2))
    @test_throws ArgumentError domain_map(ws; gauge=:invalid)
    @test_throws ArgumentError map_value(smap, :unknown, 1)
    @test_throws ArgumentError map_value(smap, :x, -1)
    @test_throws ArgumentError lift_value(smap, :x, 0)
    @test_throws ArgumentError map_state(smap, [1, 0])
    @test_throws ArgumentError lift_state(smap, [1, -1])
end

@testset "degree tracking, field separation and cross-domain dominance equivalence" begin
    # Stored zero quadratic term in sparse storage must not inflate degree.
    m = fixture([:a, :b, :c, :isolate], [2.5, -1.0, 0.5, 4.0], zeros(4, 4))
    m.form = QT.Form{Float64}(4,
        QT.SparseLinearForm{Float64}(SparseVector(4, [1, 2, 3, 4], [2.5, -1.0, 0.5, 4.0])),
        QT.SparseQuadraticForm{Float64}(SparseMatrixCSC(4, 4, [1, 1, 2, 4, 5], [1, 1, 2, 3], [1.0, -0.5, 0.75, -0.0])))
    ws = Workspace(m; rules=:dominance)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [2, 2, 2, 0]
    @test effective_field(ws, :isolate) == 4
    @test isempty(incident_couplings(ws, :isolate))
    root = checkpoint(ws)
    assume!(ws, :a, 1)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [0, 1, 1, 0]
    @test_throws ArgumentError effective_field(ws, :a)
    @test_throws ArgumentError incident_couplings(ws, :a)
    assume!(ws, :b, 0)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [0, 0, 0, 0]
    unfix!(ws, :a)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [1, 0, 1, 0]
    reset!(ws, m)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [2, 2, 2, 0]
    cp = checkpoint(ws)
    assume!(ws, :c, 1)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [1, 1, 0, 0]
    rollback!(ws, cp)
    @test [degree(ws, v) for v in (:a, :b, :c, :isolate)] == [2, 2, 2, 0]

    # Equivalent strict dominance across domains and gauges; tie cases abstain.
    tie_bool = Workspace(fixture([:x, :y], [1.0, 0.0], [0.0 -1.0; 0.0 0.0]; domain=:bool); rules=:dominance)
    tie_map = domain_map(tie_bool; domain=:spin, gauge=[-1, 1])
    @test prove_dominance(tie_bool, :x).stop_reason === :not_strict
    @test prove_dominance(tie_bool, :x; map=tie_map).stop_reason === :not_strict
    @test propagate!(tie_bool; map=tie_map).deductions == 0
end

function mapped_local_cycle(ws, cp, m)
    d0 = degree(ws, 2)
    f0 = effective_field(ws, 2; map=m)
    c0 = conditioned_constant(ws; map=m)
    r = assume!(ws, 1, 1)
    d1 = degree(ws, 2)
    f1 = effective_field(ws, 2; map=m)
    c1 = conditioned_constant(ws; map=m)
    couplings = incident_couplings(ws, 2; map=m)
    _, reason, _, visits, _, _ = QUBOPreprocessing._dominance_witness(ws, 2; map=m, max_work=4, max_exact_work=4)
    p = propagate!(ws; map=m, max_work=16, max_exact_work=32)
    rollback!(ws, cp)
    return (r.edge_visits, reason, visits, p.deductions, length(couplings), d0, d1, f0 != f1, c0 == c1)
end

@testset "mapped local queries and updates do not scale with untouched graph" begin
    small = Workspace(sparse_chain(10); rules=:dominance)
    large = Workspace(sparse_chain(2000); rules=:dominance)
    @test propagate!(small).deductions == propagate!(large).deductions == 0
    ms = domain_map(small; domain=:spin, gauge=[isodd(i) ? -1 : 1 for i in 1:10])
    ml = domain_map(large; domain=:spin, gauge=[isodd(i) ? -1 : 1 for i in 1:2000])
    cps, cpl = checkpoint(small), checkpoint(large)
    for _ in 1:3
        mapped_local_cycle(small, cps, ms)
        mapped_local_cycle(large, cpl, ml)
    end
    res_s = mapped_local_cycle(small, cps, ms)
    res_l = mapped_local_cycle(large, cpl, ml)
    @test res_s == res_l == (1, :proved, 2, 1, 1, 2, 1, true, false)
    bytes_s = @allocated mapped_local_cycle(small, cps, ms)
    bytes_l = @allocated mapped_local_cycle(large, cpl, ml)
    @test bytes_l <= bytes_s + 2048
end
