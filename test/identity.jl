linear(model) = QT.linear_form(model isa QT.AbstractModel ? QT.form(model) : model)
quadratic(model) = QT.quadratic_form(model isa QT.AbstractModel ? QT.form(model) : model)

# Independent inputs: constructors below install already represented data,
# so the oracle neither conditions nor reads terms from a production export.
function fixture(labels, L, Q; kind=:sparse, scale=1.0, offset=0.0, sense=:min, domain=:bool)
    n = length(labels)
    if kind === :sparse
        lf = QT.SparseLinearForm{Float64}(sparse(L))
        qf = QT.SparseQuadraticForm{Float64}(sparse(Q))
    elseif kind === :dense
        lf = QT.DenseLinearForm{Float64}(copy(L))
        qf = QT.DenseQuadraticForm{Float64}(UpperTriangular(copy(Q)))
    else
        lf = QT.DictLinearForm{Float64}(Dict(i=>L[i] for i in 1:n))
        qf = QT.DictQuadraticForm{Float64}(Dict((i,j)=>Q[i,j] for i in 1:n for j in i+1:n))
    end
    V = eltype(labels)
    vm = QT.VariableMap{V}(Dict(v=>i for (i,v) in enumerate(labels)), copy(labels))
    f = QT.Form{Float64}(n, lf, qf, scale, offset; sense, domain)
    return QT.Model{V,Float64,Int}(vm, f)
end

# Guard BEFORE exponentiation/allocation. Only tiny independent fixtures run.
function states(n, domain)
    0 <= n <= 8 || throw(ArgumentError("tiny oracle accepts at most eight variables"))
    low = domain === :bool ? 0 : -1
    return ([iszero((mask >> (i-1)) & 1) ? low : 1 for i in 1:n] for mask in 0:(2^n-1))
end

function reference(L, Q, alpha, beta, x, T=Float64)
    c(v) = T === Rational{BigInt} ? Rational{BigInt}(v) : T(v)
    total = c(beta)
    for i in eachindex(x)
        total += c(L[i]) * x[i]
        for j in i+1:length(x)
            total += c(Q[i,j]) * x[i] * x[j]
        end
    end
    return c(alpha) * total
end

function exact_model_energy(model, x)
    # Extract individual coefficients, then use exact binary-value rationals;
    # this never calls the implementation's numerical energy evaluator.
    f = QT.form(model)
    lf, qf = linear(f), quadratic(f)
    n = QT.dimension(model)
    L = [lf[i] for i in 1:n]
    Q = zeros(Float64, n, n)
    for i in 1:n, j in i+1:n
        Q[i,j] = qf[i,j]
    end
    return reference(L, Q, QT.scale(model), QT.offset(model), x, Rational{BigInt})
end

@testset "identity matrix" begin
    @test_throws ArgumentError states(9, :bool)
    labels = ["last", "first", "isolated"]
    for kind in (:sparse, :dense, :dict), domain in (:bool, :spin),
        sense in (:min, :max), alpha in (1.0, -1.0, 2.5, -0.25, 0.0, -0.0),
        n in (0, 1, 3), constant in (false, true)
        L = n == 3 ? [0.75, -1.125, 0.0] : fill(0.75, n)
        Q = zeros(Float64, n, n)
        n == 3 && (Q[1,2] = 0.375)
        constant && (fill!(L, 0.0); fill!(Q, 0.0))
        beta = 1.625
        model = fixture(labels[1:n], L, Q; kind, scale=alpha, offset=beta, sense, domain)
        ws, report = preprocess(model; rules=:identity)
        @test report.rules === :identity
        @test report.stop_reason === :quiescent
        @test report.deductions == report.assumptions == 0
        @test report.generation == generation(ws)
        result = materialize(ws)
        @test result.status === :certified
        @test result.certificate == (scope=:original, reduction_chain=(), unchanged_representation=true)
        @test generation(result) == generation(ws)
        out = export_model(result)
        @test original_variables(result) == labels[1:n] == QT.variables(out)
        @test index_map(result) == collect(1:n)
        @test QT.dimension(out) == n
        @test typeof(QT.form(out)) == typeof(QT.form(model))
        @test isequal(QT.data(linear(out)), QT.data(linear(model)))
        @test isequal(QT.data(quadratic(out)), QT.data(quadratic(model)))
        @test isequal(QT.scale(out), alpha)
        @test isequal(QT.offset(out), beta)
        @test QT.sense(out) == QT.sense(model)
        @test QT.domain(out) == QT.domain(model)
        for x in states(n, domain)
            rec = reconstruct(result, x)
            @test rec.state == x
            @test rec.state !== x
            @test rec.generation == generation(result)
            @test rec.energy.method === :float64
            @test rec.energy.finite
            @test rec.energy.value == reference(L, Q, alpha, beta, x)
            @test exact_model_energy(out, x) == reference(L, Q, alpha, beta, x, Rational{BigInt})
        end
    end
end

@testset "exact stored Float64 boundary values" begin
    # Include signed stored zeros, subnormal, adjacent floats, cancellation,
    # large finite coefficients and under/overflow of ordinary evaluation.
    for kind in (:sparse, :dense, :dict)
        L = [-0.0, nextfloat(0.0), prevfloat(1.0), -floatmax(Float64)]
        Q = zeros(4,4)
        Q[1,2] = -0.0
        Q[2,3] = nextfloat(1.0)
        Q[3,4] = floatmax(Float64)
        m = fixture([:d, :b, :c, :a], L, Q; kind, scale=2.0, offset=-0.0)
        r = materialize(Workspace(m))
        out = export_model(r)
        @test isequal(QT.data(linear(out)), QT.data(linear(m)))
        @test isequal(QT.data(quadratic(out)), QT.data(quadratic(m)))
        for x in states(4, :bool)
            @test exact_model_energy(out, x) == reference(L,Q,2.0,-0.0,x,Rational{BigInt})
        end
        rec = reconstruct(r, [0,0,0,1])
        @test !rec.energy.finite
        @test isinf(rec.energy.value)
    end
    # Raw explicitly stored sparse signed zeros must not be dropped.
    m = fixture([7,3], zeros(2), zeros(2,2))
    m.form = QT.Form{Float64}(2,
        QT.SparseLinearForm{Float64}(SparseVector(2, [1], [-0.0])),
        QT.SparseQuadraticForm{Float64}(SparseMatrixCSC(2,2,[1,1,2],[1],[-0.0])))
    out = export_model(materialize(Workspace(m)))
    @test isequal(nonzeros(QT.data(linear(out))), [-0.0])
    @test isequal(nonzeros(QT.data(quadratic(out))), [-0.0])
end

@testset "ownership and transactional generation" begin
    for kind in (:sparse, :dense, :dict)
        m = fixture(["z", "a", "isolate"], [1.0,-2.0,0.0], [0.0 0.5 0.0; 0.0 0.0 0.0; 0.0 0.0 0.0]; kind)
        ws = Workspace(m)
        other = Workspace(m)
        @test generation(ws) != generation(other)
        historical = materialize(ws)
        old = generation(ws)
        linear(m)[1] = 20.0
        quadratic(m)[1,2] = -4.0
        QT.variables(m)[1] = "caller edit"
        m.metadata["unrelated"] = [1]
        @test original_variables(ws) == ["z","a","isolate"]
        @test reconstruct(historical, [1,0,0]).energy.value == 1.0
        out = export_model(historical)
        linear(out)[1] = 99.0
        QT.variables(out)[1] = "export edit"
        out.metadata["new"] = [2]
        @test linear(export_model(historical))[1] == 1.0
        @test QT.variables(export_model(historical))[1] == "z"
        vars = original_variables(ws)
        vars[1] = "query edit"
        map = index_map(historical)
        map[1] = 3
        @test index_map(historical) == [1,2,3]
        @test original_variables(ws)[1] == "z"
        bad = fixture(["z","a","isolate"], [NaN,0.0,0.0], zeros(3,3); kind)
        @test_throws ArgumentError reset!(ws, bad)
        @test generation(ws) == old
        @test reconstruct(materialize(ws), [1,0,0]).energy.value == 1.0
        new = fixture(["z","a","isolate"], [2.0,-2.0,0.0], zeros(3,3); kind)
        @test reset!(ws, new) === ws
        @test generation(ws) != old
        @test generation(ws).workspace == old.workspace
        @test reconstruct(materialize(ws), [1,0,0]).energy.value == 2.0
        @test generation(historical) == old
        @test reconstruct(historical, [1,0,0]).energy.value == 1.0
        latest = generation(ws)
        relabeled = fixture(["a","z","isolate"], [2.0,-2.0,0.0], zeros(3,3); kind)
        reset!(ws, relabeled)
        @test generation(ws) != latest
        @test original_variables(ws) == ["a","z","isolate"]
        latest = generation(ws)
        reset!(ws, relabeled)
        @test generation(ws) != latest
        rec = reconstruct(historical, [1,0,0])
        rec.state[1] = 0
        @test reconstruct(historical, [1,0,0]).state == [1,0,0]
        QT.empty!(out)
        @test QT.dimension(export_model(historical)) == 3
    end
    # Tuple labels retain original order, without sorting.
    m = fixture([(3,"z"),(1,"a")], [0.0,1.0], zeros(2,2))
    @test original_variables(materialize(Workspace(m))) == [(3,"z"),(1,"a")]
end

@testset "explicit refusals" begin
    m = fixture([:x,:y], [1.0,0.0], zeros(2,2))
    for rules in (:unknown, (), nothing)
        @test_throws ArgumentError Workspace(m; rules)
        @test_throws ArgumentError preprocess(m; rules)
    end
    @test_throws ArgumentError Workspace(nothing)
    @test_throws ArgumentError Workspace(QT.Model(Dict(:x=>1.0f0), Dict{Tuple{Symbol,Symbol},Float32}()))
    @test_throws ArgumentError Workspace(QT.Model(Dict(:x=>1//2), Dict{Tuple{Symbol,Symbol},Rational{Int}}()))
    @test_throws ArgumentError materialize(Workspace(m); coefficient_type=Float32)
    for kind in (:sparse, :dense, :dict), v in (Inf, -Inf, NaN)
        @test_throws ArgumentError Workspace(fixture([:x,:y], [v,0.0], zeros(2,2); kind))
        Q = [0.0 v; 0.0 0.0]
        @test_throws ArgumentError Workspace(fixture([:x,:y], [1.0,0.0], Q; kind))
        @test_throws ArgumentError Workspace(fixture([:x,:y], [1.0,0.0], zeros(2,2); kind, scale=v))
        @test_throws ArgumentError Workspace(fixture([:x,:y], [1.0,0.0], zeros(2,2); kind, offset=v))
    end
    for domain in (:bool, :spin)
        r = materialize(Workspace(fixture([:x,:y], [1.0,0.0], zeros(2,2); domain)))
        low = domain === :bool ? 0 : -1
        for y in ([1], [1,low,1], [1,missing], [1,nothing], [1,NaN], [1,Inf], [1,2], [1,0.5], [1,"1"], [1,1+0im])
            @test_throws ArgumentError reconstruct(r,y)
        end
        @test_throws ArgumentError reconstruct(r, Dict(:x=>1,:y=>low))
        @test reconstruct(r, [1.0,Float64(low)]).state == [1,low]
    end
    for kind in (:sparse, :dense)
        @test_throws ArgumentError Workspace(fixture([:x], [0.0], ones(1,1); kind))
    end
    # Dict fixture omits diagonal by construction; install malformed raw data.
    d = fixture([:x], [0.0], zeros(1,1); kind=:dict)
    QT.data(quadratic(d))[(1,1)] = 1.0
    @test_throws ArgumentError Workspace(d)
    d = fixture([:x,:x], [0.0,0.0], zeros(2,2))
    @test_throws ArgumentError Workspace(d)
    m.variable_map.map[:x] = 2
    @test_throws ArgumentError Workspace(m)
end

@testset "integerize_scale and is_integer_scaled (#51, #87)" begin
    # 1. Issue #87 reproducer: f(x) = 0.3*x1 + 0.6*x2 - 0.9*x1*x2 has unique exact binary64
    #    minimizer x = (1, 1) with f(1, 1) = -2^-54 < 0. Default integerize_scale (atol = 0.0)
    #    must be exact (no Float64 product 0.9 * 10 == 9.0, no tolerance), leaving non-dyadic
    #    decimal coefficients unchanged so preprocess returns x = [1, 1] with a valid certificate.
    f_87 = QT.Form{Float64}(
        2,
        QT.DenseLinearForm{Float64}([0.3, 0.6]),
        QT.DictQuadraticForm{Float64}(Dict((1, 2) => -0.9)),
        1.0,
        0.0;
        sense = :min,
        domain = :bool,
    )
    m_87 = QT.Model{Int,Float64,Int}(QT.VariableMap{Int}(Dict(1 => 1, 2 => 2), [1, 2]), f_87)
    for m_unpert in (integerize_scale(m_87), integerize_scale(m_87; atol = 0.0), integerize_scale(m_87; atol = 1e-20))
        @test !is_integer_scaled(m_unpert)
        @test QT.scale(m_unpert) == 1.0
        @test Dict(QT.linear_terms(m_unpert)) == Dict(1 => 0.3, 2 => 0.6)
        @test Dict(QT.quadratic_terms(m_unpert)) == Dict((1, 2) => -0.9)
    end
    for kw in ((;), (integerize_scale = true,), (atol = 0.0,), (atol = 1e-20,), (integerize_scale = false,))
        ws_87, _ = preprocess(m_87; rules = :mixed, kw...)
        @test !ws_87.perturbed
        @test iszero(ws_87.max_perturbation)
        mat_87 = materialize(ws_87; coefficient_type = Rational{BigInt})
        @test !mat_87.perturbed
        @test iszero(mat_87.max_perturbation)
        n_res = QT.dimension(export_model(mat_87))
        @test n_res == 0
        x_87 = Int.(reconstruct(mat_87, zeros(Int, n_res)).state)
        @test x_87 == [1, 1]
        cert_87 = export_certificate(ws_87)
        @test cert_87 !== nothing
        @test !cert_87.perturbed
        @test iszero(cert_87.max_perturbation)
        @test verify_certificate(ws_87, cert_87).valid
    end

    function effective_perturbation(m_in, m_out)
        R = Rational{BigInt}
        s_in = R(QT.scale(m_in))
        s_out = R(QT.scale(m_out))
        max_err = abs(s_out * R(QT.offset(m_out)) - s_in * R(QT.offset(m_in)))
        lin_in = Dict{Int,Float64}(QT.linear_terms(m_in))
        lin_out = Dict{Int,Float64}(QT.linear_terms(m_out))
        for i in 1:QT.dimension(m_in)
            err = abs(s_out * R(get(lin_out, i, 0.0)) - s_in * R(get(lin_in, i, 0.0)))
            err > max_err && (max_err = err)
        end
        quad_in = Dict{Tuple{Int,Int},Float64}(QT.quadratic_terms(m_in))
        quad_out = Dict{Tuple{Int,Int},Float64}(QT.quadratic_terms(m_out))
        for ij in union(keys(quad_in), keys(quad_out))
            err = abs(s_out * R(get(quad_out, ij, 0.0)) - s_in * R(get(quad_in, ij, 0.0)))
            err > max_err && (max_err = err)
        end
        return max_err
    end

    # Explicit opt-in tolerance-based rounding (atol = 1e-12) on the #87 reproducer:
    # records perturbed = true and the exact largest absolute effective-coefficient change
    # (including stored scale) on Workspace, ExportResult/ConditionedExport, and DominanceCertificate.
    expected_pert_87 = max(
        abs(Rational{BigInt}(0.1) * 3 - Rational{BigInt}(1.0) * Rational{BigInt}(0.3)),
        abs(Rational{BigInt}(0.1) * 6 - Rational{BigInt}(1.0) * Rational{BigInt}(0.6)),
        abs(Rational{BigInt}(0.1) * (-9) - Rational{BigInt}(1.0) * Rational{BigInt}(-0.9)),
    )
    @test expected_pert_87 == 1 // 18014398509481984
    ws_87_id = Workspace(m_87; integerize_scale = true, atol = 1e-12)
    @test ws_87_id.perturbed
    @test ws_87_id.max_perturbation == expected_pert_87
    @test effective_perturbation(m_87, export_model(materialize(ws_87_id))) == expected_pert_87
    ws_87_opt, _ = preprocess(m_87; rules = :mixed, atol = 1e-12)
    @test ws_87_opt.perturbed
    @test ws_87_opt.max_perturbation == expected_pert_87
    cert_87_opt = export_certificate(ws_87_opt)
    @test cert_87_opt !== nothing
    @test cert_87_opt.perturbed
    @test cert_87_opt.max_perturbation == expected_pert_87
    @test verify_certificate(ws_87_opt, cert_87_opt).valid
    mat_87_opt = materialize(ws_87_opt; coefficient_type = Rational{BigInt})
    @test mat_87_opt.perturbed
    @test mat_87_opt.max_perturbation == expected_pert_87
    @test !mat_87_opt.certificate.unchanged_representation
    @test mat_87_opt.certificate.proof.perturbed
    @test mat_87_opt.certificate.proof.max_perturbation == expected_pert_87
    exp_87_id = materialize(ws_87_id)
    @test exp_87_id isa ExportResult
    @test mat_87_opt isa ConditionedExport
    for x in (ws_87_opt, exp_87_id, mat_87_opt)
        @test :perturbed in propertynames(x) && :max_perturbation in propertynames(x)
        @test :_snapshot ∉ propertynames(x)
        @test :_snapshot in propertynames(x, true)
        @test all(p -> (getproperty(x, p); true), propertynames(x, true))
    end

    # Stored-scale rounding in opt-in decimal path:
    # - [0.1, 1e12] at scale 1.0 -> stored [1.0, 1e13] at scale 0.1; effective change on 1e12 is ~5.55e-5.
    # - Single coefficient [0.2] at scale 1.0 -> stored [1.0] at scale 0.2; exact objective is preserved
    #   (max_perturbation == 0 // 1, perturbed == false).
    # - Non-zero offset and non-unit scale included in effective perturbation.
    # - [0.9] with max_decimals = 53 integerizes exactly with m = 2^53 under default atol = 0.0.
    m_scale_amp = fixture([:x1, :x2], [0.1, 1e12], zeros(2, 2); domain = :bool, sense = :min, scale = 1.0, offset = 0.0)
    ws_scale_amp = Workspace(m_scale_amp; integerize_scale = true, atol = 1e-12)
    out_scale_amp = export_model(materialize(ws_scale_amp))
    @test QT.scale(out_scale_amp) == 0.1
    @test Dict(QT.linear_terms(out_scale_amp)) == Dict(1 => 1.0, 2 => 1e13)
    @test ws_scale_amp.perturbed
    @test ws_scale_amp.max_perturbation == 244140625 // 4398046511104
    @test ws_scale_amp.max_perturbation == effective_perturbation(m_scale_amp, out_scale_amp)

    m_offset_amp = fixture([:x1], [0.1], zeros(1, 1); domain = :bool, sense = :min, scale = -2.5, offset = 1e12)
    ws_offset_amp = Workspace(m_offset_amp; integerize_scale = true, atol = 1e-12)
    out_offset_amp = export_model(materialize(ws_offset_amp))
    @test ws_offset_amp.perturbed
    @test ws_offset_amp.max_perturbation == effective_perturbation(m_offset_amp, out_offset_amp)

    m_exact_02 = fixture([:x1], [0.2], zeros(1, 1); domain = :bool, sense = :min, scale = 1.0, offset = 0.0)
    ws_exact_02 = Workspace(m_exact_02; integerize_scale = true, atol = 1e-12)
    mat_exact_02 = materialize(ws_exact_02)
    out_exact_02 = export_model(mat_exact_02)
    @test is_integer_scaled(ws_exact_02)
    @test QT.scale(out_exact_02) == 0.2
    @test Dict(QT.linear_terms(out_exact_02)) == Dict(1 => 1.0)
    @test iszero(effective_perturbation(m_exact_02, out_exact_02))
    @test !ws_exact_02.perturbed
    @test iszero(ws_exact_02.max_perturbation)
    @test !mat_exact_02.perturbed
    @test iszero(mat_exact_02.max_perturbation)
    @test mat_exact_02.certificate.unchanged_representation

    m_dyadic_53 = fixture([:x1], [0.9], zeros(1, 1); domain = :bool, sense = :min)
    ws_dyadic_53 = Workspace(m_dyadic_53; integerize_scale = true, max_decimals = 53)
    out_dyadic_53 = export_model(materialize(ws_dyadic_53))
    @test is_integer_scaled(ws_dyadic_53)
    @test QT.scale(out_dyadic_53) == 2.0^-53
    @test iszero(effective_perturbation(m_dyadic_53, out_dyadic_53))
    @test !ws_dyadic_53.perturbed
    @test iszero(ws_dyadic_53.max_perturbation)

    # Tampering with perturbed / max_perturbation on a certificate is rejected by verify_certificate
    # and transport_certificate.
    forged_unpert = DominanceCertificate(
        cert_87_opt.generation,
        cert_87_opt._scope_checkpoint,
        cert_87_opt.assumptions,
        cert_87_opt.steps,
        cert_87_opt._source,
        cert_87_opt._map,
        false,
        zero(Rational{BigInt}),
    )
    @test verify_certificate(ws_87_opt, forged_unpert).stop_reason === :different_source
    forged_wrong_mag = DominanceCertificate(
        cert_87_opt.generation,
        cert_87_opt._scope_checkpoint,
        cert_87_opt.assumptions,
        cert_87_opt.steps,
        cert_87_opt._source,
        cert_87_opt._map,
        true,
        expected_pert_87 + (1 // 100),
    )
    @test verify_certificate(ws_87_opt, forged_wrong_mag).stop_reason === :different_source
    dmap_87 = domain_map(ws_87_opt; domain = :spin)
    @test_throws ArgumentError transport_certificate(ws_87_opt, forged_unpert, dmap_87)
    tcert_87_opt = transport_certificate(ws_87_opt, cert_87_opt, dmap_87)
    @test tcert_87_opt.perturbed
    @test tcert_87_opt.max_perturbation == expected_pert_87
    @test verify_certificate(ws_87_opt, tcert_87_opt; map = dmap_87).valid

    # 2. Coefficient within atol of a decimal (0.3 + 1e-13 and L_chimera = [-0.9, -1.7999999999999998, -0.9]):
    #    - Default (atol = 0.0) leaves the snapshot unchanged and unperturbed.
    #    - Explicit opt-in (atol = 1e-12) rounds into exact integers with scale = 0.1 and records perturbation.
    v_near_dec = 0.3 + 1e-13
    m_near_dec = fixture([:x1, :x2], [v_near_dec, 0.6], [0.0 -0.9; 0.0 0.0]; domain = :bool, sense = :min)
    @test !is_integer_scaled(integerize_scale(m_near_dec))
    ws_nd_exact = Workspace(m_near_dec; integerize_scale = true)
    @test !is_integer_scaled(ws_nd_exact)
    @test !ws_nd_exact.perturbed
    @test iszero(ws_nd_exact.max_perturbation)
    @test materialize(ws_nd_exact).certificate.unchanged_representation
    ws_nd_opt = Workspace(m_near_dec; integerize_scale = true, atol = 1e-12)
    @test is_integer_scaled(ws_nd_opt)
    @test ws_nd_opt.perturbed
    mat_nd_opt = materialize(ws_nd_opt)
    @test ws_nd_opt.max_perturbation == effective_perturbation(m_near_dec, export_model(mat_nd_opt))
    @test mat_nd_opt.perturbed
    @test mat_nd_opt.max_perturbation == ws_nd_opt.max_perturbation
    @test !mat_nd_opt.certificate.unchanged_representation

    L_chimera = [-0.9, -1.7999999999999998, -0.9]
    Q_chimera = [0.0 1.8 0.0; 0.0 0.0 1.8; 0.0 0.0 0.0]
    expected_pert_ch = max(
        abs(Rational{BigInt}(0.1) * (-9) - Rational{BigInt}(1.0) * Rational{BigInt}(-0.9)),
        abs(Rational{BigInt}(0.1) * (-18) - Rational{BigInt}(1.0) * Rational{BigInt}(-1.7999999999999998)),
        abs(Rational{BigInt}(0.1) * 18 - Rational{BigInt}(1.0) * Rational{BigInt}(1.8)),
    )
    for kind in (:sparse, :dense, :dict)
        m_ch = fixture([:x1, :x2, :x3], L_chimera, Q_chimera; kind, domain=:bool, sense=:min)
        @test !is_integer_scaled(m_ch)
        ws_raw = Workspace(m_ch)
        @test !is_integer_scaled(ws_raw)
        @test !is_gauge_invariant(ws_raw)
        @test !ws_raw.perturbed
        @test iszero(ws_raw.max_perturbation)

        # Default integerize_scale (atol = 0.0) leaves non-dyadic decimals unchanged
        m_ch_default = integerize_scale(m_ch)
        @test !is_integer_scaled(m_ch_default)
        @test QT.scale(m_ch_default) == 1.0
        ws_int_default = Workspace(m_ch; integerize_scale=true)
        @test !is_integer_scaled(ws_int_default)
        @test !ws_int_default.perturbed
        @test iszero(ws_int_default.max_perturbation)

        # Opt-in tolerance-based decimal rounding (atol = 1e-12)
        m_ch_int = integerize_scale(m_ch; atol=1e-12)
        @test is_integer_scaled(m_ch_int)
        @test QT.scale(m_ch_int) == 0.1
        @test Dict(QT.linear_terms(m_ch_int)) == Dict(1 => -9.0, 2 => -18.0, 3 => -9.0)
        @test Dict(ij => v for (ij, v) in QT.quadratic_terms(m_ch_int) if !iszero(v)) == Dict((1, 2) => 18.0, (2, 3) => 18.0)
        @test effective_perturbation(m_ch, m_ch_int) == expected_pert_ch

        # Workspace(...; integerize_scale=true, atol=1e-12) and reset!(...; integerize_scale=true, atol=1e-12)
        ws_int = Workspace(m_ch; integerize_scale=true, atol=1e-12)
        @test is_integer_scaled(ws_int)
        @test is_gauge_invariant(ws_int)
        @test zero_field_fraction(ws_int) == 1.0
        @test ws_int._snapshot.scale == 0.1
        @test ws_int.perturbed
        @test ws_int.max_perturbation == expected_pert_ch

        reset!(ws_raw, m_ch; integerize_scale=true, atol=1e-12)
        @test is_integer_scaled(ws_raw)
        @test is_gauge_invariant(ws_raw)
        @test ws_raw.perturbed
        @test ws_raw.max_perturbation == expected_pert_ch

        reset!(ws_raw, m_ch; integerize_scale=true)
        @test !is_integer_scaled(ws_raw)
        @test !ws_raw.perturbed
        @test iszero(ws_raw.max_perturbation)

        # preprocess(m_ch; rules=:identity) and default preprocess(m_ch; rules=:mixed) preserve exact binary64,
        # while preprocess(m_ch; rules=:mixed, atol=1e-12) opts into decimal rounding and records perturbation
        ws_id, _ = preprocess(m_ch; rules=:identity)
        @test !is_integer_scaled(ws_id)
        @test !ws_id.perturbed
        ws_mix_exact, _ = preprocess(m_ch; rules=:mixed)
        @test !is_integer_scaled(ws_mix_exact)
        @test !ws_mix_exact.perturbed
        @test iszero(ws_mix_exact.max_perturbation)

        ws_mix, rep_mix = preprocess(m_ch; rules=:mixed, atol=1e-12)
        @test is_integer_scaled(ws_mix)
        @test ws_mix._snapshot.scale == 0.1
        @test ws_mix.perturbed
        @test ws_mix.max_perturbation == expected_pert_ch
        mat_mix = materialize(ws_mix)
        @test QT.scale(export_model(mat_mix)) == 0.1
        @test mat_mix.perturbed
        @test mat_mix.max_perturbation == expected_pert_ch

        # Explicit override integerize_scale=false on rules=:mixed even when atol=1e-12 is passed
        ws_mix_raw, _ = preprocess(m_ch; rules=:mixed, integerize_scale=false, atol=1e-12)
        @test !is_integer_scaled(ws_mix_raw)
        @test !ws_mix_raw.perturbed
        @test iszero(ws_mix_raw.max_perturbation)
    end

    # 3. Sub-ulp near-tie perturbations on dyadic values must never be rounded away
    m_near = fixture([:x1, :x2, :x3], [-0.75 + 2.0^-53, -prevfloat(0.5), 0.0], [0.0 1.0 0.5; 0.0 0.0 0.0; 0.0 0.0 0.0])
    @test !is_integer_scaled(m_near)
    for m_near_out in (integerize_scale(m_near), integerize_scale(m_near; atol=1e-12))
        @test !is_integer_scaled(m_near_out)
        @test QT.scale(m_near_out) == 1.0
        @test Dict(QT.linear_terms(m_near_out)) == Dict(QT.linear_terms(m_near))
    end

    # 4. DenseQuadraticForm with non-integer entries in the masked lower triangle of UpperTriangular(A)
    A_int_upper = [0.0 2.0; 1.0 / 3.0 0.0]
    m_masked_int = fixture([:x1, :x2], [1.0, -3.0], A_int_upper; kind=:dense)
    @test is_integer_scaled(m_masked_int)
    @test is_integer_scaled(Workspace(m_masked_int))

    A_dyadic_upper = [0.0 0.5; 1.0 / 3.0 0.0]
    m_masked_dyadic = fixture([:x1, :x2], [0.25, -0.5], A_dyadic_upper; kind=:dense)
    @test !is_integer_scaled(m_masked_dyadic)
    m_masked_dyadic_int = integerize_scale(m_masked_dyadic)
    @test is_integer_scaled(m_masked_dyadic_int)
    @test QT.scale(m_masked_dyadic_int) == 0.25
    ws_masked_dyadic = Workspace(m_masked_dyadic; integerize_scale=true)
    @test is_integer_scaled(ws_masked_dyadic)
    @test !ws_masked_dyadic.perturbed
    @test iszero(ws_masked_dyadic.max_perturbation)

    # 5. Validation of kwargs and unsupported inputs
    m_ok = fixture([:x, :y], [0.5, -0.25], [0.0 0.75; 0.0 0.0]; offset=0.5, scale=2.0)
    @test is_integer_scaled(integerize_scale(m_ok))
    @test QT.scale(integerize_scale(m_ok)) == 0.5
    ws_ok = Workspace(m_ok; integerize_scale=true)
    @test is_integer_scaled(ws_ok)
    @test !ws_ok.perturbed
    @test iszero(ws_ok.max_perturbation)
    @test propertynames(ws_ok) == (:perturbed, :max_perturbation)
    @test_throws ArgumentError is_integer_scaled(nothing)
    @test_throws ArgumentError integerize_scale(nothing)
    @test_throws ArgumentError integerize_scale(m_ok; max_decimals=-1)
    @test_throws ArgumentError integerize_scale(m_ok; max_decimals=true)
    @test_throws ArgumentError integerize_scale(m_ok; atol=-1e-12)
    @test_throws ArgumentError integerize_scale(m_ok; atol=NaN)
    @test_throws ArgumentError integerize_scale(m_ok; atol=Inf)
    @test_throws ArgumentError integerize_scale(m_ok; atol=true)
    @test_throws ArgumentError Workspace(m_ok; integerize_scale=true, max_decimals=-1)
    @test_throws ArgumentError Workspace(m_ok; integerize_scale=true, atol=-1.0)
end

@testset "label and gauge tuples: linear scans without per-size recompilation" begin
    # Label validation reads tuple entries through the getfield builtin; generic
    # indexing on an n-parameter Tuple costs O(n) per access (~50s at n = 40k).
    big = Tuple(1:40_000)
    QUBOPreprocessing._validate_label_copy((1, 2), (1, 2))
    @test (@elapsed QUBOPreprocessing._validate_label_copy(big, deepcopy(big))) < 2.0
    @test_throws ArgumentError QUBOPreprocessing._validate_label_copy((1, 2), (1, 3))
    @test QUBOPreprocessing._ints((Int8(1), Int8(2), Int8(2))) == [1, 2, 2]

    function independent_workspace(n)
        m = QT.Model{Int,Float64,Int}(
            Dict{Int,Float64}(i => (isodd(i) ? 2.0 : -3.0) for i in 1:n),
            Dict{Tuple{Int,Int},Float64}(); sense=:min, domain=:bool)
        return Workspace(m; rules=:dominance)
    end
    # DomainGaugeMap does not compile a new constructor for every model size
    # (previously ~25s on the first call at n = 3000).
    domain_map(independent_workspace(10); domain=:spin)
    domain_map(independent_workspace(10); domain=:bool, gauge=[isodd(i) ? -1 : 1 for i in 1:10])
    ws_fresh = independent_workspace(3_001)
    @test (@elapsed domain_map(ws_fresh; domain=:spin, gauge=[isodd(i) ? -1 : 1 for i in 1:3_001])) < 10.0
    ws_fresh_bool = independent_workspace(3_002)
    @test (@elapsed domain_map(ws_fresh_bool; domain=:bool, gauge=[isodd(i) ? -1 : 1 for i in 1:3_002])) < 10.0
    p10 = QUBOPreprocessing._init_poly_state(independent_workspace(10)._snapshot)
    QUBOPreprocessing._verify_poly_witness_state(p10, Tuple(zeros(Int, 10)), Tuple{Int,Int}[], Any[], nothing)
    p_fresh = QUBOPreprocessing._init_poly_state(independent_workspace(3_003)._snapshot)
    w_fresh = Tuple(zeros(Int, 3_003))
    @test (@elapsed QUBOPreprocessing._verify_poly_witness_state(p_fresh, w_fresh, Tuple{Int,Int}[], Any[], nothing)) < 1.0

    # Export, verification and materialization stay linear at n = 20k
    # (previously ~14s each for export and materialize).
    n = 20_000
    ws = independent_workspace(n)
    @test propagate!(ws).deductions == n
    export_certificate(independent_workspace(3); map=nothing)
    t = @elapsed begin
        cert = export_certificate(ws)
        res = materialize(ws; coefficient_type=Rational{BigInt})
        bmap = domain_map(ws; domain=:spin)
    end
    @test t < 5.0
    @test length(cert.steps) == n
    @test verify_certificate(ws, cert).valid
    @test QT.dimension(export_model(res)) == 0
    @test bmap.gauge == Tuple(ones(Int, n))

    # Shared batch non-isbits tuples (e.g. roof-duality flow_edges) are deep-copied
    # once per batch in _proof_steps / reductions / deepcopy(cert) rather than O(k * M)
    # times, while remaining fully detached from workspace storage; isbits and Symbol
    # tuples return in O(1).
    t_bits = (1, 2, 3)
    @test QUBOPreprocessing._deepcopy_tuple(t_bits) === t_bits
    t_syms = (:a, :b, :c)
    @test QUBOPreprocessing._deepcopy_tuple(t_syms) === t_syms
    shared_flow = ((1, 2, Rational{BigInt}(3, 1)), (2, 3, Rational{BigInt}(5, 1)))
    c1 = QUBOPreprocessing._deepcopy_tuple(shared_flow)
    @test c1 !== shared_flow
    @test c1[1][3].num !== shared_flow[1][3].num

    m_roof = QT.Model{Int,Float64,Int}(
        Dict(1 => 2.0, 2 => 0.0, 3 => 0.0, 4 => 0.0, 5 => 0.0, 6 => 0.0),
        Dict(
            (1, 2) => -2.0, (1, 3) => -2.0, (2, 3) => -2.0,
            (3, 4) => 0.5,
            (4, 5) => 1.0, (5, 6) => 1.0, (4, 6) => 1.0,
        ); sense=:min, domain=:spin)
    ws_roof = Workspace(m_roof; rules=:mixed)
    rep_roof = apply_roof_duality!(ws_roof)
    @test length(rep_roof.fixings) == 3
    cert_roof = export_certificate(ws_roof)
    @test length(cert_roof.steps) == 3
    @test !isempty(cert_roof.steps[1].flow_edges)
    @test cert_roof.steps[1].flow_edges === cert_roof.steps[2].flow_edges
    @test cert_roof.steps[2].flow_edges === cert_roof.steps[3].flow_edges
    cert_roof_copy = deepcopy(cert_roof)
    @test cert_roof_copy.steps[1].flow_edges === cert_roof_copy.steps[2].flow_edges
    @test cert_roof_copy.steps[1].flow_edges !== cert_roof.steps[1].flow_edges
    res_roof = materialize(ws_roof)
    res_roof_copy = deepcopy(res_roof)
    @test res_roof_copy.certificate.reduction_chain === res_roof_copy.certificate.proof.steps
    @test res_roof_copy.certificate.reduction_chain[1].flow_edges === res_roof_copy.certificate.reduction_chain[2].flow_edges
    @test res_roof_copy.certificate.reduction_chain[1].flow_edges !== res_roof.certificate.reduction_chain[1].flow_edges
    @test verify_certificate(ws_roof, cert_roof).valid

    # Heterogeneous reduction chains (DominanceStep + EliminationStep + RelationStep)
    # materialize via type-erased _ConditionedCertNT without specializing NamedTuple
    # on a concrete K-element heterogeneous Tuple type.
    m_het = QT.Model{Int,Float64,Int}(
        Dict(1 => 5.0, 2 => 0.0, 3 => 0.0, 4 => 0.0),
        Dict((2, 3) => -2.0, (3, 4) => -2.0); sense=:min, domain=:bool)
    ws_het = Workspace(m_het; rules=:mixed)
    schedule_reductions!(ws_het; allow_weak_dominance=true, allow_weak_relations=true)
    res_het = materialize(ws_het)
    @test res_het.certificate.reduction_chain isa Tuple
    @test verify_certificate(ws_het, export_certificate(ws_het)).valid
end
