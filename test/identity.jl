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
    for rules in (:dominance, :unknown, (), nothing)
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
    for name in (:checkpoint, :assume!, :propagate!, :rollback!, :unfix!, :changes)
        @test !isdefined(QUBOPreprocessing, name)
    end
end
