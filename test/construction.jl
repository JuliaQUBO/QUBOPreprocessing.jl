# Independent scalar references for exact binary64 constructor state. Keep the
# fixtures tiny: these tests check algebra and fallback selection, not wall time.
function construction_fixture(L, Q; kind=:sparse, domain=:bool, scale=1.0, offset=0.3)
    n = length(L)
    labels = collect(1:n)
    lf, qf = if kind === :sparse
        QT.SparseLinearForm{Float64}(sparse(L)), QT.SparseQuadraticForm{Float64}(sparse(Q))
    elseif kind === :dense
        QT.DenseLinearForm{Float64}(copy(L)), QT.DenseQuadraticForm{Float64}(UpperTriangular(copy(Q)))
    else
        QT.DictLinearForm{Float64}(Dict(i => L[i] for i in 1:n)),
        QT.DictQuadraticForm{Float64}(Dict((i,j) => Q[i,j] for i in 1:n for j in (i+1):n))
    end
    vm = QT.VariableMap{Int}(Dict(i => i for i in labels), labels)
    return QT.Model{Int,Float64,Int}(vm, QT.Form{Float64}(n, lf, qf, scale, offset; domain, sense=:min))
end

# Expire at a chosen deadline poll, without depending on compilation speed or
# wall-clock scheduling. This comparison is specific to the test-owned type.
mutable struct ConstructionPollDeadline
    expire_at::Int
    polls::Int
    expired::Bool
end
ConstructionPollDeadline(expire_at::Int) = ConstructionPollDeadline(expire_at, 0, false)
function Base.:>=(::UInt64, deadline::ConstructionPollDeadline)
    deadline.polls += 1
    deadline.expired = deadline.polls >= deadline.expire_at
    return deadline.expired
end

function construction_reference(L, Q, offset, domain)
    R = Rational{BigInt}
    fields = R.(L)
    n = length(L)
    lo, hi, dual = similar(fields), similar(fields), similar(fields)
    for i in 1:n
        row = R[Q[min(i,j), max(i,j)] for j in 1:n if j != i]
        csum = sum(row; init=R(0))
        if domain === :bool
            lo[i] = fields[i] + sum((min(R(0), q) for q in row); init=R(0))
            hi[i] = fields[i] + sum((max(R(0), q) for q in row); init=R(0))
            dual[i] = fields[i] / 2 + csum / 4
        else
            asum = sum(abs, row; init=R(0))
            lo[i], hi[i] = fields[i] - asum, fields[i] + asum
            dual[i] = 2 * fields[i] - 2 * csum
        end
    end
    qsum = sum((R(Q[i,j]) for i in 1:n for j in (i+1):n); init=R(0))
    fsum = sum(fields; init=R(0))
    constant = R(offset)
    dual_constant = domain === :bool ? constant + fsum / 2 + qsum / 4 : constant - fsum + qsum
    return (; fields, lo, hi, dual, constant, dual_constant)
end

function check_construction_state(ws, L, Q, offset, domain)
    R = Rational{BigInt}
    st = ws._state
    ref = construction_reference(L, Q, offset, domain)
    @test st.fields == ref.fields
    @test st.lower == ref.lo
    @test st.upper == ref.hi
    @test st.dual_fields == ref.dual
    @test st.constant == ref.constant
    @test st.dual_constant == ref.dual_constant
    for i in eachindex(L)
        expected = Dict(j => R(Q[min(i,j), max(i,j)]) for j in eachindex(L)
                        if j != i && !iszero(Q[min(i,j), max(i,j)]))
        @test Dict(st.adjacency[i]) == expected
        @test st.degrees[i] == length(expected)
        for (j, pos) in st.adj_pos[i]
            @test st.adjacency[i][pos] == (j => expected[j])
        end
    end
    poly = QUBOPreprocessing._init_poly_state(ws._snapshot)
    @test poly !== nothing
    @test poly.fields == ref.fields
    @test poly.constant == ref.constant
    @test poly.h_spin == (domain === :bool ? ref.dual : ref.fields)
    @test poly.c_spin == (domain === :bool ? ref.dual_constant : ref.constant)
    @test poly.adj == st.adjacency
    @test !ws.perturbed && iszero(ws.max_perturbation)
    return nothing
end

@testset "normalized finite binary64 conversion" begin
    R = Rational{BigInt}
    values = [0.0, -0.0, 0.1, -0.3, nextfloat(0.0), -nextfloat(0.0),
              prevfloat(floatmin(Float64)), floatmin(Float64), prevfloat(1.0),
              nextfloat(1.0), 2.0^80, -2.0^120, floatmax(Float64), -floatmax(Float64)]
    # Exercise exponent/mantissa/sign combinations with a bounded deterministic
    # bit stream, including values outside constructor accumulator eligibility.
    bits = UInt64(93)
    for _ in 1:300
        bits = bits * UInt64(6364136223846793005) + UInt64(1442695040888963407)
        value = reinterpret(Float64, bits)
        isfinite(value) && push!(values, value)
    end
    for v in values
        q = QUBOPreprocessing._to_exact(v)
        @test q == R(v)
        @test denominator(q) > 0
        @test gcd(numerator(q), denominator(q)) == 1
    end
    for q in (Int128(0), Int128(1), Int128(-1), Int128(12), -(Int128(1) << 120)),
        shift in (0, 1, 55, 1074)
        @test QUBOPreprocessing._from_dyadic_integer(q, shift) == R(q) / (BigInt(1) << shift)
        cache = QUBOPreprocessing._dyadic_denominators(shift)
        cached = QUBOPreprocessing._from_dyadic_integer(q, shift, cache)
        @test cached == R(q) / (BigInt(1) << shift)
        @test denominator(cached) > 0 && gcd(numerator(cached), denominator(cached)) == 1
    end
end

@testset "constructor denominator ownership and read-only arithmetic" begin
    R = Rational{BigInt}
    cache = QUBOPreprocessing._dyadic_denominators(5)
    a = QUBOPreprocessing._from_dyadic_integer(Int128(3), 4, cache)
    b = QUBOPreprocessing._from_dyadic_integer(Int128(-5), 4, cache)
    c = QUBOPreprocessing._from_dyadic_integer(Int128(6), 5, cache)
    @test denominator(a) === denominator(b) === denominator(c)
    originals = (R(3,16), R(-5,16), R(3,16))
    @test (a + b, a - b, a * b, a // b, -a, abs(b)) ==
          (originals[1] + originals[2], originals[1] - originals[2],
           originals[1] * originals[2], originals[1] // originals[2],
           -originals[1], abs(originals[2]))
    @test (a,b,c) == originals

    L = [0.1,-0.3,0.2]
    Q = [0.0 0.1 -0.3; 0.0 0.0 0.2; 0.0 0.0 0.0]
    for domain in (:bool,:spin)
        model = construction_fixture(L,Q; domain)
        ws = Workspace(model; rules=:mixed)
        other = Workspace(model; rules=:mixed)
        poly = QUBOPreprocessing._init_poly_state(ws._snapshot)
        @test denominator(ws._state.fields[1]) !== denominator(other._state.fields[1])
        @test denominator(ws._state.fields[1]) !== denominator(poly.fields[1])
        # Public coefficient results must stay owned even though private initial
        # rationals now share read-only denominator storage within one state.
        owned = (effective_field(ws,1), last(first(incident_couplings(ws,1))), conditioned_constant(ws))
        for q in owned
            Base.GMP.MPZ.set!(denominator(q), BigInt(7))
        end
        check_construction_state(ws,L,Q,0.3,domain)
        check_construction_state(other,L,Q,0.3,domain)
        @test poly.fields == R.(L)
    end
end

@testset "dyadic constructor caches and arbitrary-precision fallback" begin
    tiny = nextfloat(0.0)
    cases = (
        ([0.1,-0.3,0.0,0.2], [0.0 0.3 -0.1 0.0; 0.0 0.0 0.2 0.0; 0.0 0.0 0.0 -0.3; zeros(1,4)], 0.3, true),
        ([1/512,-3/512,0.0,2/512], [0.0 3/512 -1/512 0.0; 0.0 0.0 2/512 0.0; 0.0 0.0 0.0 -3/512; zeros(1,4)], 0.1, true),
        ([2.0^80,-2.0^79,0.0,2.0^78], [0.0 2.0^78 0.0 0.0; 0.0 0.0 -2.0^79 0.0; zeros(2,4)], 0.3, true),
        ([tiny,-2tiny,0.0,3tiny], [0.0 3tiny -tiny 0.0; 0.0 0.0 2tiny 0.0; 0.0 0.0 0.0 -3tiny; zeros(1,4)], tiny, true),
        ([2.0^100,2.0^-100,0.0,0.0], [0.0 0.1 0.0 0.0; zeros(3,4)], 0.3, false),
        ([floatmax(Float64),-floatmax(Float64),0.0,0.0], [0.0 floatmax(Float64) 0.0 0.0; zeros(3,4)], tiny, false),
        (zeros(4), zeros(4,4), floatmax(Float64), true),
    )
    for (L,Q,offset,fast) in cases, domain in (:bool,:spin), kind in (:sparse,:dense,:dict)
        model = construction_fixture(L, Q; offset, domain, kind, scale=-0.5)
        ws = Workspace(model; rules=:mixed, integerize_scale=false)
        @test (QUBOPreprocessing._dyadic_construction_plan(ws._snapshot).shift >= 0) == fast
        check_construction_state(ws, L, Q, offset, domain)
        out = export_model(materialize(ws))
        @test QT.scale(out) === -0.5
        @test QT.offset(out) === offset
        @test isequal(QT.data(QT.linear_form(QT.form(out))), QT.data(QT.linear_form(QT.form(model))))
        @test isequal(QT.data(QT.quadratic_form(QT.form(out))), QT.data(QT.quadratic_form(QT.form(model))))
        @test QUBOPreprocessing._init_poly_state(ws._snapshot; deadline=UInt64(0)) === nothing
    end
    # The sum bound, not only each individual conversion, must select fallback.
    near_limit = construction_fixture(fill(2.0^124, 4), zeros(4,4))
    @test QUBOPreprocessing._dyadic_construction_plan(QUBOPreprocessing._snapshot(near_limit)).shift < 0
    check_construction_state(Workspace(near_limit; rules=:mixed), fill(2.0^124, 4), zeros(4,4), 0.3, :bool)
end

@testset "dyadic construction preserves updates, replay, proofs and reset" begin
    R = Rational{BigInt}
    L = [0.1,-0.3,0.2]
    Q = [0.0 0.3 -0.1; 0.0 0.0 0.2; 0.0 0.0 0.0]
    for domain in (:bool,:spin)
        model = construction_fixture(L,Q; domain)
        ws = Workspace(model; rules=:mixed)
        root = checkpoint(ws)
        low = domain === :bool ? 0 : -1
        assume!(ws,1,low)
        assume!(ws,2,1)
        unfix!(ws,1) # non-LIFO replay rebuilds the constructor state
        @test assumptions(ws) == [2=>1]
        @test_throws ArgumentError rollback!(ws, root)
        unfix!(ws,2)
        check_construction_state(ws,L,Q,0.3,domain)
        before_reset = checkpoint(ws)
        reset!(ws, model)
        @test_throws ArgumentError rollback!(ws, before_reset)
        check_construction_state(ws,L,Q,0.3,domain)

        # No strict unary fixing exists initially in this triangle. Exact local
        # elimination therefore exercises transformed rational state and replay.
        L2 = domain === :bool ? fill(-0.1,3) : zeros(3)
        Q2 = [0.0 0.1 0.1; 0.0 0.0 0.1; 0.0 0.0 0.0]
        ws = Workspace(construction_fixture(L2,Q2; domain); rules=:mixed)
        cp = checkpoint(ws)
        @test eliminate_variable!(ws,1).stop_reason === :applied
        cert = export_certificate(ws)
        @test cert !== nothing && verify_certificate(ws,cert).valid
        result = materialize(ws; coefficient_type=R)
        out = export_model(result)
        for a in (low,1), b in (low,1)
            y = [a,b]
            lifted = reconstruct(result,y).state
            exact_energy = R(0.3) + sum((R(L2[i])*lifted[i] for i in 1:3); init=R(0)) +
                           sum((R(Q2[i,j])*lifted[i]*lifted[j] for i in 1:3 for j in (i+1):3); init=R(0))
            residual_energy = R(QT.offset(out)) + sum((QT.linear_form(QT.form(out))[i]*y[i] for i in 1:2); init=R(0)) +
                              QT.quadratic_form(QT.form(out))[1,2]*y[1]*y[2]
            @test exact_energy == R(QT.scale(out))*residual_energy
        end
        rollback!(ws,cp)
        check_construction_state(ws,L2,Q2,0.3,domain)
    end
end

@testset "construction expiry during preflight and replay scans" begin
    ws = Workspace(construction_fixture([0.1,0.3], [0.0 0.1; 0.0 0.0]); rules=:mixed)
    historical_snapshot = ws._snapshot
    historical_generation = generation(ws)
    historical_state = deepcopy(ws._state)
    storage_content(s) = (s.kind, s.shape, s.values, s.indices, s.pair_indices, s.pointers)
    snapshot_content(s) = (s.labels, s.label_type, s.state_type,
        storage_content(s.linear), storage_content(s.quadratic),
        s.scale, s.offset, s.sense, s.domain, s.perturbed, s.max_perturbation)
    historical_contents = deepcopy(snapshot_content(historical_snapshot))

    # Preflight polls once before scanning, twice for the two nonzero fields,
    # once for the edge, and once after scanning. Replay then polls twice for
    # its fields and once for its edge. Interrupt each scan at its first term.
    for (phase, expire_at) in ((:preflight_linear, 2), (:preflight_quadratic, 4),
                               (:replay_linear, 6), (:replay_quadratic, 8))
        @testset "$phase" begin
            deadline = ConstructionPollDeadline(expire_at)
            result = phase in (:preflight_linear, :preflight_quadratic) ?
                QUBOPreprocessing._dyadic_construction_plan(historical_snapshot; deadline) :
                QUBOPreprocessing._init_poly_state(historical_snapshot; deadline)
            @test result === nothing
            @test deadline.expired
            @test deadline.polls == expire_at
            @test ws._snapshot === historical_snapshot
            @test snapshot_content(historical_snapshot) == historical_contents
            @test generation(ws) == historical_generation
            for field in fieldnames(typeof(historical_state))
                @test getfield(ws._state, field) == getfield(historical_state, field)
            end
        end
    end
end
