# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

function check_integer_payload(ws)
    st = ws._state
    I = eltype(st.fields)
    @test I in (Int128, BigInt)
    @test st.fields isa Vector{I}
    @test st.dual_fields isa Vector{I}
    @test st.adjacency isa Vector{Vector{Pair{Int,I}}}
    @test st.trail isa Vector{QUBOPreprocessing._UndoEntry{I}}
    @test st.constant isa I && st.dual_constant isa I
    @test st.lower === nothing || st.lower isa Vector{I}
    @test st.upper === nothing || st.upper isa Vector{I}
    R = Rational{BigInt}
    physical(v) = R(v) / (big(1) << st.shift)
    is_bool = ws._snapshot.domain === QT.BoolDomain
    free = findall(==(2), st.fixed)
    total_f = sum((physical(st.fields[i]) for i in free); init=R(0))
    total_q = sum((physical(q) for i in free for (j,q) in st.adjacency[i]
                   if i < j && st.fixed[j] == 2); init=R(0))
    for i in free
        f = physical(st.fields[i])
        qs = R[physical(q) for (j,q) in st.adjacency[i] if st.fixed[j] == 2]
        @test st.degrees[i] == length(qs)
        @test physical(st.dual_fields[i]) == (is_bool ? f/2 + sum(qs; init=R(0))/4 : 2*f - 2*sum(qs; init=R(0)))
        if st.lower !== nothing
            lo = f + sum((is_bool ? min(R(0),q) : -abs(q) for q in qs); init=R(0))
            hi = f + sum((is_bool ? max(R(0),q) : abs(q) for q in qs); init=R(0))
            @test physical(st.lower[i]) == lo
            @test physical(st.upper[i]) == hi
        end
    end
    @test physical(st.dual_constant) == (is_bool ? physical(st.constant) + total_f/2 + total_q/4 :
        physical(st.constant) - total_f + total_q)
    for e in st.trail
        e isa QUBOPreprocessing._UndoQueue && continue
        @test e.constant isa I && e.dual_constant isa I
        @test e.fields isa Vector{QUBOPreprocessing._NeighborRecord{I}}
    end
end

function check_integer_objective(ws, L, Q, scale, offset, domain)
    R = Rational{BigInt}
    # Use a coordinate map to request rational output even for an identity
    # workspace, whose default no-map identity API remains Float64-only.
    map = domain_map(ws; domain)
    result = materialize(ws, map; coefficient_type=R)
    model = export_model(result)
    n = QT.dimension(model)
    n <= 8 || throw(ArgumentError("integer-state oracle accepts at most eight free variables"))
    for y in states(n, domain)
        rec = reconstruct(result, y)
        energy = QT.offset(model)
        for i in 1:n
            energy += linear(model)[i]*y[i]
            for j in i+1:n
                energy += quadratic(model)[i,j]*y[i]*y[j]
            end
        end
        @test R(QT.scale(model))*energy == reference(L,Q,scale,offset,rec.state,R)
    end
    proof = export_certificate(ws)
    proof === nothing || @test verify_certificate(ws, proof).valid
    check_integer_payload(ws)
end

@testset "persistent integer payload across represented decimal conditioning" begin
    for domain in (:bool,:spin), sense in (:min,:max), scale in (-2.0,0.0,0.5),
        unit in (0.1,1/512)
        L = [-3unit, unit, 2unit]
        Q = [0.0 unit -2unit; 0.0 0.0 3unit; 0.0 0.0 0.0]
        ws = Workspace(fixture([:x,:y,:z],L,Q; domain,sense,scale,offset=unit);
                       rules=:mixed, integerize_scale=false)
        @test eltype(ws._state.fields) === Int128
        check_integer_objective(ws,L,Q,scale,unit,domain)
        root = checkpoint(ws)
        low = domain === :bool ? 0 : -1
        assume!(ws,:x,low)
        assume!(ws,:z,1)
        check_integer_objective(ws,L,Q,scale,unit,domain)
        unfix!(ws,:x)
        @test assumptions(ws) == [:z=>1]
        @test_throws ArgumentError rollback!(ws,root)
        check_integer_objective(ws,L,Q,scale,unit,domain)
    end
end

@testset "exponent extension rescales live state and old undo records" begin
    L = [1.0,0.0,0.0,2.0]
    Q = [0.0 1.0 1.0 0.0; zeros(3,4)]
    ws = Workspace(fixture([:x,:y,:z,:isolate],L,Q; domain=:spin); rules=:mixed)
    root = checkpoint(ws)
    assume!(ws,:isolate,1)
    cp = checkpoint(ws)
    gauge = domain_map(ws; domain=:bool,gauge=[-1,1,-1,1])
    before_map_constant = conditioned_constant(ws; map=gauge)
    @test ws._state.shift == 0
    @test eliminate_variable!(ws,:x).stop_reason === :applied
    @test ws._state.shift == 1
    @test ws._state.extensions == 1
    @test eltype(ws._state.fields) === Int128
    @test conditioned_constant(ws; map=gauge) == QUBOPreprocessing._direct_mapped_constant(ws,gauge)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,cp)
    @test ws._state.shift == 1 # rollback retains a valid finer integer grid
    @test conditioned_constant(ws; map=gauge) == before_map_constant
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "promotion precedes integer overflow and preserves checkpoints" begin
    L = [0.0,0.0,1.0]
    Q = [0.0 2.0^125 0.0; zeros(2,3)]
    ws = Workspace(fixture([:x,:y,:isolate],L,Q; domain=:spin); rules=:mixed)
    @test eltype(ws._state.fields) === BigInt
    root = checkpoint(ws)
    assume!(ws,:isolate,1)
    # Exercise the guarded update at the actual Int128 boundary. All live and
    # historical numerators fit Int128 here; the constructor conservatively
    # chooses BigInt because it reserves headroom for future arithmetic.
    ws._state.numeric = QUBOPreprocessing._regrid(ws._state,Int128,ws._state.shift)
    @test eltype(ws._state.fields) === Int128
    cp = checkpoint(ws)
    @test assume!(ws,:x,-1).stop_reason === :applied
    @test eltype(ws._state.fields) === BigInt
    @test ws._state.promotions == 1
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,cp)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)

    # A large exponent extension preserves the polynomial in the wide backend.
    # Rollback restores old values under the new denominator.
    assume!(ws,:isolate,1)
    original_constant = conditioned_constant(ws)
    QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+1076)
    @test conditioned_constant(ws) == original_constant
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "integer reductions, maps and local block reconstruction" begin
    for domain in (:bool,:spin), sense in (:min,:max), scale in (-0.5,0.5)
        L = domain === :bool ? [-0.5,-0.5,0.0,0.0] : [0.5,-0.5,0.0,0.0]
        Q = [0.0 0.5 0.25 0.0; 0.0 0.0 0.0 -0.25; zeros(2,4)]
        ws = Workspace(fixture([:a,:b,:c,:d],L,Q; domain,sense,scale,offset=0.125);rules=:mixed)
        root = checkpoint(ws)
        @test eliminate_block!(ws,[:a,:b]).stop_reason === :applied
        check_integer_objective(ws,L,Q,scale,0.125,domain)
        rollback!(ws,root)
        check_integer_objective(ws,L,Q,scale,0.125,domain)
    end
    L = zeros(3)
    Q = [0.0 -4.0 2.0; 0.0 0.0 1.0; 0.0 0.0 0.0]
    ws = Workspace(fixture([:x,:y,:z],L,Q;domain=:spin);rules=:mixed)
    root = checkpoint(ws)
    @test contract_relation!(ws,:x,:y;sign=1).stop_reason === :applied
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    gauge = domain_map(ws;domain=:bool,gauge=[-1,1,-1])
    before_constant = conditioned_constant(ws;map=gauge)
    QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+124)
    @test eltype(ws._state.fields) === BigInt
    @test ws._state.promotions == 1
    @test conditioned_constant(ws;map=gauge) == before_constant
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)

    for value in (nextfloat(0.0),floatmax(Float64))
        L = [value,-value]
        Q = [0.0 value;0.0 0.0]
        ws = Workspace(fixture([:x,:y],L,Q;offset=value,domain=:spin);rules=:mixed)
        check_integer_objective(ws,L,Q,1.0,value,:spin)
        @test eliminate_variable!(ws,:x).stop_reason === :applied
        check_integer_objective(ws,L,Q,1.0,value,:spin)
    end
end

@testset "integer no-progress path preserves payload and policy" begin
    ws = Workspace(fixture([:x,:y,:z],zeros(3),[0.0 1.0 1.0;0.0 0.0 1.0;0.0 0.0 0.0];domain=:spin);
                   rules=:dominance)
    numeric = ws._state.numeric
    report = propagate!(ws)
    @test report.deductions == 0
    @test report.stop_reason === :quiescent
    @test ws._state.numeric === numeric
    @test ws._state.promotions == ws._state.extensions == 0
    @test isempty(deductions(ws))
end

@testset "integer relation screening and complete schedules" begin
    n = 8 # guarded complete-state oracle limit
    L = zeros(n)
    Q = [i<j ? 4.0 : 0.0 for i in 1:n,j in 1:n]
    Q[1,2] = -4.0
    ws = Workspace(fixture(collect(1:n),L,Q;domain=:spin);rules=:mixed)
    st = ws._state
    raw12 = st.adjacency[1][st.adj_pos[1][2]].second
    raw34 = st.adjacency[3][st.adj_pos[3][4]].second
    @test QUBOPreprocessing._can_possibly_contract(ws,1,2,raw12,1,nothing)
    @test !QUBOPreprocessing._can_possibly_contract(ws,3,4,raw34,1,nothing)
    @test QUBOPreprocessing._can_possibly_contract(ws,1,2,Rational{BigInt}(-4),1,nothing)
    report = schedule_reductions!(ws;allow_weak_dominance=true,allow_weak_relations=true)
    @test report.deductions > 0
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "interrupted reductions do not commit grid extension" begin
    R = Rational{BigInt}
    ws = Workspace(fixture([:x,:y,:z],[1.0,0.0,0.0],
        [0.0 1.0 1.0;zeros(2,3)];domain=:spin);rules=:mixed)
    attempt = prove_elimination(ws,:x)
    @test attempt.stop_reason === :proved
    step = last(attempt.certificate.steps)
    numeric = ws._state.numeric
    cp = checkpoint(ws)
    result = QUBOPreprocessing._apply_reduction!(ws,1,Int8(4),step,step.constant_delta,
        Pair{Int,R}[p for p in step.linear_deltas],
        Tuple{Int,Int,R}[t for t in step.quadratic_deltas];max_work=0)
    @test result.stop_reason === :work_limit
    @test ws._state.numeric === numeric
    @test ws._state.shift == ws._state.extensions == 0
    @test isempty(reductions(ws))
    @test_throws ArgumentError QUBOPreprocessing._apply_reduction!(ws,1,Int8(4),step,R(1//3),
        Pair{Int,R}[],Tuple{Int,Int,R}[])
    @test ws._state.numeric === numeric
    rollback!(ws,cp)
    check_integer_payload(ws)
end

@testset "direct dyadic intervals enclose exact values" begin
    R = Rational{BigInt}
    ws = Workspace(fixture([:x],zeros(1),zeros(1,1)))
    values = [big(0),big(1),-big(1),big(2)^53+1,big(2)^128-1,
              -(big(2)^127),big(2)^2098-1,-(big(2)^2098-1)]
    for shift in (0,54,1074,1076,2100), q in values,
        numerator in (typemin(Int128) <= q <= typemax(Int128) ? (Int128(q),q) : (q,))
        ws._state.shift = shift # the zero polynomial is unchanged on every grid
        lo,hi = QUBOPreprocessing._enclose_grid(ws._state,numerator)
        exact = R(q)/(big(1)<<shift)
        @test !isnan(lo) && !isnan(hi)
        @test lo != Inf && hi != -Inf
        @test lo <= hi
        @test !isfinite(lo) || R(lo) <= exact
        @test !isfinite(hi) || exact <= R(hi)
    end
end
