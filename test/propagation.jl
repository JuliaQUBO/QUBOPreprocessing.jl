function engine_state(ws)
    st = ws._state
    proofdata(p) = p === nothing ? nothing : Tuple(getfield(p,f) for f in fieldnames(DominanceStep))
    history = [u isa QUBOPreprocessing._UndoFix ?
        (:fix,u.serial,u.fix_depth,u.index,u.value,u.constant,u.fields,u.queue_length,proofdata(u.proof)) :
        (:queue,u.serial,u.fix_depth,u.index,u.head,u.queued) for u in st.trail]
    # Serial allocation and execution counters are deliberately monotone.
    return deepcopy((st.fields,st.constant,st.fixed,st.queue,st.queued,st.head,
                     st.lower,st.upper,st.fixes,st.callers,st.entries,st.proof_count,history))
end

function check_engine(ws,labels,L,Q,scale,offset,domain,sense)
    n = length(labels)
    n <= 6 || throw(ArgumentError("tiny propagation oracle requires n<=6"))
    st = ws._state
    R = Rational{BigInt}
    fixed = Dict(i=>Int(st.fixed[i]) for i in 1:n if st.fixed[i] != 2)
    c = R(offset)
    for i in 1:n
        haskey(fixed,i) && (c += R(L[i])*fixed[i])
        for j in i+1:n
            haskey(fixed,i) && haskey(fixed,j) && (c += R(Q[i,j])*fixed[i]*fixed[j])
        end
        haskey(fixed,i) && continue
        field = R(L[i])
        a,b = R(0),R(0)
        for j in 1:n
            i == j && continue
            q = R(Q[min(i,j),max(i,j)])
            if haskey(fixed,j)
                field += q*fixed[j]
            else
                a += domain === :bool ? min(0,q) : -abs(q)
                b += domain === :bool ? max(0,q) : abs(q)
            end
        end
        @test st.fields[i] == field
        @test st.lower[i] == field+a
        @test st.upper[i] == field+b
    end
    @test st.constant == c
    callers = Dict(assumptions(ws))
    scope = Tuple(i=>callers[labels[i]] for i in 1:n if haskey(callers,labels[i]))
    optima = oracle_optima(L,Q,scale,offset,domain,sense,scope)
    for (label,value) in deductions(ws)
        i = findfirst(==(label),labels)
        @test all(x[i] == value for x in optima)
    end
    proof = export_certificate(ws)
    if proof !== nothing
        @test verify_certificate(ws,proof).valid
        @test proof.assumptions == Tuple(st.trail[p].index=>st.trail[p].value for p in st.callers)
    end
    result = isempty(st.fixes) ? materialize(ws) : materialize(ws;coefficient_type=R)
    out = export_model(result)
    free = [i for i in 1:n if !haskey(fixed,i)]
    @test QT.variables(out) == labels[free]
    energies = R[]
    for y in states(length(free),domain)
        restored = reconstruct(result,y)
        energy = R(QT.offset(out))
        for j in eachindex(y)
            energy += R(linear(out)[j])*y[j]
            for k in j+1:length(y)
                energy += R(quadratic(out)[j,k])*y[j]*y[k]
            end
        end
        energy *= R(QT.scale(out))
        @test energy == reference(L,Q,scale,offset,restored.state,R)
        push!(energies,energy)
    end
    best = sense === :min ? minimum(energies) : maximum(energies)
    @test best == reference(L,Q,scale,offset,first(optima),R)
    return result
end

@testset "certified propagation domains, scopes and residuals" begin
    labels = [(9,"last"),(1,"first"),(2,"isolate"),(4,"other")]
    L = [3.0,1.0,0.0,-2.0]
    Q = [0.0 -2.0 0.0 0.0;0.0 0.0 0.0 0.0;0.0 0.0 0.0 0.0;0.0 0.0 0.0 0.0]
    for kind in (:sparse,:dense,:dict), domain in (:bool,:spin), sense in (:min,:max), scale in (-2.0,0.0,0.5)
        model = fixture(labels,L,Q;kind,domain,sense,scale,offset=0.75)
        ws = Workspace(model;rules=:dominance)
        root = checkpoint(ws)
        initial = engine_state(ws)
        report = propagate!(ws)
        @test report.stop_reason === :quiescent
        @test report.pending == 0
        @test generation(report) == generation(ws)
        @test isempty(assumptions(ws))
        @test !haskey(Dict(deductions(ws)),labels[3]) # no strict fixing for zero isolate
        check_engine(ws,labels,L,Q,scale,0.75,domain,sense)
        @test propagate!(ws).candidates == 0
        rollback!(ws,root)
        @test engine_state(ws) == initial
        @test isempty(deductions(ws))
        assume!(ws,labels[2],domain === :bool ? 1 : -1)
        propagate!(ws)
        check_engine(ws,labels,L,Q,scale,0.75,domain,sense)
    end
end

@testset "resumable queue and exact/work/deduction stops" begin
    model = fixture([:x,:y],[3.0,1.0],[0.0 -2.0;0.0 0.0])
    for limit in (:work,:deductions,:exact)
        ws = Workspace(model;rules=:dominance)
        root = checkpoint(ws)
        before = engine_state(ws)
        stop = limit === :work ? propagate!(ws;max_work=0) :
               limit === :deductions ? propagate!(ws;max_deductions=0) : propagate!(ws;max_exact_work=0)
        @test stop.stop_reason in (:work_limit,:deduction_limit,:verification_limit)
        @test engine_state(ws) == before
        firstpass = limit === :work ? propagate!(ws;max_work=3) :
                    limit === :deductions ? propagate!(ws;max_deductions=1) : propagate!(ws;max_exact_work=5)
        @test firstpass.deductions == 1
        @test length(deductions(ws)) == 1
        check_engine(ws,[:x,:y],[3.0,1.0],[0.0 -2.0;0.0 0.0],1.0,0.0,:bool,:min)
        saved = checkpoint(ws)
        halfway = engine_state(ws)
        report = propagate!(ws)
        @test report.stop_reason === :quiescent
        @test deductions(ws;since=saved) == [:y=>0]
        @test assumptions(ws) == []
        @test length(export_certificate(ws).steps) == 2
        @test verify_certificate(ws,export_certificate(ws)).valid
        @test report.totals.candidates == firstpass.candidates+report.candidates
        rollback!(ws,saved)
        @test engine_state(ws) == halfway
        @test propagate!(ws).deductions == 1
        rollback!(ws,root)
        @test engine_state(ws) == before
    end
    ws = Workspace(model;rules=:dominance)
    before = engine_state(ws)
    @test propagate!(ws;deadline_ns=UInt64(0)).stop_reason === :deadline
    @test engine_state(ws) == before
    @test_throws ArgumentError propagate!(ws;max_work=-1)
    @test_throws ArgumentError propagate!(Workspace(model))
    _,report = preprocess(model;rules=:dominance)
    @test report.deductions == 2
    @test_throws ArgumentError preprocess(model;max_work=1)
end

@testset "interleaved proof scopes and safe assumption replay" begin
    labels = [:x,:y,:z,:w]
    L = [1.0,0.0,2.0,0.0]
    Q = [0.0 -2.0 0.0 0.0;0.0 0.0 0.0 0.0;0.0 0.0 0.0 -3.0;0.0 0.0 0.0 0.0]
    model = fixture(labels,L,Q)
    ws = Workspace(model;rules=:dominance)
    @test propagate!(ws).deductions == 0
    root = checkpoint(ws)
    assume!(ws,:y,0)
    @test propagate!(ws).deductions == 1
    @test deductions(ws) == [:x=>0]
    assume!(ws,:z,1)
    # Earlier witness constant is0; current constant2. Scope prefix binds the
    # witness to the assumptions actually used at its birth, not later ones.
    c = export_certificate(ws)
    @test c.steps[1].scope_length == 1
    @test c.steps[1].constant == 0
    @test ws._state.constant == 2
    @test verify_certificate(ws,c).valid
    propagate!(ws)
    c = export_certificate(ws)
    @test [s.scope_length for s in c.steps] == [1,2]
    @test verify_certificate(ws,c).valid
    check_engine(ws,labels,L,Q,1.0,0.0,:bool,:min)
    @test assume!(ws,:x,0).stop_reason === :unchanged
    @test assumptions(ws) == [:y=>0,:z=>1]
    @test_throws ArgumentError unfix!(ws,:x)
    @test_throws ArgumentError assume!(ws,:x,1)
    @test unfix!(ws,:y).stop_reason === :applied
    @test assumptions(ws) == [:z=>1]
    @test isempty(deductions(ws)) # no inferred value was replayed as a caller pin
    @test !verify_certificate(ws,c).valid
    @test_throws ArgumentError rollback!(ws,root)
    propagate!(ws)
    @test !haskey(Dict(deductions(ws)),:x)
    check_engine(ws,labels,L,Q,1.0,0.0,:bool,:min)
    fresh = Workspace(model;rules=:dominance)
    assume!(fresh,:z,1);propagate!(fresh)
    @test deductions(ws) == deductions(fresh)
    @test index_map(ws) == index_map(fresh)
    token = generation(ws)
    reset!(ws,model)
    @test generation(ws) != token
    @test ws._state.rules === :dominance
    @test propagate!(ws).deductions == 0
end

@testset "root-global proofs and residual graph splitting" begin
    for domain in (:bool,:spin)
        # Connected star. Fixing the center leaves two free zero-field isolates:
        # the original graph does not fit capacity1, each residual component does.
        L = domain === :bool ? [3.0,0.0,0.0] : [3.0,1.0,1.0]
        Q = [0.0 1.0 1.0;0.0 0.0 0.0;0.0 0.0 0.0]
        labels = [:center,:left,:right]
        ws = Workspace(fixture(labels,L,Q;domain);rules=:dominance)
        @test propagate!(ws).deductions == 1
        @test deductions(ws) == [:center=>(domain === :bool ? 0 : -1)]
        out = check_engine(ws,labels,L,Q,1.0,0.0,domain,:min)
        @test QT.dimension(export_model(out)) == 2
        @test isempty(collect(QT.quadratic_terms(export_model(out))))
        rootproof = export_certificate(ws)
        @test only(rootproof.steps).scope_length == 0
        assume!(ws,:left,1)
        c = export_certificate(ws)
        @test only(c.steps).scope_length == 0
        @test c.assumptions == (2=>1,)
        @test verify_certificate(ws,c).valid
        @test !verify_certificate(ws,rootproof).valid # historical tip
        check_engine(ws,labels,L,Q,1.0,0.0,domain,:min)
    end
end

@testset "exact export, all-fixed and cross-domain equivalence" begin
    ws = Workspace(fixture([:x,:y],[-2.0,1.0],[0.0 2.0^-53;0.0 0.0]);rules=:dominance)
    @test propagate!(ws;max_deductions=1).deductions == 1
    @test_throws ArgumentError materialize(ws)
    intermediate = materialize(ws;coefficient_type=Rational{BigInt})
    @test verify_certificate(ws,intermediate.certificate.proof).valid
    @test linear(export_model(intermediate))[1] == 1 + big(1)//big(2)^53
    propagate!(ws)
    final = materialize(ws)
    @test QT.dimension(export_model(final)) == 0
    @test reconstruct(final,Int[]).state == [1,0]
    @test !verify_certificate(ws,intermediate.certificate.proof).valid

    L = [3.0,1.0,0.0]
    Q = [0.0 -2.0 0.0;0.0 0.0 0.0;0.0 0.0 0.0]
    R = Rational{BigInt}
    h = [R(L[i])/2 + sum((R(Q[min(i,j),max(i,j)])/4 for j in 1:3 if j != i);init=R(0)) for i in 1:3]
    J = R.(Q)./4
    beta = R(0.5)+sum(R.(L))/2+sum(R.(Q))/4
    @test all(R(Float64(v)) == v for v in [h...;vec(J)...;beta])
    for sense in (:min,:max), scale in (-2.0,0.0,0.5)
        bool = Workspace(fixture([:a,:b,:isolate],L,Q;sense,scale,offset=0.5);rules=:dominance)
        spin = Workspace(fixture([:a,:b,:isolate],Float64.(h),Float64.(J);
                                 sense,scale,offset=Float64(beta),domain=:spin);rules=:dominance)
        propagate!(bool);propagate!(spin)
        @test Dict(deductions(spin)) == Dict(label=>2*v-1 for (label,v) in deductions(bool))
        for x in states(3,:bool)
            @test reference(L,Q,scale,0.5,x,R) == reference(h,J,scale,beta,2 .* x .- 1,R)
        end
    end
end

function propagated_cycle(ws,cp)
    assume!(ws,1,1)
    r = propagate!(ws;max_work=16,max_exact_work=32)
    rollback!(ws,cp)
    return r
end
@testset "local work, no-change and workspace isolation" begin
    small = Workspace(sparse_chain(10);rules=:dominance)
    large = Workspace(sparse_chain(2000);rules=:dominance)
    @test propagate!(small).deductions == propagate!(large).deductions == 0
    a,b = checkpoint(small),checkpoint(large)
    for _ in 1:3;propagated_cycle(small,a);propagated_cycle(large,b);end
    x,y = propagated_cycle(small,a),propagated_cycle(large,b)
    @test x.candidates == y.candidates == 2
    @test x.edge_visits == y.edge_visits == 2
    @test x.deductions == y.deductions == 1
    smallbytes = @allocated propagated_cycle(small,a)
    largebytes = @allocated propagated_cycle(large,b)
    @test largebytes <= smallbytes+2048
    r = propagate!(large)
    @test r.candidates == r.edge_visits == r.exact_work == r.deductions == 0
    @test r.checkpoint._depth == b._depth
    @test isempty(deductions(large;since=b))
    @test export_certificate(large) === nothing
    assume!(small,1,1);propagate!(small)
    @test isempty(deductions(large))
    @test index_map(small)[2] == 0
    @test index_map(large)[2] == 2
end
