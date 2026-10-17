function oracle_optima(L,Q,scale,offset,domain,sense,scope)
    n = length(L)
    # states guards the dimension before exponentiation/allocation.
    xs = [x for x in states(n,domain) if all(x[i] == v for (i,v) in scope)]
    energies = [reference(L,Q,scale,offset,x,Rational{BigInt}) for x in xs]
    best = sense === :min ? minimum(energies) : maximum(energies)
    return [x for (x,e) in zip(xs,energies) if e == best]
end

function copy_step(s; variable=s.variable,value=s.value,lower=s.lower,upper=s.upper,
                   constant=s.constant,predecessors=s.predecessors,method=s.method)
    DominanceStep(variable,value,lower,upper,constant,predecessors,method)
end
function copy_certificate(c; token=c.generation,position=c._scope_checkpoint,
                          scope=c.assumptions,steps=c.steps,source=c._source)
    DominanceCertificate(token,position,scope,steps,source)
end

@testset "strong proofs against independent scoped optima" begin
    labels = ["last","first","third","isolate"]
    L = [2.0,0.0,-3.0,0.0]
    Q = [0.0 -0.5 0.0 0.0; 0.0 0.0 0.25 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]
    for kind in (:sparse,:dense,:dict), domain in (:bool,:spin), sense in (:min,:max), scale in (-2.0,0.0,0.5)
        ws = Workspace(fixture(labels,L,Q;kind,domain,sense,scale,offset=1.25))
        original = algebra_state(ws)
        for scope in ((),(2=>(domain === :bool ? 0 : -1),))
            root = checkpoint(ws)
            for (i,v) in scope; assume!(ws,labels[i],v); end
            optima = oracle_optima(L,Q,scale,1.25,domain,sense,scope)
            for i in (1,3,4)
                before = algebra_state(ws)
                attempt = prove_dominance(ws,labels[i])
                @test algebra_state(ws) == before
                @test attempt.edge_visits <= 2*length(ws._state.adjacency[i])
                if attempt.certificate === nothing
                    @test attempt.stop_reason in (:zero_scale,:not_strict)
                else
                    c = attempt.certificate
                    @test attempt.stop_reason === :proved
                    @test generation(c) == generation(ws)
                    @test c.assumptions == scope
                    @test length(c.steps) == 1
                    @test verify_certificate(ws,c).valid
                    step = only(c.steps)
                    @test all(x[i] == step.value for x in optima)
                    @test step.predecessors == 0
                end
            end
            rollback!(ws,root)
        end
        @test algebra_state(ws) == original
    end
end

@testset "fast enclosure, exact fallback and refusals" begin
    ws = Workspace(fixture([:x,:y],[10.0,0.0],[0.0 -1.0;0.0 0.0]))
    a = prove_dominance(ws,:x;max_exact_work=0)
    @test a.stop_reason === :proved
    @test a.method === :interval
    @test a.exact_fallbacks == a.exact_work == 0
    @test verify_certificate(ws,a.certificate).valid
    @test prove_dominance(ws,:x;max_work=0).stop_reason === :work_limit
    @test prove_dominance(ws,:x;deadline_ns=UInt64(0)).stop_reason === :deadline
    @test_throws ArgumentError prove_dominance(ws,:missing)
    @test_throws ArgumentError prove_dominance(ws,:x;max_exact_work=-1)
    # Outward expansion at the positive first edge masks a small positive
    # lower bound until exact fallback. The exact gap is nextfloat(1)-1.
    ws = Workspace(fixture([:x,:y,:z],[nextfloat(1.0),0.0,0.0],
                           [0.0 1.0 -1.0;0.0 0.0 0.0;0.0 0.0 0.0]))
    @test prove_dominance(ws,:x;max_exact_work=0).stop_reason === :verification_limit
    @test prove_dominance(ws,:x;max_work=2).stop_reason === :work_limit
    a = prove_dominance(ws,:x)
    @test a.method === :exact
    @test a.exact_fallbacks == 1
    @test a.edge_visits == 4
    @test only(a.certificate.steps).lower == Rational{BigInt}(nextfloat(1.0))-1
    @test verify_certificate(ws,a.certificate).valid
    # Subnormal cancellation, overflow and exact ties cannot be repaired by eps.
    tiny = nextfloat(0.0)
    ws = Workspace(fixture([:x,:y],[2*tiny,0.0],[0.0 tiny;0.0 0.0];domain=:spin))
    a = prove_dominance(ws,:x)
    @test a.method === :exact
    @test only(a.certificate.steps).lower == Rational{BigInt}(tiny)
    @test verify_certificate(ws,a.certificate).valid
    ws = Workspace(fixture([:x,:y],[floatmax(Float64),0.0],
                           [0.0 floatmax(Float64);0.0 0.0];scale=-2.0,sense=:max))
    a = prove_dominance(ws,:x)
    @test a.method === :exact
    @test a.stop_reason === :proved
    @test verify_certificate(ws,a.certificate).valid
    ws = Workspace(fixture([:x,:y],[1.0,0.0],[0.0 -1.0;0.0 0.0]))
    @test prove_dominance(ws,:x).stop_reason === :not_strict
    ws = Workspace(fixture([:x],[0.0],zeros(1,1)))
    @test prove_dominance(ws,:x).certificate === nothing
    ws = Workspace(fixture([:x],[-1.0],zeros(1,1);scale=-0.0))
    @test prove_dominance(ws,:x).stop_reason === :zero_scale
    assume!(ws,:x,1)
    @test prove_dominance(ws,:x).stop_reason === :already_fixed
end

@testset "conditional scope and independent tamper verification" begin
    model = fixture([:x,:y],[1.0,0.0],[0.0 -2.0;0.0 0.0];offset=0.5)
    ws = Workspace(model)
    root = checkpoint(ws)
    @test prove_dominance(ws,:x).certificate === nothing
    assume!(ws,:y,0)
    c = prove_dominance(ws,:x).certificate
    @test c.assumptions == (2=>0,)
    @test only(c.steps).value == 0 # globally the unique optimum has x=y=1
    @test verify_certificate(ws,c).valid
    ancestor = copy_certificate(c;position=root)
    @test verify_certificate(ws,ancestor).stop_reason === :stale_scope
    @test !verify_certificate(ws,c;max_work=0).valid
    @test verify_certificate(ws,c;deadline_ns=UInt64(0)).stop_reason === :deadline
    step = only(c.steps)
    for bad in (copy_step(step;value=1),copy_step(step;value=2),
                copy_step(step;variable=3),copy_step(step;constant=step.constant+1),
                copy_step(step;lower=step.upper+1),copy_step(step;predecessors=1),
                copy_step(step;method=:tolerance))
        @test !verify_certificate(ws,copy_certificate(c;steps=(bad,))).valid
    end
    @test !verify_certificate(ws,copy_certificate(c;steps=())).valid
    @test !verify_certificate(ws,copy_certificate(c;scope=())).valid
    other = Workspace(model)
    @test verify_certificate(other,c).stop_reason === :stale_generation
    source = c._source
    changed = QUBOPreprocessing._Snapshot(source.labels,source.label_type,source.state_type,
        source.linear,source.quadratic,source.scale,source.offset+1,source.sense,source.domain)
    @test verify_certificate(ws,copy_certificate(c;source=changed)).stop_reason === :different_source
    rollback!(ws,root)
    @test verify_certificate(ws,c).stop_reason === :stale_scope
    assume!(ws,:y,0) # same values on a different branch must not revive old scope
    @test verify_certificate(ws,c).stop_reason === :stale_scope
    @test verify_certificate(ws,ancestor).stop_reason === :stale_scope
    c = prove_dominance(ws,:x).certificate
    @test verify_certificate(ws,c).valid
    reset!(ws,model)
    @test verify_certificate(ws,c).stop_reason === :stale_generation

    # Verifier recomputes from represented source, not the producer's cached field.
    ws = Workspace(fixture([:x],[1.0],zeros(1,1)))
    ws._state.fields[1] = -big(100)//big(1)
    bad = prove_dominance(ws,:x).certificate
    @test verify_certificate(ws,bad).stop_reason === :invalid_bound
end

@testset "ordered strong deduction prefix" begin
    model = fixture([:x,:y],[3.0,1.0],[0.0 -2.0;0.0 0.0])
    ws = Workspace(model)
    root = checkpoint(ws)
    firstproof = prove_dominance(ws,:x).certificate
    @test verify_certificate(ws,firstproof).valid
    assume!(ws,:x,only(firstproof.steps).value)
    nextstep, reason, _, _, _, _ = QUBOPreprocessing._dominance_witness(ws,2;predecessors=1)
    @test reason === :proved
    rollback!(ws,root)
    chain = copy_certificate(firstproof;steps=(only(firstproof.steps),nextstep))
    @test verify_certificate(ws,chain).valid
    @test !verify_certificate(ws,copy_certificate(chain;steps=(nextstep,))).valid
    @test !verify_certificate(ws,copy_certificate(chain;steps=reverse(chain.steps))).valid
    @test !verify_certificate(ws,copy_certificate(chain;steps=(only(firstproof.steps),
        copy_step(nextstep;predecessors=0)))).valid
    optima = oracle_optima([3.0,1.0],[0.0 -2.0;0.0 0.0],1.0,0.0,:bool,:min,())
    @test all(all(x[step.variable] == step.value for step in chain.steps) for x in optima)
end

@testset "proof does not authorize rounded residual transport" begin
    model = fixture([:x,:y],[-2.0,1.0],[0.0 2.0^-53;0.0 0.0])
    ws = Workspace(model)
    a = prove_dominance(ws,:x)
    @test verify_certificate(ws,a.certificate).valid
    @test only(a.certificate.steps).value == 1
    assume!(ws,:x,1)
    @test_throws ArgumentError materialize(ws)
    residual = export_model(materialize(ws;coefficient_type=Rational{BigInt}))
    @test linear(residual)[1] == 1 + big(1)//big(2)^53
    @test reconstruct(materialize(ws;coefficient_type=Rational{BigInt}),[0]).state == [1,0]
end

@testset "represented-value stress and scoped rollback" begin
    tiny = nextfloat(0.0)
    pool = [0.0,tiny,-tiny,1.0,-1.0,nextfloat(1.0),2.0^-53,
            floatmax(Float64)/4,-floatmax(Float64)/4,0.1,-0.3]
    fast, fallback, proved = 0,0,0
    for seed in 1:12, domain in (:bool,:spin), sense in (:min,:max), scale in (-2.0,0.0,0.5)
        bits = trace_bits(seed)
        draw() = pool[Int(bits()%length(pool))+1]
        L = [draw() for _ in 1:3]
        Q = zeros(3,3)
        for i in 1:3, j in i+1:3; Q[i,j] = draw(); end
        ws = Workspace(fixture([:x,:y,:z],L,Q;domain,sense,scale,offset=0.1))
        root = checkpoint(ws)
        for iteration in 1:6
            assume!(ws,:y,isodd(iteration) ? 1 : (domain === :bool ? 0 : -1))
            scope = (2=>Int(ws._state.fixed[2]),)
            optima = oracle_optima(L,Q,scale,0.1,domain,sense,scope)
            for (i,label) in ((1,:x),(3,:z))
                a = prove_dominance(ws,label)
                fast += a.method === :interval
                fallback += a.exact_fallbacks
                if a.certificate !== nothing
                    proved += 1
                    @test verify_certificate(ws,a.certificate).valid
                    @test all(x[i] == only(a.certificate.steps).value for x in optima)
                else
                    @test a.stop_reason in (:zero_scale,:not_strict)
                end
            end
            rollback!(ws,root)
            @test isempty(assumptions(ws))
        end
    end
    @test fast > 0
    @test fallback > 0
    @test proved > 0
end
