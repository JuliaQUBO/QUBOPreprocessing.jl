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
        @test Rational{BigInt}(st.fields[i]) / (big(1)<<st.shift) == field
        @test Rational{BigInt}(st.lower[i]) / (big(1)<<st.shift) == field+a
        @test Rational{BigInt}(st.upper[i]) / (big(1)<<st.shift) == field+b
    end
    @test Rational{BigInt}(st.constant) / (big(1)<<st.shift) == c
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
    @test Rational{BigInt}(ws._state.constant) / (big(1)<<ws._state.shift) == 2
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

# BEGIN TYPED RELATION QUEUE REGRESSION FIXTURES
# Typed relation-queue regression fixtures (all at most eight variables).
import UUIDs
# Independent synthetic fixtures only. Every model is checked <=8 BEFORE construction.
const REL_TRACE=String[]
mutable struct RelationDeadline
    expire_at::Int
    polls::Int
end
# Test-only deterministic clock accepted by a type-specific guard method.
# Legal public UInt64/nothing deadlines keep the original production method.
function QUBOPreprocessing._limits(max_work,deadline::RelationDeadline)
    max_work isa Integer && !(max_work isa Bool) && 0<=max_work<=typemax(Int) ||
        throw(ArgumentError("max_work must be a nonnegative machine-sized integer"))
    return nothing
end
function Base.:>=(::UInt64,d::RelationDeadline)
    d.polls+=1
    return d.polls>=d.expire_at
end
function relation_normalize(x)
    x===nothing && return "nothing"
    x isa UUIDs.UUID && return "<UUIDs.UUID>"
    x isa Symbol && return string(x)
    x isa AbstractString && return String(x)
    x isa AbstractFloat && return (string(typeof(x)),bitstring(x))
    x isa Number && return (string(typeof(x)),string(x))
    x isa Pair && return (relation_normalize(x.first),relation_normalize(x.second))
    x isa AbstractDict && return sort!([(repr(relation_normalize(k)),relation_normalize(v)) for (k,v) in x];by=first)
    x isa Union{Tuple,AbstractArray} && return (string(typeof(x)),[relation_normalize(v) for v in x])
    return (string(typeof(x)),[(string(f),relation_normalize(getfield(x,f))) for f in fieldnames(typeof(x))])
end
function relation_record(label,ws,result,deadline=nothing)
    push!(REL_TRACE,repr((label,relation_normalize(result),relation_normalize(ws._state),deadline===nothing ? 0 : deadline.polls)))
end
function relation_input(kind,domain,sense,scale)
    if kind===:glk
        h=[2.0,2.0,0.0];J=[0.0 -3.0 2.0;0.0 0.0 2.0;zeros(1,3)]
    elseif kind===:twins
        h=zeros(4);J=[0.0 0.0 -2.0 1.0;0.0 0.0 -2.0 1.0;0.0 0.0 0.0 1.0;zeros(1,4)]
    else
        h=[0.0,1.0,-1.0,0.0];J=[0.0 -4.0 0.5 0.0;0.0 0.0 -1.0 0.0;0.0 0.0 0.0 -2.0;zeros(1,4)]
    end
    # Keep all min/max and scale signs nontrivial while retaining exact Float64 inputs.
    direction=(sense===:min ? 1 : -1)*(scale<0 ? -1 : 1)
    h=direction*h;J=direction*J;c=0.125
    if domain===:spin
        return h,J,c
    end
    n=length(h);L=2h;Q=4J;c-=sum(h)
    for i in 1:n,j in i+1:n
        L[i]-=2J[i,j];L[j]-=2J[i,j];c+=J[i,j]
    end
    return L,Q,c
end
function relation_workspace(L,Q,c,domain,sense,scale,backend)
    1<=length(L)<=8 || error("tiny relations fixtures require at most8 variables")
    ws=Workspace(fixture(collect(1:length(L)),L,Q;domain,sense,scale,offset=c);rules=:relations,integerize_scale=false)
    st=ws._state
    if backend===:fine_int128
        QUBOPreprocessing._ensure_grid!(st,st.shift+2)
    elseif backend===:bigint
        st.numeric=QUBOPreprocessing._regrid(st,BigInt,st.shift)
    elseif backend===:fine_bigint
        QUBOPreprocessing._ensure_grid!(st,st.shift+130)
    end
    @test eltype(st.fields)==(backend in (:bigint,:fine_bigint) ? BigInt : Int128)
    return ws
end
function relation_oracle(ws,L,Q,c,domain,sense,scale)
    n=length(L);@test n<=8
    original=[reference(L,Q,scale,c,x,Rational{BigInt}) for x in states(n,domain)]
    best=sense===:min ? minimum(original) : maximum(original)
    mat=isempty(ws._state.fixes) ? materialize(ws) : materialize(ws;coefficient_type=Rational{BigInt});out=export_model(mat)
    proof=export_certificate(ws)
    proof===nothing || @test verify_certificate(ws,proof).valid
    lf,qf=linear(out),quadratic(out);energies=Rational{BigInt}[]
    for y in states(QT.dimension(out),domain)
        rr=reconstruct(mat,y);energy=Rational{BigInt}(QT.offset(out))
        for i in eachindex(y)
            energy+=Rational{BigInt}(lf[i])*y[i]
            for j in i+1:length(y);energy+=Rational{BigInt}(qf[i,j])*y[i]*y[j];end
        end
        energy*=Rational{BigInt}(QT.scale(out))
        @test energy==reference(L,Q,scale,c,rr.state,Rational{BigInt})
        push!(energies,energy)
    end
    @test (sense===:min ? minimum(energies) : maximum(energies))==best
    return nothing
end
@testset "typed relation queue exact state, proof, residual and rollback invariants" begin
    for kind in (:glk,:twins,:chain),domain in (:bool,:spin),sense in (:min,:max),
        scale in (-0.5,0.5),weak in (false,true),mapped in (false,true),
        backend in (:int128,:fine_int128,:bigint,:fine_bigint)
        L,Q,c=relation_input(kind,domain,sense,scale)
        ws=relation_workspace(L,Q,c,domain,sense,scale,backend)
        root=checkpoint(ws)
        map=mapped ? domain_map(ws;domain=domain===:bool ? :spin : :bool,gauge=[isodd(i) ? -1 : 1 for i in eachindex(L)]) : nothing
        report=contract_relations!(ws;allow_weak=weak,map)
        @test report.stop_reason===:quiescent
        relation_record((kind,domain,sense,scale,weak,mapped,backend,:complete),ws,report)
        relation_oracle(ws,L,Q,c,domain,sense,scale)
        rollback!(ws,root)
        @test all(==(Int8(2)),ws._state.fixed)
        relation_oracle(ws,L,Q,c,domain,sense,scale)
        relation_record((kind,domain,sense,scale,weak,mapped,backend,:rollback),ws,nothing)
    end
end
@testset "direct queue ordered polls and exact/work caps preserve parent traces" begin
    for kind in (:glk,:twins),domain in (:bool,:spin),weak in (false,true),backend in (:int128,:bigint),
        work in (0,1,3,12,100),exact in (0,4,100)
        L,Q,c=relation_input(kind,domain,:min,0.5)
        ws=relation_workspace(L,Q,c,domain,:min,0.5,backend)
        result=QUBOPreprocessing._step_relation_queue!(ws,typemax(Int),nothing,weak,1,work,exact,nothing)
        relation_record((kind,domain,weak,backend,:caps,work,exact),ws,result)
        relation_oracle(ws,L,Q,c,domain,:min,0.5)
    end
    for kind in (:glk,:twins),domain in (:bool,:spin),weak in (false,true),backend in (:int128,:bigint),expire in 1:24
        L,Q,c=relation_input(kind,domain,:min,0.5)
        ws=relation_workspace(L,Q,c,domain,:min,0.5,backend)
        d=RelationDeadline(expire,0)
        result=QUBOPreprocessing._step_relation_queue!(ws,typemax(Int),nothing,weak,1,1000,1000,d)
        @test d.polls<=expire
        relation_record((kind,domain,weak,backend,:deadline,expire),ws,result,d)
        relation_oracle(ws,L,Q,c,domain,:min,0.5)
    end
    L,Q,c=relation_input(:glk,:spin,:min,0.5)
    for deadline in (UInt64(0),nothing),work in (0,1)
        ws=relation_workspace(L,Q,c,:spin,:min,0.5,:int128)
        before=relation_normalize(ws._state)
        r=QUBOPreprocessing._step_relation_queue!(ws,0,nothing,false,1,work,0,deadline)
        @test r[1]===(deadline===nothing ? :work_limit : :deadline)
        @test relation_normalize(ws._state)==before
        relation_record((:entry_guard,deadline,work),ws,r)
    end
end
# Applying a contraction may widen the payload. This fixture verifies that
# queue-pop journaling uses the new owner after the applied exit.
@testset "applying relation exits after an Int128 to BigInt payload replacement" begin
    q=-ldexp(1.0,115);n=6;L=zeros(n);Q=zeros(n,n)
    for i in 1:n,j in i+1:n;Q[i,j]=q;end
    ws=relation_workspace(L,Q,0.0,:spin,:min,1.0,:int128)
    QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+4)
    @test QUBOPreprocessing._payload_fits(ws._state.numeric)
    old=ws._state.numeric
    r=QUBOPreprocessing._step_relation_queue!(ws,typemax(Int),nothing,true,1,10000,10000,nothing)
    @test r[1]===:applied
    @test ws._state.numeric!==old
    @test eltype(ws._state.fields)===BigInt
    @test ws._state.promotions==1
    @test any(e isa QUBOPreprocessing._UndoReduction for e in ws._state.trail)
    @test last(ws._state.trail) isa QUBOPreprocessing._UndoQueue
    relation_record(:apply_payload_replacement,ws,r)
    relation_oracle(ws,L,Q,0.0,:spin,:min,1.0)
end

@testset "forward, reverse and nonadjacent twin branch lifetime" begin
    # Forward: the first queued vertex is the eliminated endpoint.
    L,Q,c=relation_input(:glk,:spin,:min,0.5)
    ws=relation_workspace(L,Q,c,:spin,:min,0.5,:int128)
    r=QUBOPreprocessing._step_relation_queue!(ws,typemax(Int),nothing,false,1,10000,10000,nothing)
    @test r[1]===:applied
    @test ws._state.fixed[1]==3
    relation_record(:forward_branch,ws,r)
    relation_oracle(ws,L,Q,c,:spin,:min,0.5)
    # Reverse: eliminating the first star center would exceed fill0, but a leaf
    # can contract into it. The reverse branch must not perform the forward pop.
    L=[10.0,0.0,0.0,0.0]
    Q=[0.0 -3.0 1.0 1.0;zeros(3,4)];c=0.0
    for backend in (:int128,:bigint)
        ws=relation_workspace(L,Q,c,:spin,:min,1.0,backend)
        beforehead=ws._state.rel_head
        r=QUBOPreprocessing._step_relation_queue!(ws,0,nothing,false,1,10000,10000,nothing)
        @test r[1]===:applied
        @test ws._state.fixed[1]==2 && ws._state.fixed[2]==3
        @test ws._state.rel_head==beforehead
        relation_record((:reverse_branch,backend),ws,r)
        relation_oracle(ws,L,Q,c,:spin,:min,1.0)
    end
    # Nonadjacent twins are tried after all adjacent orientations exceed fill0.
    L=zeros(5);Q=zeros(5,5)
    for i in 1:2,j in 3:5;Q[i,j]=1.0;end
    for backend in (:int128,:bigint)
        ws=relation_workspace(L,Q,c,:spin,:min,1.0,backend)
        r=QUBOPreprocessing._step_relation_queue!(ws,0,nothing,true,1,10000,10000,nothing)
        @test r[1]===:applied
        @test ws._state.fixed[1]==3 && ws._state.fixed[2]==2
        step=only(export_certificate(ws).steps)
        @test step.eliminated==1 && step.representative==2
        relation_record((:twin_branch,backend),ws,r)
        relation_oracle(ws,L,Q,c,:spin,:min,1.0)
    end
end
@testset "non-strict attempts retain the borrowed payload and fallback status" begin
    # With fill0, blocked adjacent pairs and non-strict witnesses are resumable.
    L=zeros(3);Q=[0.0 1.0 1.0;0.0 0.0 1.0;zeros(1,3)]
    for backend in (:int128,:bigint),weak in (false,true),fallback in (false,true)
        ws=relation_workspace(L,Q,0.0,:spin,:min,1.0,backend)
        payload=ws._state.numeric
        r=QUBOPreprocessing._step_relation_queue!(ws,typemax(Int),nothing,weak,1,10000,10000,nothing;allow_exact_fallback=fallback)
        r[1]===:applied || @test ws._state.numeric===payload
        relation_record((:fallback_status,backend,weak,fallback),ws,r)
        relation_oracle(ws,L,Q,0.0,:spin,:min,1.0)
    end
end
