# A bounded, deterministic test generator; no process-global RNG is used.
function trace_bits(seed)
    state = Ref(UInt64(seed))
    return () -> (state[] = state[] * UInt64(6364136223846793005) + UInt64(1442695040888963407))
end

function algebra_state(ws)
    st = ws._state
    return deepcopy((st.fields, st.constant, st.fixed, st.queue, st.queued,
                     [(e.index,e.value,e.constant,e.fields,e.queue_length) for e in st.trail]))
end

function check_conditioning(ws, labels, L, Q, alpha, beta, domain)
    fixed = Dict(assumptions(ws))
    free = [i for i in eachindex(labels) if !haskey(fixed, labels[i])]
    @test index_map(ws) == [something(findfirst(==(i), free), 0) for i in eachindex(labels)]
    result = isempty(fixed) ? materialize(ws) : materialize(ws; coefficient_type=Rational{BigInt})
    out = export_model(result)
    @test QT.variables(out) == labels[free]
    @test QT.domain(out) == ws._snapshot.domain
    @test QT.sense(out) == ws._snapshot.sense
    for y in states(length(free), domain)
        # Independent substitution directly in the original scalar expression.
        full = [haskey(fixed,label) ? fixed[label] : y[findfirst(==(i),free)] for (i,label) in enumerate(labels)]
        rec = reconstruct(result, y)
        @test rec.state == full
        @test rec.energy.value == reference(L,Q,alpha,beta,full)
        energy = Rational{BigInt}(QT.offset(out))
        for (j,i) in enumerate(free)
            energy += Rational{BigInt}(linear(out)[j]) * y[j]
            for k in j+1:length(free)
                energy += Rational{BigInt}(quadratic(out)[j,k]) * y[j]*y[k]
            end
        end
        @test Rational{BigInt}(QT.scale(out))*energy == reference(L,Q,alpha,beta,full,Rational{BigInt})
    end
    return result
end

@testset "reversible exact conditioning traces" begin
    labels = [(7,"z"), (1,"a"), (4,"middle"), (2,"isolate")]
    for kind in (:sparse,:dense,:dict), domain in (:bool,:spin), sense in (:min,:max), alpha in (0.0,-2.0,0.5)
        L = [0.5,-1.25,0.0,0.0]
        Q = [0.0 0.75 -0.5 0.0; 0.0 0.0 1.125 0.0; 0.0 0.0 0.0 0.0; 0.0 0.0 0.0 0.0]
        ws = Workspace(fixture(labels,L,Q; kind,domain,sense,scale=alpha,offset=-0.25))
        randbits = trace_bits(23)
        low = domain === :bool ? 0 : -1
        checkpoints = [(checkpoint(ws), algebra_state(ws))]
        for _ in 1:45
            choice = randbits() % 4
            if choice == 0 && length(checkpoints) > 1
                cp, expected = pop!(checkpoints)
                rollback!(ws,cp)
                @test algebra_state(ws) == expected
            elseif choice == 1 && !isempty(assumptions(ws))
                old = checkpoint(ws)
                fixed = assumptions(ws)
                victim = first(fixed)
                retained = fixed[2:end]
                @test unfix!(ws,first(victim)).stop_reason === :applied
                @test assumptions(ws) == retained
                @test_throws ArgumentError changes(ws,old)
                empty!(checkpoints)
                push!(checkpoints,(checkpoint(ws),algebra_state(ws)))
            else
                push!(checkpoints,(checkpoint(ws),algebra_state(ws)))
                i = Int(randbits() % 4) + 1
                existing = Dict(assumptions(ws))
                value = get(existing, labels[i], isodd(randbits()) ? 1 : low)
                r = assume!(ws,labels[i],value)
                @test r.stop_reason in (:applied,:unchanged)
            end
            check_conditioning(ws,labels,L,Q,alpha,-0.25,domain)
        end
    end
end

@testset "checkpoint validity, ownership and limits" begin
    m = fixture([:x,:y,:z], [1.0,2.0,3.0], [0.0 0.5 0.0; 0.0 0.0 1.0; 0.0 0.0 0.0])
    ws, other = Workspace(m), Workspace(m)
    root = checkpoint(ws)
    @test isempty(changes(ws,root))
    @test_throws ArgumentError rollback!(other,root)
    @test assume!(ws,:x,1; max_work=0).stop_reason === :work_limit
    @test assume!(ws,:x,1; deadline_ns=UInt64(0)).stop_reason === :deadline
    @test isempty(changes(ws,root))
    for invalid in (NaN,Inf,missing,2,0.5,nothing)
        @test_throws ArgumentError assume!(ws,:x,invalid)
    end
    @test_throws ArgumentError assume!(ws,:unknown,0)
    @test_throws ArgumentError assume!(ws,:x,1; max_work=-1)
    @test_throws ArgumentError assume!(ws,:x,1; deadline_ns=0.0)
    @test assume!(ws,:x,1).edge_visits == 1
    cp = checkpoint(ws)
    before = algebra_state(ws)
    @test assume!(ws,:x,1).stop_reason === :unchanged
    @test_throws ArgumentError assume!(ws,:x,0)
    @test algebra_state(ws) == before
    @test assume!(ws,:y,0).edge_visits == 2
    @test changes(ws,cp) == [:y=>0]
    @test assume!(ws,:z,1).stop_reason === :applied
    historical = materialize(ws)
    @test QT.dimension(export_model(historical)) == 0
    @test reconstruct(historical,Int[]).state == [1,0,1]
    @test_throws ArgumentError reconstruct(historical,[1])
    @test_throws ArgumentError reconstruct(historical,Dict())
    saved = checkpoint(ws)
    @test unfix!(ws,:x; max_work=0).stop_reason === :work_limit
    @test changes(ws,saved) == []
    @test unfix!(ws,:x; deadline_ns=UInt64(0)).stop_reason === :deadline
    rollback!(ws,cp)
    @test algebra_state(ws) == before
    @test_throws ArgumentError rollback!(ws,saved)
    assume!(ws,:y,0); assume!(ws,:z,1)
    @test_throws ArgumentError rollback!(ws,saved) # same depth, different lineage
    @test unfix!(ws,:x).stop_reason === :applied
    @test assumptions(ws) == [:y=>0,:z=>1]
    @test_throws ArgumentError rollback!(ws,root) # non-LIFO replay changes epoch
    @test reconstruct(historical,Int[]).state == [1,0,1]
    out = export_model(materialize(ws))
    linear(out)[1] = 99.0
    @test linear(export_model(materialize(ws)))[1] == 1
    cp = checkpoint(ws)
    oldgen = generation(ws)
    @test_throws ArgumentError reset!(ws,fixture([:x],[NaN],zeros(1,1)))
    @test generation(ws) == oldgen
    @test isempty(changes(ws,cp))
    reset!(ws,m)
    @test_throws ArgumentError rollback!(ws,cp)
    @test isempty(assumptions(ws))
    @test isempty(assumptions(other))
    empty = Workspace(fixture(Symbol[], Float64[], zeros(0,0)))
    @test rollback!(empty,checkpoint(empty)) === empty
    @test index_map(empty) == Int[]
end

@testset "numeric transport abstains instead of rounding" begin
    # 1 + 2^-53 cannot be represented as a Float64, although each input can.
    m = fixture([:x,:y], [0.0,1.0], [0.0 2.0^-53; 0.0 0.0])
    ws = Workspace(m)
    assume!(ws,:x,1)
    cp = checkpoint(ws)
    @test_throws ArgumentError materialize(ws)
    @test isempty(changes(ws,cp))
    out = export_model(materialize(ws; coefficient_type=Rational{BigInt}))
    @test linear(out)[1] == 1 + big(1)//big(2)^53
    @test_throws ArgumentError materialize(ws; coefficient_type=Float32)
    @test_throws ArgumentError reconstruct(materialize(ws; coefficient_type=Rational{BigInt}),[0.5])
    # Finite source coefficients can overflow when conditioned.
    ws = Workspace(fixture([:x,:y],[floatmax(Float64),floatmax(Float64)],zeros(2,2);offset=floatmax(Float64)))
    assume!(ws,:x,1)
    @test_throws ArgumentError materialize(ws)
    @test QT.offset(export_model(materialize(ws; coefficient_type=Rational{BigInt}))) == 2*Rational{BigInt}(floatmax(Float64))
end

function local_cycle(ws, cp)
    r = assume!(ws,1,1)
    rollback!(ws,cp)
    return r
end
function sparse_chain(n)
    labels = collect(1:n)
    vm = QT.VariableMap{Int}(Dict(i=>i for i in labels), labels)
    L = QT.DictLinearForm{Float64}(Dict{Int,Float64}())
    Q = QT.DictQuadraticForm{Float64}(Dict{Tuple{Int,Int},Float64}((i,i+1)=>0.5 for i in 1:n-1))
    return QT.Model{Int,Float64,Int}(vm, QT.Form{Float64}(n,L,Q))
end

@testset "local work does not scale with unrelated graph" begin
    small, large = Workspace(sparse_chain(10)), Workspace(sparse_chain(2000))
    a, b = checkpoint(small), checkpoint(large)
    for _ in 1:3
        local_cycle(small,a); local_cycle(large,b)
    end
    @test local_cycle(small,a).edge_visits == local_cycle(large,b).edge_visits == 1
    smallbytes = @allocated local_cycle(small,a)
    largebytes = @allocated local_cycle(large,b)
    @test largebytes <= smallbytes + 2048
    assume!(large,1,1)
    @test large._state.queue == [2]
    @test all(==(2), large._state.fixed[3:end])
    @test assume!(large,1,1; max_work=0).edge_visits == 0
    rollback!(large,b)
    @test isempty(large._state.queue)
    @test !any(large._state.queued)
end
