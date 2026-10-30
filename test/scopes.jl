@testset "removed-fixing reports retain provenance" begin
    model = fixture([:x,:y,:z],[1.0,0.0,0.0],[0.0 -2.0 0.0;0.0 0.0 0.0;0.0 0.0 0.0])
    ws = Workspace(model;rules=:dominance)
    propagate!(ws)
    root = checkpoint(ws)
    assume!(ws,:y,0);propagate!(ws)
    branch = checkpoint(ws)
    proof = export_certificate(ws)
    assume!(ws,:z,1)
    report = rollback!(ws,root;report=true)
    @test generation(report) == generation(ws)
    @test report.checkpoint == root
    @test report.caller_unfixed == [3=>1,2=>0]
    @test report.deduction_unfixed == [1=>0]
    @test isempty(assumptions(ws)) && isempty(deductions(ws))
    @test !verify_certificate(ws,proof).valid
    @test_throws ArgumentError rollback!(ws,branch;report=true)
    @test_throws ArgumentError rollback!(Workspace(model;rules=:dominance),root;report=true)
    @test isempty(rollback!(ws,root;report=true).deduction_unfixed)
    empty!(report.caller_unfixed) # owned return values do not mutate the workspace
    @test isempty(assumptions(ws))
    assume!(ws,:y,1);propagate!(ws)
    @test deductions(ws) == [:x=>1]
    allfixed = materialize(ws)
    @test reconstruct(allfixed,[0]).state == [1,1,0]
    reset!(ws,model)
    @test_throws ArgumentError rollback!(ws,root;report=true)
end

function compare_fresh_scope(ws,model,labels,L,Q,scale,offset,domain,sense)
    # The oracle uses original scalar expressions, not the fresh producer.
    check_engine(ws,labels,L,Q,scale,offset,domain,sense)
    fresh = Workspace(model;rules=:dominance)
    for (label,value) in assumptions(ws); assume!(fresh,label,value); end
    propagate!(fresh)
    expected = Dict(deductions(fresh))
    @test all(get(expected,label,nothing) == value for (label,value) in deductions(ws))
    check_engine(fresh,labels,L,Q,scale,offset,domain,sense)
    return fresh
end

@testset "bounded randomized branch/backtrack/replay traces" begin
    labels = [(i,"original") for i in 1:6]
    L = [1.0,0.0,2.0,0.0,0.0,0.0]
    Q = zeros(6,6);Q[1,2]=-2.0;Q[3,4]=-3.0;Q[5,6]=1.0
    for domain in (:bool,:spin), sense in (:min,:max), scale in (-2.0,0.0,0.5), seed in (41,913)
        model = fixture(labels,L,Q;domain,sense,scale,offset=-0.25)
        ws = Workspace(model;rules=:dominance)
        random = trace_bits(seed)
        low = domain === :bool ? 0 : -1
        stack = [(checkpoint(ws),engine_state(ws))]
        counts = Dict(k=>0 for k in (:pin,:rollback,:replay,:propagate,:conflict,:repeat))
        touched = Set{Int}()
        # Force a non-LIFO replay with multiple retained pins before random draws.
        for i in (2,4,6); assume!(ws,labels[i],low); end
        propagate!(ws;max_deductions=1)
        @test unfix!(ws,labels[2]).stop_reason === :applied
        counts[:replay] += 1
        empty!(stack);push!(stack,(checkpoint(ws),engine_state(ws)))
        for step in 1:60
            action = Int(random()%6)
            free = findall(==(2),ws._state.fixed)
            if action == 0 && length(stack)>1
                cp,expected = pop!(stack)
                caller = reverse(changes(ws,cp))
                inferred = reverse(deductions(ws;since=cp))
                report = rollback!(ws,cp;report=true)
                indexpairs(pairs) = [findfirst(==(label),labels)=>value for (label,value) in pairs]
                @test report.caller_unfixed == indexpairs(caller)
                @test report.deduction_unfixed == indexpairs(inferred)
                @test engine_state(ws) == expected
                counts[:rollback] += 1
            elseif action == 1 && length(assumptions(ws))>=2
                stale = checkpoint(ws)
                retained = assumptions(ws)[2:end]
                @test unfix!(ws,first(first(assumptions(ws)))).stop_reason === :applied
                @test assumptions(ws) == retained
                @test isempty(deductions(ws))
                @test_throws ArgumentError rollback!(ws,stale)
                empty!(stack);push!(stack,(checkpoint(ws),engine_state(ws)))
                counts[:replay] += 1
            elseif action == 2
                limits = random()%3
                r = limits == 0 ? propagate!(ws;max_work=2) :
                    limits == 1 ? propagate!(ws;max_exact_work=5) : propagate!(ws;max_deductions=1)
                @test r.stop_reason in (:quiescent,:work_limit,:verification_limit,:deduction_limit)
                counts[:propagate] += 1
            elseif action in (3,4) && any(!=(2),ws._state.fixed)
                fixed = findall(!=(2),ws._state.fixed)
                i = fixed[Int(random()%length(fixed))+1]
                value = Int(ws._state.fixed[i])
                before = engine_state(ws)
                if action == 3
                    @test assume!(ws,labels[i],value).stop_reason === :unchanged
                    counts[:repeat] += 1
                else
                    @test_throws ArgumentError assume!(ws,labels[i],low+1-value)
                    counts[:conflict] += 1
                end
                @test engine_state(ws) == before
            elseif !isempty(free)
                push!(stack,(checkpoint(ws),engine_state(ws)))
                i = free[Int(random()%length(free))+1]
                @test assume!(ws,labels[i],isodd(random()) ? 1 : low).stop_reason === :applied
                push!(touched,i);counts[:pin] += 1
            else
                propagate!(ws)
            end
            compare_fresh_scope(ws,model,labels,L,Q,scale,-0.25,domain,sense)
        end
        # Coverage is measured from executed operations, not nominal RNG draws.
        @test all(counts[k]>0 for k in keys(counts))
        @test length(touched)>=3
        r = propagate!(ws)
        fresh = compare_fresh_scope(ws,model,labels,L,Q,scale,-0.25,domain,sense)
        @test Dict(deductions(ws)) == Dict(deductions(fresh))
        @test propagate!(ws).candidates == 0
        # Work totals retain executed work across all backtracking and replay.
        @test ws._state.total_candidates >= r.candidates
    end
end

@testset "rollback capture has local allocation shape" begin
    function cycle_with_capture(ws,cp)
        assume!(ws,1,1)
        propagate!(ws)
        return rollback!(ws,cp;report=true)
    end
    a,b = Workspace(sparse_chain(10);rules=:dominance),Workspace(sparse_chain(2000);rules=:dominance)
    propagate!(a);propagate!(b)
    x,y = checkpoint(a),checkpoint(b)
    for _ in 1:3;cycle_with_capture(a,x);cycle_with_capture(b,y);end
    @test cycle_with_capture(b,y).deduction_unfixed == [2=>0]
    small = @allocated cycle_with_capture(a,x)
    large = @allocated cycle_with_capture(b,y)
    @test large <= small+2048
    @test isempty(rollback!(b,y;report=true).caller_unfixed)
end

@testset "deduction-matched assumptions survive a later structural rollback (#71)" begin
    L = Dict(5 => 1/3, 4 => 1.0, 6 => 2.0, 2 => -4.0, 3 => 1.0, 1 => 1/3)
    Q = Dict((4, 5) => 3.0, (1, 2) => -0.25, (6, 8) => 4.0, (2, 5) => 2.0, (1, 3) => 2/3,
             (3, 8) => 4.0, (2, 6) => -1.0, (7, 8) => -0.25, (4, 7) => 0.5, (3, 4) => -2.0,
             (5, 6) => -1.0, (2, 7) => 4.0, (2, 8) => 0.75, (5, 7) => -2/3, (1, 6) => -0.5,
             (3, 5) => -1/3, (5, 8) => -2/3, (2, 4) => -0.5, (1, 7) => 3.5, (3, 6) => 0.75,
             (6, 7) => -3.0, (1, 8) => 4.0)
    model = QT.Model{Int,Float64,Int}(L, Q; domain=:bool, sense=:min)
    function lifted_states(ws)
        res = materialize(ws; coefficient_type=Rational{BigInt})
        nr = QT.dimension(export_model(res))
        return [reconstruct(res, [(k >> (b - 1)) & 1 for b in 1:nr]).state for k in 0:(2^nr - 1)]
    end

    ws = Workspace(model; rules=:mixed)
    schedule_reductions!(ws)
    @test (1 => 0) in deductions(ws)
    @test !(2 in first.(deductions(ws))) # x2 is removed structurally, not fixed
    # Matching a deduction is still a no-op that does not enter the caller scope.
    @test assume!(ws, 1, 0).stop_reason === :unchanged
    @test assume!(ws, 1, 0).stop_reason === :unchanged # repeats do not duplicate
    @test isempty(assumptions(ws))
    cert = export_certificate(ws)
    @test isempty(cert.assumptions)
    @test verify_certificate(ws, cert).valid
    # The structural rollback replays the matched request as a caller assumption.
    r = assume!(ws, 2, 1)
    @test r.stop_reason === :applied
    @test r.changed == 2
    @test assumptions(ws) == [1 => 0, 2 => 1]
    @test all(s -> s[1] == 0 && s[2] == 1, lifted_states(ws))
    schedule_reductions!(ws)
    @test all(s -> s[1] == 0 && s[2] == 1, lifted_states(ws))
    @test verify_certificate(ws, export_certificate(ws)).valid

    # A request made after a checkpoint is discarded by rolling back to it.
    ws = Workspace(model; rules=:mixed)
    schedule_reductions!(ws)
    cp = checkpoint(ws)
    assume!(ws, 1, 0)
    rollback!(ws, cp)
    @test assume!(ws, 2, 1).stop_reason === :applied
    @test assumptions(ws) == [2 => 1]
end
