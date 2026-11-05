# Independent transcription of the two predecessor caller policies. This does
# not call the package's policy planner or dispatcher.
function legacy_policy_reference(run, alive, n, m, policy)
    middle = policy === :legacy_middle
    rel = (middle || n <= 500) ? typemax(Int) : (m > 15000 ? 25000 : (m > 5000 ? 75000 : typemax(Int)))
    blocks = middle || (n <= 1500 && m <= 10000)
    pass() = run(:reductions; allow_weak_dominance=true, allow_weak_relations=true,
                 enable_star_triangle=true, enable_blocks=blocks, relation_work_budget=rel)
    probe() = run(:probing; max_candidates=min(n,100), max_rounds=n<=100 ? 8 : 1,
                  max_trial_fixes=n<=100 ? 512 : 64, max_work=n<=100 ? 2000000 : 100000,
                  max_exact_work=n<=100 ? 2000000 : 100000, order=:coercive)
    pass()
    if policy !== :legacy_census
        if alive() && (middle || !(m>10000 && n>500))
            run(:roof_duality)
            alive() && run(:submodular_cut;allow_weak=true)
            alive() && run(:maxcut;allow_weak=true)
            alive() && pass()
            if m<=5000 && n<=500 && alive()
                probe()
                alive() && pass()
            end
        end
        return
    end
    post = 0
    for iter in 1:(m<=5000 && n<=500 ? 8 : 1)
        alive() && !(m>10000 && n>500) || break
        deductions = run(:roof_duality)
        alive() && (deductions += run(:submodular_cut;allow_weak=true))
        alive() && (deductions += run(:maxcut;allow_weak=true))
        deductions>0 && alive() && pass()
        iter>1 && deductions==0 && post==0 && break
        probed=0;post=0
        if m<=5000 && n<=500 && alive()
            probed=probe();deductions+=probed
        end
        if probed>0 && alive()
            post=pass();deductions+=post
        end
        deductions>0 || break
    end
end

@testset "Frozen policy threshold and call-order parity" begin
    for n in (100,101,500,501,1500,1501), m in (5000,5001,10000,10001,15000,15001),
        policy in (:legacy_benchmark,:legacy_middle,:legacy_census), productive in (false,true)
        old=Symbol[];new=Symbol[];old_options=Dict{Symbol,Any}()
        ref(f;kw...)=(push!(old,f);old_options[f]=(;kw...); productive ? 1 : 0)
        fresh(f)=(push!(new,f);productive ? 1 : 0)
        legacy_policy_reference(ref,()->true,n,m,policy)
        gates=QUBOPreprocessing._legacy_policy_settings(policy,n,m)
        QUBOPreprocessing._run_legacy_policy!(fresh,()->true,policy,gates)
        @test old==new
        @test old_options[:reductions].relation_work_budget==gates.relation_work_budget
        @test old_options[:reductions].enable_blocks==gates.enable_blocks
        if haskey(old_options,:probing)
            @test old_options[:probing].max_rounds==gates.probe_rounds
            @test old_options[:probing].max_candidates==gates.max_candidates
            @test old_options[:probing].max_trial_fixes==gates.max_trial_fixes
            @test old_options[:probing].max_work==gates.probe_work
        end
    end
    for policy in (:legacy_benchmark,:legacy_census), solve_at in 1:7
        old=Symbol[];new=Symbol[]
        legacy_policy_reference((f;kw...)->(push!(old,f);1),()->length(old)<solve_at,10,12,policy)
        QUBOPreprocessing._run_legacy_policy!(f->(push!(new,f);1),()->length(new)<solve_at,
            policy,QUBOPreprocessing._legacy_policy_settings(policy,10,12))
        @test old==new
    end
end

function policy_tiny_model(domain, sense)
    n=4
    lf=QT.DenseLinearForm{Float64}([-1.25,0.5,-2.0,1.0])
    qf=QT.DictQuadraticForm{Float64}(Dict((1,2)=>0.25,(2,3)=>-1.5,(3,4)=>0.75,(1,4)=>-0.5))
    vm=QT.VariableMap{Int}(Dict(i=>i for i in 1:n),collect(1:n))
    return QT.Model{Int,Float64,Int}(vm,QT.Form{Float64}(n,lf,qf,0.5,0.125;sense,domain))
end

function policy_exact_state(ws)
    mat=materialize(ws;coefficient_type=Rational{BigInt},map=domain_map(ws;domain=:bool))
    model=export_model(mat)
    n,L,Q,scale,offset=QT.qubo(model,:dict;sense=:min,domain=:bool)
    return (n,Dict(L),Dict(Q),scale,offset,index_map(mat),assumptions(ws))
end

@testset "Tiny coefficients, scope and default preservation" begin
    for weak in (false,true), domain in (:bool,:spin), sense in (:min,:max),
        policy in (:legacy_benchmark,:legacy_census,:legacy_middle)
        model=policy_tiny_model(domain,sense)
        old=Workspace(model;rules=:mixed,integerize_scale=false)
        new=Workspace(model;rules=:mixed,integerize_scale=false)
        assume!(old,1,1);assume!(new,1,1)
        function run(f;kw...)
            before=count(==(Int8(2)),old._state.fixed)
            opts=(;kw...)
            if f===:reductions
                schedule_reductions!(old;merge(opts,(allow_weak_dominance=weak,allow_weak_relations=weak))...)
            elseif f===:roof_duality
                apply_roof_duality!(old)
            elseif f===:submodular_cut
                apply_submodular_cut!(old;allow_weak=weak)
            elseif f===:maxcut
                apply_maxcut!(old;allow_weak=weak)
            else
                probe_variables!(old;opts...)
            end
            return before-count(==(Int8(2)),old._state.fixed)
        end
        legacy_policy_reference(run,()->any(==(Int8(2)),old._state.fixed),4,4,policy)
        report=schedule!(new;policy,allow_weak=weak,input_edges=4)
        @test policy_exact_state(new)==policy_exact_state(old)
        @test export_certificate(new).assumptions==export_certificate(old).assumptions
        @test [s.scope_length for s in export_certificate(new).steps]==[s.scope_length for s in export_certificate(old).steps]
        @test report.policy_version==1
        @test report.deductions==sum(f.freed for f in report.families;init=0)
        @test generation(report)==generation(new)
    end
    model=policy_tiny_model(:bool,:min)
    cheap=schedule!(Workspace(model;rules=:mixed);policy=:cheap)
    @test cheap.stop_reason===:cheap_quiescent
    @test :roof_duality in cheap.skipped_families
    @test :relations in cheap.skipped_families
    a=Workspace(model;rules=:mixed);b=Workspace(model;rules=:mixed)
    direct=schedule_budgeted!(a;time_limit=0)
    wrapped=schedule!(b;policy=:budgeted,time_limit=0)
    @test policy_exact_state(a)==policy_exact_state(b)
    @test direct.stop_reason===wrapped.stop_reason
    @test !wrapped.settings.double_probe && !wrapped.settings.contract_relations
    events=Any[]
    schedule_budgeted!(Workspace(model;rules=:mixed);time_limit=0,double_probe=true,
                      contract_relations=true,on_family=e->push!(events,e))
    @test length(events)==1
    @test events[1].family===:cheap
    @test events[1].before_checkpoint!=events[1].after_checkpoint
    @test_throws ArgumentError schedule!(b;policy=:unknown)
    @test_throws ArgumentError schedule!(b;time_limit=1)
    @test_throws ArgumentError schedule!(b;policy=:budgeted)
    @test_throws ArgumentError schedule_budgeted!(b;time_limit=0,on_family=4)
end
