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

@testset "Observer failures preserve committed progress and consume shared time" begin
    ws=Workspace(policy_tiny_model(:bool,:min);rules=:mixed)
    before=checkpoint(ws)
    observed=Ref{Any}(nothing)
    failure=ErrorException("observer failure after committed family")
    caught=try
        schedule_budgeted!(ws;time_limit=10,on_family=e->(observed[]=e;throw(failure)))
        nothing
    catch err
        err
    end
    @test caught===failure
    @test observed[].freed>0
    @test checkpoint(ws)==observed[].after_checkpoint!=before
    @test verify_certificate(ws,export_certificate(ws)).valid

    n=5
    vm=QT.VariableMap{Int}(Dict(i=>i for i in 1:n),collect(1:n))
    model=QT.Model{Int,Float64,Int}(vm,QT.Form{Float64}(n,
        QT.DenseLinearForm{Float64}(zeros(n)),
        QT.DictQuadraticForm{Float64}(Dict((i,j)=>1.0 for i in 1:n for j in i+1:n)),
        1.0,0.0;sense=:min,domain=:spin))
    events=Any[];callback_ns=Ref(UInt64(0))
    report=schedule_budgeted!(Workspace(model;rules=:mixed);time_limit=0.1,
        on_family=e->begin
            push!(events,e)
            start=time_ns()
            sleep(0.15) # Lower bound only: no fragile wall-clock upper bound.
            callback_ns[]+=time_ns()-start
        end)
    @test report.stop_reason===:deadline
    @test report.residual_variables>0
    @test length(events)==1 && only(events).family===:cheap
    @test report.elapsed_s>=callback_ns[]/1e9
    @test report.elapsed_s>=sum(f.time_s for f in report.families)+callback_ns[]/1e9
end


@testset "Census stops an unproductive second round before probing" begin
    # Metadata callback only: a productive first roof call justifies another
    # outer round, whose completed zero-deduction flow calls must stop before
    # a second probe. No model with these synthetic deductions is constructed.
    calls=Symbol[]
    function run(family)
        push!(calls,family)
        return family===:roof_duality && count(==(:roof_duality),calls)==1 ? 1 : 0
    end
    rounds=QUBOPreprocessing._run_legacy_policy!(run,()->true,:legacy_census,
        QUBOPreprocessing._legacy_policy_settings(:legacy_census,5,10))
    expected=[:reductions,:roof_duality,:submodular_cut,:maxcut,:reductions,
              :probing,:roof_duality,:submodular_cut,:maxcut]
    @test calls==expected
    @test rounds==2
    @test count(==(:probing),calls)==1
    @test count(==(:reductions),calls)==2
end

@testset "Unsolved strong policy executes and aggregates every enabled flow family" begin
    # The antiferromagnetic K5 has 20 ground states: every variable and every
    # pair product vary across them. Strong persistency cannot fix a variable
    # or contract a pair. Degree four excludes low-degree elimination. The
    # public input_edges override below is synthetic gate context only; it
    # disables blocks/probing without allocating a large graph.
    n=5
    pairs=[(i,j) for i in 1:n for j in i+1:n]
    model=QT.Model{Int,Float64,Int}(
        QT.VariableMap{Int}(Dict(i=>i for i in 1:n),collect(1:n)),
        QT.Form{Float64}(n,QT.DenseLinearForm{Float64}(zeros(n)),
            QT.DictQuadraticForm{Float64}(Dict(p=>1.0 for p in pairs)),
            0.5,0.125;sense=:min,domain=:spin))
    R=Rational{BigInt}
    # Independent original-coordinate polynomial, including physical scale
    # and offset. It uses no package objective or persistency implementation.
    original_energy(s)=R(1//2)*(R(1//8)+sum(s[i]*s[j] for (i,j) in pairs))
    states=[[isodd(mask >> (i-1)) ? 1 : -1 for i in 1:n] for mask in 0:31]
    energies=original_energy.(states)
    best=minimum(energies)
    optima=states[findall(==(best),energies)]
    @test best==-15//16
    @test length(optima)==20
    for i in 1:n
        @test Set(s[i] for s in optima)==Set((-1,1))
    end
    for (i,j) in pairs
        @test Set(s[i]*s[j] for s in optima)==Set((-1,1))
    end
    input_n,input_L,input_Q,input_scale,input_offset=QT.qubo(model,:dict;sense=:min,domain=:spin)
    input_snapshot=(input_n,Dict(input_L),Dict(input_Q),input_scale,input_offset)
    ws=Workspace(model;rules=:mixed,integerize_scale=false)
    before_generation=generation(ws)
    exact_before=policy_exact_state(ws)
    report=schedule!(ws;policy=:legacy_benchmark,allow_weak=false,input_edges=10001)
    @test report.policy===:legacy_benchmark && report.policy_version==1
    @test report.settings.initial_variables==5 && report.settings.initial_edges==10001
    @test !report.settings.enable_blocks && report.settings.enable_flow && !report.settings.enable_probing
    @test !report.settings.allow_weak && report.settings.tie_break===:low
    @test !report.settings.double_probe && !report.settings.contract_relations
    @test report.settings.relation_work_budget==typemax(Int)
    @test report.stop_reason===:policy_complete && report.passes==1
    @test report.initial_variables==report.residual_variables==5 && report.deductions==0
    @test [f.family for f in report.families]==[:reductions,:roof_duality,:submodular_cut,:maxcut]
    @test [f.calls for f in report.families]==[2,1,1,1]
    @test all(f.freed==0 && isfinite(f.time_s) && f.time_s>=0 for f in report.families)
    @test sum(f.freed for f in report.families)==report.deductions
    @test report.skipped_families==[:roof_scc,:blocks,:probing]
    @test generation(report)==before_generation
    @test policy_exact_state(ws)==exact_before
    @test export_certificate(ws)===nothing
    @test isempty(assumptions(ws))
    after_n,after_L,after_Q,after_scale,after_offset=QT.qubo(model,:dict;sense=:min,domain=:spin)
    @test (after_n,Dict(after_L),Dict(after_Q),after_scale,after_offset)==input_snapshot

    # Verify the exact residual and reconstruction on all 32 assignments in
    # original coordinates, independently of package objective evaluation.
    mat=materialize(ws;coefficient_type=R,map=domain_map(ws;domain=:bool))
    rn,L,Q,scale,offset=QT.qubo(export_model(mat),:dict;sense=:min,domain=:bool)
    @test rn==5 && length(Q)==10
    residual_energies=R[]
    for mask in 0:31
        b=[Int(isodd(mask >> (i-1))) for i in 1:rn]
        s=reconstruct(mat,b).state
        e=R(scale)*(R(offset)+sum(R(c)*b[i] for (i,c) in L)+
                   sum(R(c)*b[i]*b[j] for ((i,j),c) in Q))
        @test all(x in (-1,1) for x in s)
        @test e==original_energy(s)
        push!(residual_energies,e)
    end
    @test sort(residual_energies)==sort(energies)

    # A separate isolated unary variable forces one independently justified
    # strong fixing while leaving the same frustrated K5 residual. This gives
    # the repeated family report a real deduction and retained proof to audit.
    proof_model=QT.Model{Int,Float64,Int}(
        QT.VariableMap{Int}(Dict(i=>i for i in 1:6),collect(1:6)),
        QT.Form{Float64}(6,QT.DenseLinearForm{Float64}([0,0,0,0,0,3]),
            QT.DictQuadraticForm{Float64}(Dict(p=>1.0 for p in pairs)),
            0.5,0.125;sense=:min,domain=:spin))
    proof_ws=Workspace(proof_model;rules=:mixed,integerize_scale=false)
    proved=schedule!(proof_ws;policy=:legacy_benchmark,allow_weak=false,input_edges=10001)
    @test proved.initial_variables==6 && proved.residual_variables==5 && proved.deductions==1
    @test [f.calls for f in proved.families]==[2,1,1,1]
    @test [f.freed for f in proved.families]==[1,0,0,0]
    cert=export_certificate(proof_ws)
    @test cert!==nothing && length(cert.steps)==1 && isempty(cert.assumptions)
    @test verify_certificate(proof_ws,cert).valid
    proof_mat=materialize(proof_ws;coefficient_type=R,map=domain_map(proof_ws;domain=:bool))
    pn,pL,pQ,pscale,poffset=QT.qubo(export_model(proof_mat),:dict;sense=:min,domain=:bool)
    @test pn==5
    for mask in 0:31
        b=[Int(isodd(mask >> (i-1))) for i in 1:pn]
        s=reconstruct(proof_mat,b).state
        e=R(pscale)*(R(poffset)+sum(R(c)*b[i] for (i,c) in pL)+
                    sum(R(c)*b[i]*b[j] for ((i,j),c) in pQ))
        @test s[6]==-1
        @test e==original_energy(s)-3//2
    end
end
