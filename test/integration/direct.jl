function independent_optimum(model;scope=Dict())
    n = QT.dimension(model)
    n <= 8 || throw(ArgumentError("oracle requires n<=8 before exponentiation"))
    low = QT.domain(model) === QT.BoolDomain ? 0 : -1
    values = Rational{BigInt}[]
    labels = QT.variables(model)
    for mask in 0:(1<<n)-1
        state = [isodd(mask>>(i-1)) ? 1 : low for i in 1:n]
        all(!haskey(scope,labels[i]) || state[i]==scope[labels[i]] for i in 1:n) || continue
        push!(values,ScriptedChild.scalar(model,state))
    end
    return QT.sense(model) === QT.Min ? minimum(values) : maximum(values)
end

@testset "exact direct on/off domain/sense/scale/label parity" begin
    labels = [(9,"x"),(1,"y"),(4,"tie")]
    for domain in (:bool,:spin),sense in (:min,:max),scale in (-2.0,0.0,0.5),rules in (:identity,:dominance,:elimination,:relations,:mixed)
        model = QT.Model(Dict(labels[1]=>3.0,labels[2]=>1.0,labels[3]=>0.0),
                         Dict((labels[1],labels[2])=>-2.0);domain,sense,scale,offset=0.75)
        r = sample_preprocessed(model,ScriptedChild.factory();rules,enable_star_triangle=(rules === :mixed))
        @test r.optimal && r.scope_optimal
        @test r.scope === :original
        @test r.stop_reason === :optimal
        @test generation(r) == generation(r.exported)
        @test r.metadata.labels == QT.variables(model)
        @test r.metadata.scale == scale
        @test r.metadata.offset == 0.75
        @test r.metadata.domain == QT.domain(model)
        @test r.metadata.sense == QT.sense(model)
        @test r.metadata.total_seconds >= sum(values(r.metadata.phases))
        @test all(length(x.state)==3 && x.energy.finite for x in r.samples)
        @test ScriptedChild.scalar(model,first(r.samples).state) == independent_optimum(model)
        @test all(x.energy.value == Float64(ScriptedChild.scalar(model,x.state)) for x in r.samples)
        @test length(r.samples) == length(r.reads)
    end
end

@testset "scope, status and invalid child results" begin
    model = QT.Model(Dict(:x=>1.0,:y=>0.0),Dict((:x,:y)=>-2.0))
    ws = Workspace(model;rules=:dominance)
    assume!(ws,:y,0)
    r = sample_preprocessed(ws,()->error("all-fixed must not dispatch"))
    @test r.scope_optimal && !r.optimal
    @test r.scope === :assumptions && r.stop_reason === :scope_optimal
    @test !r.metadata.child_called
    @test r.metadata.caller_assumptions == (QT.index(model,:y)=>0,)
    @test length(r.metadata.reduction_chain) == 1
    @test only(r.metadata.reduction_chain).variable == QT.index(model,:x)
    @test ScriptedChild.scalar(model,only(r.samples).state) == independent_optimum(model;scope=Dict(:y=>0))
    old = r.exported.certificate.proof
    reset!(ws,model)
    @test !verify_certificate(ws,old).valid
    @test generation(ws) != generation(r)

    nofix = QT.Model(Dict(:a=>0.0,:b=>0.0),Dict((:a,:b)=>-1.0))
    for (mode,reason,has_samples) in ((:heuristic,:feasible,true),(:empty,:empty_child,false),
            (:partial,:malformed_child,false),(:invalid,:malformed_child,false),
            (:invalid_first,:feasible,true),(:timeout,:child_timeout,true),
            (:failure_incumbent,:child_failure,true))
        got = sample_preprocessed(nofix,ScriptedChild.factory(mode))
        @test got.stop_reason === reason
        @test !got.optimal && !got.scope_optimal
        @test !isempty(got.samples) == has_samples
        @test all(all(v in (0,1) for v in x.state) for x in got.samples)
    end
    ordinary = sample_preprocessed(nofix,QD.ExactSampler.Optimizer)
    public_child = QD.ExactSampler.Optimizer()
    v = MOI.VariableIndex.(1:2)
    QD.set_model!(public_child,QT.Model(Dict(v[1]=>0.0,v[2]=>0.0),Dict((v[1],v[2])=>-1.0)))
    MOI.optimize!(public_child)
    public_status = MOI.get(public_child,MOI.TerminationStatus())
    @test ordinary.child_status === Symbol(string(public_status))
    @test ordinary.optimal == (public_status === MOI.OPTIMAL)
    @test ScriptedChild.scalar(nofix,first(ordinary.samples).state) == independent_optimum(nofix)
    fully = QT.Model(Dict(:a=>1.0,:b=>2.0),Dict{Tuple{Symbol,Symbol},Float64}();offset=0.5)
    @test sample_preprocessed(fully,()->error("all-fixed dispatch")).optimal
    empty_model = QT.Model(Dict{Int,Float64}(),Dict{Tuple{Int,Int},Float64}();offset=2.0)
    e = sample_preprocessed(empty_model,()->error("empty dispatch"))
    @test e.optimal && only(e.samples).state == Int[] && only(e.samples).energy.value == 2
end

@testset "shared allowance, capacity and exact-export refusals" begin
    model = QT.Model(Dict(:x=>3.0,:y=>1.0,:tie=>0.0),Dict((:x,:y)=>-2.0))
    calls = Ref(0)
    factory = () -> (calls[]+=1;ScriptedChild.Optimizer())
    @test sample_preprocessed(model,factory;max_work=0).stop_reason === :work_limit
    @test calls[] == 0
    @test sample_preprocessed(model,factory;deadline_ns=UInt64(0)).stop_reason === :deadline
    @test calls[] == 0
    @test sample_preprocessed(model,factory;max_child_variables=0).stop_reason === :capacity_limit
    @test calls[] == 0
    @test sample_preprocessed(model,factory;max_results=0).stop_reason === :result_limit
    @test calls[] == 0
    unsupported = sample_preprocessed(model,factory;max_work=100_000)
    @test unsupported.stop_reason === :unsupported_work_limit && !unsupported.metadata.child_called
    limit_seen=Ref{Any}(nothing)
    bound = (child,residual,remaining,deadline) -> begin
        limit_seen[]=(remaining,deadline)
        1<<QT.dimension(residual) # this tiny scripted child completes exactly these assignments
    end
    r = sample_preprocessed(model,factory;max_work=100_000,child_work_bound=bound,
                            deadline_ns=time_ns()+UInt64(30_000_000_000))
    @test r.optimal
    @test r.metadata.work_used+r.metadata.work_remaining == 100_000
    @test r.metadata.child_work_reserved == 2
    @test limit_seen[][1] > 2 && limit_seen[][2] isa UInt64
    @test 0 < ScriptedChild.limits[] <= 30
    builtin = sample_preprocessed(model,QD.ExactSampler.Optimizer;max_work=100_000)
    @test builtin.metadata.child_called && builtin.metadata.work_used <= 100_000
    @test builtin.metadata.child_work_reserved > 0
    interrupted = sample_preprocessed(model,ScriptedChild.factory();max_deductions=0)
    @test interrupted.optimal && isempty(interrupted.metadata.reduction_chain)
    @test interrupted.metadata.propagation.stop_reason === :deduction_limit
    unsafe = Workspace(QT.Model(Dict(:x=>-2.0,:y=>1.0),Dict((:x,:y)=>2.0^-53)))
    assume!(unsafe,:x,1)
    before = calls[]
    @test sample_preprocessed(unsafe,factory).stop_reason === :unsafe_export
    @test calls[] == before
    @test_throws ArgumentError sample_preprocessed(model,factory;max_work=-1)
    @test_throws ArgumentError sample_preprocessed(model,()->:badchild)
    @test_throws ArgumentError sample_preprocessed(Workspace(model),factory;rules=:dominance)
    # Every source refresh produces a new generation even with unchanged shape.
    a = sample_preprocessed(model,ScriptedChild.factory())
    b = sample_preprocessed(model,ScriptedChild.factory())
    @test generation(a) != generation(b)

    # Find bounded interruptions at the actual exported/child/lifting boundaries,
    # independently of their implementation-specific reservation constants.
    nofix = QT.Model(Dict(:a=>0.0,:b=>0.0),Dict((:a,:b)=>-1.0))
    stopped = Dict{Symbol,SolverResult}()
    for allowance in 1:512
        partial = sample_preprocessed(nofix,ScriptedChild.factory();max_work=allowance,
                                     child_work_bound=(child,residual,remaining,deadline)->4)
        @test partial.metadata.work_used <= allowance
        if partial.stop_reason === :work_limit
            phase = partial.metadata.stopped_phase
            if phase === :materialization || phase === :reconstruction && !isempty(partial.samples)
                stopped[phase] = partial
            end
        end
        length(stopped)==2 && break
    end
    @test Set(keys(stopped)) == Set((:materialization,:reconstruction))
    @test !stopped[:materialization].metadata.child_called
    @test stopped[:materialization].exported === nothing
    retained = stopped[:reconstruction]
    @test retained.metadata.child_called && !retained.optimal
    @test ScriptedChild.scalar(nofix,first(retained.samples).state) == independent_optimum(nofix)
    @test sample_preprocessed(model,ScriptedChild.factory();max_exact_work=0).optimal
    oversized_exact = QT.Model(Dict(i=>0.0 for i in 1:21),Dict{Tuple{Int,Int},Float64}();scale=0.0)
    refused = sample_preprocessed(oversized_exact,QD.ExactSampler.Optimizer;max_child_variables=64)
    @test refused.stop_reason === :capacity_limit && !refused.metadata.child_called
    overflow = QT.Model(Dict(:a=>1.0),Dict{Tuple{Symbol,Symbol},Float64}();offset=1e308,scale=1e308)
    nonfinite = sample_preprocessed(overflow,()->error("all-fixed must remain local"))
    @test nonfinite.stop_reason === :nonfinite_energy
    @test !nonfinite.optimal && isempty(nonfinite.samples)
end

@testset "batch reconstruction reuses original storage" begin
    function reconstruction_bytes(n)
        lf = QT.DenseLinearForm{Float64}(zeros(n))
        qf = QT.DenseQuadraticForm{Float64}(QUBOPreprocessing.UpperTriangular(zeros(n,n)))
        form = QT.Form{Float64}(n,lf,qf,1.0,0.0;sense=:min,domain=:bool)
        model = QT.Model{Int,Float64,Int}(QT.VariableMap{Int}(collect(1:n)),form)
        result = materialize(Workspace(model))
        evaluator = QUBOPreprocessing._source_evaluator(result._snapshot)
        y=zeros(Int,n)
        for _ in 1:3;QUBOPreprocessing._reconstruct(result,y,evaluator);end
        @test QUBOPreprocessing._reconstruct(result,y,evaluator).state == reconstruct(result,y).state
        return @allocated QUBOPreprocessing._reconstruct(result,y,evaluator)
    end
    small,large = reconstruction_bytes(10),reconstruction_bytes(200)
    @test large <= small+8192 # complete state storage grows; the dense graph is not copied per sample
end
