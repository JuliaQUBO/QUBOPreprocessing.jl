@testset "certified incumbent survives public container normalization" begin
    for domain in (:bool,:spin),sense in (:min,:max),offset in (1e8,2.0^54)
        model = QT.Model(Dict(MOI.VariableIndex(1)=>1.0),
            Dict{Tuple{MOI.VariableIndex,MOI.VariableIndex},Float64}();domain,sense,offset)
        child = ScriptedChild.factory(:ranked)()
        QD.set_model!(child,deepcopy(model));MOI.optimize!(child)
        best = Int(MOI.get(child,MOI.VariablePrimal(1),MOI.VariableIndex(1)))
        @test MOI.get(child,MOI.TerminationStatus()) === MOI.OPTIMAL
        @test ScriptedChild.scalar(model,[best]) == independent_optimum(model)
        direct = sample_preprocessed(model,ScriptedChild.factory(:ranked);rules=:identity)
        @test direct.optimal && first(direct.samples).state == [best]
        @test length(direct.samples)==2 && direct.reads==[1,2]
        opt = Optimizer(ScriptedChild.factory(:ranked);rules=:identity)
        QD.set_model!(opt,deepcopy(model));MOI.optimize!(opt)
        @test MOI.get(opt,MOI.TerminationStatus()) === MOI.OPTIMAL
        actual = Int(MOI.get(opt,MOI.VariablePrimal(1),MOI.VariableIndex(1)))
        @test actual == best
        @test ScriptedChild.scalar(model,[actual]) == independent_optimum(model)
        @test MOI.get(opt,MOI.ResultCount()) == 1
        @test QT.reads(QT.solution(opt),1) == 1
        metadata = QT.metadata(QT.solution(opt))
        @test metadata["reads"]["number_of_reads"] == 1
        @test metadata["reads"]["final_number_of_reads"] == 1
        @test length(MOI.get(opt,MOI.RawOptimizerAttribute("preprocessing_result")).samples)==2
    end
end

@testset "zero result cap includes local reconstruction" begin
    for model in (QT.Model(Dict(:x=>1.0),Dict{Tuple{Symbol,Symbol},Float64}()),
                  QT.Model(Dict{Int,Float64}(),Dict{Tuple{Int,Int},Float64}();offset=2.0))
        r = sample_preprocessed(model,()->error("no local child dispatch");max_results=0)
        @test r.stop_reason === :result_limit
        @test isempty(r.samples) && isempty(r.reads)
        @test !r.optimal && !r.scope_optimal
        @test !r.metadata.child_called
    end
end

module DeadlineLabels
const copies = Ref(0)
const wait_at = Ref(0)
const until = Ref(UInt64(0))
mutable struct Label
    id::Int
end
Base.isequal(a::Label,b::Label) = a.id==b.id
Base.:(==)(a::Label,b::Label) = a.id==b.id
Base.hash(a::Label,h::UInt) = hash(a.id,h)
function Base.deepcopy_internal(x::Label,dict::IdDict)
    haskey(dict,x) && return dict[x]
    copies[] += 1
    if copies[] == wait_at[]
        while time_ns() <= until[];sleep(0.001);end
    end
    y=Label(x.id);dict[x]=y
    return y
end
const factory = () -> error("all-fixed deadline fixture must remain local")
end

@testset "final evidence copying observes the deadline" begin
    labels = [DeadlineLabels.Label(1)]
    vm = QT.VariableMap{DeadlineLabels.Label}(Dict(labels[1]=>1),labels)
    form = QT.Form{Float64}(1,QT.DictLinearForm{Float64}(Dict(1=>1.0)),
        QT.DictQuadraticForm{Float64}(Dict{Tuple{Int,Int},Float64}()))
    model = QT.Model{DeadlineLabels.Label,Float64,Int}(vm,form)
    ws = Workspace(model;rules=:dominance)
    for _ in 1:3
        DeadlineLabels.copies[]=0
        warm = sample_preprocessed(ws,DeadlineLabels.factory;
            deadline_ns=time_ns()+UInt64(30_000_000_000))
        @test warm.optimal
    end
    # Delay the final owned-label copy found by the warmed public call. This
    # avoids mistaking initial compilation for a completed late-copy boundary.
    DeadlineLabels.wait_at[]=DeadlineLabels.copies[]
    @test DeadlineLabels.wait_at[] > 0
    DeadlineLabels.copies[]=0
    DeadlineLabels.until[]=time_ns()+UInt64(500_000_000)
    late = sample_preprocessed(ws,DeadlineLabels.factory;deadline_ns=DeadlineLabels.until[])
    @test DeadlineLabels.copies[] >= DeadlineLabels.wait_at[]
    @test time_ns() > DeadlineLabels.until[]
    @test late.stop_reason === :deadline
    @test !late.optimal && !late.scope_optimal
    @test !late.metadata.child_called
    DeadlineLabels.wait_at[]=0
end
