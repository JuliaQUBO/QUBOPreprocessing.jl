using JuMP
import ToQUBO

function encoded_fixture(rules)
    model = Model(() -> ToQUBO.Optimizer(() -> QUBOPreprocessing.Optimizer(
        ScriptedChild.factory();rules,max_child_variables=8)))
    @variable(model,x,Bin)
    @variable(model,y,Bin)
    @variable(model,0<=u<=3,Int)
    @objective(model,Min,x-2y-u)
    constraint = @constraint(model,x>=1)
    return model,(x,y,u),constraint
end
function consumer_result(model)
    raw = MOI.get(backend(model),MOI.RawSolver())
    return MOI.get(raw,MOI.RawOptimizerAttribute("preprocessing_result")),raw
end
@testset "ToQUBO complete compiled bits, decoding and changed penalties" begin
    on,vars,constraint = encoded_fixture(:dominance)
    off,offvars,_ = encoded_fixture(:identity)
    optimize!(on);optimize!(off)
    r,raw = consumer_result(on)
    baseline,_ = consumer_result(off)
    state = round.(Int,value.(vars))
    @test state == round.(Int,value.(offvars)) == (1,1,3)
    @test state[1]>=1 && 0<=state[3]<=3 # independently evaluate source feasibility
    source_objective = state[1]-2state[2]-state[3]
    @test source_objective == -4
    @test objective_value(on) == source_objective
    @test r.optimal && baseline.optimal
    @test !r.metadata.child_called && baseline.metadata.child_called
    @test length(r.metadata.labels) == 4 # integer u has two compiled logical bits
    @test length(only(r.samples).state) == QT.dimension(QT.backend(raw)) == 4
    @test length(QT.state(QT.solution(raw),1)) == 4
    @test length(r.metadata.reduction_chain) == 4
    @test verify_certificate(r.workspace,r.exported.certificate.proof).valid
    @test only(r.samples).energy.value == Float64(ScriptedChild.scalar(QT.backend(raw),only(r.samples).state))
    oldproof = r.exported.certificate.proof
    oldstate = copy(only(r.samples).state)

    # Explicitly insufficient penalty is a diagnostic configuration, not a
    # default compiler failure. A compiled optimum need not be source-feasible.
    set_attribute(constraint,ToQUBO.Attributes.ConstraintEncodingPenaltyHint(),0.25)
    optimize!(on)
    changed,raw2 = consumer_result(on)
    newstate = round.(Int,value.(vars))
    @test newstate == (0,1,3)
    @test !(newstate[1]>=1)
    @test newstate[1]-2newstate[2]-newstate[3] == -5 # independent source objective
    @test changed.optimal # applies to the new compiled QUBO only
    @test only(changed.samples).energy.value == -4.75 # includes violated-constraint penalty
    @test generation(changed) != generation(r)
    @test !verify_certificate(changed.workspace,oldproof).valid
    @test only(r.samples).state == oldstate # owned historical evidence
    @test length(only(changed.samples).state) == QT.dimension(QT.backend(raw2)) == 4
end
