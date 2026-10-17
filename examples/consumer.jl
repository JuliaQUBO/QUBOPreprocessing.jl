# Run with --project=test/integration after developing this checkout there.
using QUBOPreprocessing
import QUBODrivers as QD
import QUBOTools as QT
import MathOptInterface as MOI

model = QT.Model(Dict(:x=>3.0,:y=>1.0,:isolate=>0.0),Dict((:x,:y)=>-2.0);offset=0.5)
used_child = Ref{Any}()
on = sample_preprocessed(model,()->(used_child[]=QD.ExactSampler.Optimizer());max_child_variables=8)
off = sample_preprocessed(model,QD.ExactSampler.Optimizer;rules=:identity,max_child_variables=8)
@assert minimum(x.energy.value for x in on.samples) == minimum(x.energy.value for x in off.samples) == 0.5
@assert all(length(x.state)==3 for x in on.samples)
@assert on.metadata.child_variables == 1 && off.metadata.child_variables == 3
@assert on.child_status == Symbol(string(MOI.get(used_child[],MOI.TerminationStatus())))
@assert on.optimal == (on.child_status === :OPTIMAL)
@assert verify_certificate(on.workspace,on.exported.certificate.proof).valid

# The same optional optimizer composes with ToQUBO. Restore every compiled bit
# before decoding the bounded integer. Source feasibility is checked separately.
using JuMP
import ToQUBO
source = Model(() -> ToQUBO.Optimizer(() -> QUBOPreprocessing.Optimizer(
    QD.ExactSampler.Optimizer;max_child_variables=8)))
@variable(source,x,Bin)
@variable(source,y,Bin)
@variable(source,0<=u<=3,Int)
@objective(source,Min,x-2y-u)
@constraint(source,x>=1)
optimize!(source)
state = round.(Int,value.((x,y,u)))
@assert state == (1,1,3)
@assert state[1]>=1 && 0<=state[3]<=3
@assert state[1]-2state[2]-state[3] == objective_value(source) == -4
raw = MOI.get(backend(source),MOI.RawSolver())
evidence = MOI.get(raw,MOI.RawOptimizerAttribute("preprocessing_result"))
@assert evidence.optimal && !evidence.metadata.child_called # all four bits were certified locally
@assert length(only(evidence.samples).state) == 4
println((direct_child_variables=on.metadata.child_variables,decoded=state,
         compiled_bits=length(evidence.metadata.labels),source_objective=-4))
