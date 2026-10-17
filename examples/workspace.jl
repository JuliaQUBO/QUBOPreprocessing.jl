using QUBOPreprocessing
import QUBOTools as QT

model = QT.Model(Dict(:x=>0.5,:y=>-1.0,:z=>0.0),
                 Dict((:x,:y)=>0.25,(:y,:z)=>0.5))
ws = Workspace(model)
root = checkpoint(ws)
@assert assume!(ws,:x,1; max_work=1).stop_reason == :applied
@assert changes(ws,root) == [:x=>1]
result = materialize(ws)
residual = export_model(result)
state = [label == :y ? 1 : 0 for label in QT.variables(residual)]
restored = reconstruct(result,state)
@assert Dict(zip(original_variables(result),restored.state)) == Dict(:x=>1,:y=>1,:z=>0)
@assert restored.energy.value == -0.25
rollback!(ws,root)
@assert isempty(assumptions(ws))
# Historical exports retain their original assumptions after workspace rollback.
@assert reconstruct(result,state).state == restored.state
