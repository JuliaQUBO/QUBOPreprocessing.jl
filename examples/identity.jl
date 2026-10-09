using QUBOPreprocessing
import QUBOTools as QT

# Declared zero coefficients keep isolates in the source model.
model = QT.Model(Dict("x"=>1.5, "y"=>-2.0, "isolate"=>0.0),
                 Dict(("x","y")=>0.25); scale=-2.0, offset=0.5,
                 sense=:max, domain=:bool)
ws, report = preprocess(model; rules=:identity)
@assert report.stop_reason === :quiescent
result = materialize(ws)
solver_model = export_model(result)
@assert QT.variables(solver_model) == original_variables(result)
state = [v == "y" ? 1 : 0 for v in original_variables(result)]
restored = reconstruct(result, state)
@assert restored.state == state
@assert restored.energy.value == 3.0 # -2 * (0.5 - 2)
@assert restored.energy.finite
@assert result.certificate.reduction_chain == ()
println("Original labels: ", original_variables(result))
println("Original state: ", restored.state, "; numerical energy: ", restored.energy.value)
# The valid state above is not supplied with an optimality certificate.
