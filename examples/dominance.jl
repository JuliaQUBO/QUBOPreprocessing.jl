using QUBOPreprocessing
import QUBOTools as QT

# x=0 is strict; after it is installed, y=0 becomes strict. The zero isolate
# remains free, so quiescence alone is not a proof that a supplied state is optimal.
model = QT.Model(Dict(:x=>3.0,:y=>1.0,:isolate=>0.0),Dict((:x,:y)=>-2.0))
ws = Workspace(model;rules=:dominance)
root = checkpoint(ws)
first = propagate!(ws;max_deductions=1)
@assert first.stop_reason == :deduction_limit
@assert length(deductions(ws)) == 1
@assert verify_certificate(ws,export_certificate(ws)).valid
last = propagate!(ws)
@assert last.stop_reason == :quiescent
@assert Dict(deductions(ws)) == Dict(:x=>0,:y=>0)
@assert isempty(assumptions(ws))
@assert propagate!(ws).candidates == 0
result = materialize(ws)
@assert verify_certificate(ws,result.certificate.proof).valid
residual = export_model(result)
@assert QT.variables(residual) == [:isolate]
@assert reconstruct(result,[1]).state == [label === :isolate ? 1 : 0 for label in original_variables(result)]
rollback!(ws,root)
@assert isempty(deductions(ws))
@assert index_map(ws) == collect(1:3)
