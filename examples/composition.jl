using QUBOPreprocessing
import QUBOTools as QT

# 3-variable binary minimization: F(x1, x2, x3) = 4x1 + 4x2 - 8x1*x2 + 2x1*x3 - x3.
# 1. RelationStep contracts x1 = x2 onto x2.
# 2. EliminationStep eliminates degree-1 neighbor x3 as a function of x2.
# 3. DominanceStep fixes x2 = 0 on the reduced residual.
# 4. Reconstruction unwinds (DominanceStep -> EliminationStep -> RelationStep) in reverse order.
model = QT.Model(Dict(:x1 => 4.0, :x2 => 4.0, :x3 => -1.0),
                 Dict((:x1, :x2) => -8.0, (:x1, :x3) => 2.0);
                 domain=:bool, sense=:min)
ws = Workspace(model; rules=:dominance)
root = checkpoint(ws)

@assert contract_relation!(ws, :x1, :x2).stop_reason == :applied
@assert eliminate_variable!(ws, :x3).stop_reason == :applied
@assert propagate!(ws).deductions == 1

cert = export_certificate(ws)
@assert [step_guarantee(s) for s in cert.steps] == [
    :optimum_preserving_restriction,
    :exact_elimination,
    :optimum_preserving_restriction,
]
@assert certificate_guarantee(cert) == :optimum_preserving_restriction
@assert persistency(cert) == :strong
@assert verify_certificate(ws, cert).valid

exported = materialize(ws)
@assert QT.dimension(export_model(exported)) == 0
restored = reconstruct(exported, Int[])
@assert Dict(zip(original_variables(exported), restored.state)) == Dict(:x1 => 0, :x2 => 0, :x3 => 1)
@assert restored.energy.value == -1.0

rollback!(ws, root)
@assert isempty(reductions(ws))

