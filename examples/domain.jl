using QUBOPreprocessing
import QUBOTools as QT

# Binary minimization model: 3x + y - 2x*y + 0.5 with an isolated variable.
model = QT.Model(Dict(:x => 3.0, :y => 1.0, :isolate => 0.0),
                 Dict((:x, :y) => -2.0); offset=0.5, domain=:bool, sense=:min)
ws = Workspace(model; rules=:dominance)
smap = domain_map(ws; domain=:spin, gauge=Dict(:x => -1, :y => 1, :isolate => 1))

@assert [degree(ws, v) for v in (:x, :y, :isolate)] == [1, 1, 0]
@assert effective_field(ws, :x; map=smap) == -1 // 1
@assert conditioned_constant(ws; map=smap) == 2 // 1

attempt = prove_dominance(ws, :x; map=smap)
@assert attempt.stop_reason == :proved
@assert verify_certificate(ws, attempt.certificate; map=smap).valid

root = checkpoint(ws)
propagate!(ws; map=smap)
@assert Dict(deductions(ws)) == Dict(:x => 0, :y => 0)
@assert degree(ws, :x) == 0 && degree(ws, :y) == 0
res = materialize(ws, smap)
@assert verify_certificate(ws, res.certificate.proof; map=smap).valid
residual = export_model(res)
@assert QT.domain(residual) == QT.SpinDomain
@assert QT.variables(residual) == [:isolate]
restored = reconstruct(res, [-1])
@assert Dict(zip(original_variables(res), restored.state)) == Dict(:x => 0, :y => 0, :isolate => 0)
@assert restored.energy.value == 0.5
rollback!(ws, root)
@assert [degree(ws, v) for v in (:x, :y, :isolate)] == [1, 1, 0]

