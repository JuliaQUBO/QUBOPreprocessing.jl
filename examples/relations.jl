using QUBOPreprocessing
import QUBOTools as QT

# Example: Certified pair relations (:interval, :exact, :glk_pair), reversible
# signed contractions, transitive relation_map, and fill-bounded cascades.

# 1. Glover-Lewis-Kochenberger (:glk_pair) triangle where no variable is fixed
#    by unary dominance and neither endpoint alone satisfies single-endpoint Rule 1:
m_glk = QT.Model(
    Dict(:u => 2.0, :v => 2.0, :w => 0.0),
    Dict((:u, :v) => -3.0, (:u, :w) => 2.0, (:v, :w) => 2.0);
    domain=:spin,
    sense=:min,
)

ws_dom = Workspace(m_glk; rules=:dominance)
@assert propagate!(ws_dom).deductions == 0

ws_glk, rep_glk = preprocess(m_glk; rules=:relations, cascade_dominance=true)
@assert rep_glk.stop_reason === :quiescent
@assert rep_glk.deductions == 3
cert_glk = export_certificate(ws_glk)
@assert first(cert_glk.steps) isa RelationStep
@assert first(cert_glk.steps).method === :glk_pair
@assert verify_certificate(ws_glk, cert_glk).valid

res_glk = materialize(ws_glk)
@assert QT.dimension(export_model(res_glk)) == 0
rec_glk = reconstruct(res_glk, Int[])
@assert rec_glk.state == [-1, -1, 1]
@assert rec_glk.energy.value == -11.0

# 2. Transitive signed contractions and non-compressing relation_map across checkpoints:
m_chain = QT.Model(
    Dict(:x1 => 0.0, :x2 => 0.0, :x3 => 1.0, :x4 => -1.0),
    Dict((:x1, :x2) => 10.0, (:x1, :x4) => 2.0, (:x2, :x3) => 20.0, (:x2, :x4) => 2.0, (:x3, :x4) => -3.0);
    domain=:spin,
    sense=:min,
)
ws_chain = Workspace(m_chain; rules=:relations)
cp0 = checkpoint(ws_chain)
@assert contract_relation!(ws_chain, :x1, :x2).stop_reason === :applied
cp1 = checkpoint(ws_chain)
@assert contract_relation!(ws_chain, :x2, :x3).stop_reason === :applied
@assert relation_map(ws_chain, :x1) == (:x3 => 1)
@assert relation_map(ws_chain, :x2) == (:x3 => -1)

rollback!(ws_chain, cp1)
@assert relation_map(ws_chain, :x1) == (:x2 => -1)
rollback!(ws_chain, cp0)
@assert relation_map(ws_chain) == [:x1 => 1, :x2 => 1, :x3 => 1, :x4 => 1]

println((glk_state=rec_glk.state, glk_energy=rec_glk.energy.value, steps=length(cert_glk.steps)))

