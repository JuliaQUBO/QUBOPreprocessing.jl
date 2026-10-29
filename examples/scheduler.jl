using QUBOPreprocessing
import QUBOTools as QT

# Example: Mixed exact reduction pass scheduling (issue #20) on a shared
# Workspace and Generation, with incremental fill/work budgets, optional
# degree-3 star-triangle gating, and full 7-phase pipeline accounting.

L = Dict(1 => 5.0, 2 => 0.5, 3 => 0.25, 4 => -0.25, 5 => 0.0, 6 => 0.25, 7 => -0.5)
Q = Dict(
    (1, 2) => 1.0, (2, 3) => -0.5, (3, 4) => -6.0,
    (3, 5) => 0.5, (3, 6) => 0.5,  (4, 5) => 0.5,
    (4, 6) => 0.5, (4, 7) => 1.0,  (5, 6) => 1.0,
    (5, 7) => 1.0, (6, 7) => 1.0,
)
model = QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)

# 1. Default mixed schedule runs cheap dirty-neighborhood propagation (:dominance)
#    and degree <= 2 local elimination (:elimination) first, then bounded pair
#    relations (:relations), keeping degree-3 :star_triangle disabled by default:
ws, rep_cheap = preprocess(model; rules=:mixed)
@assert rep_cheap.stop_reason === :quiescent
@assert rep_cheap.dominance_deductions >= 1
@assert rep_cheap.elimination_deductions >= 1
@assert rep_cheap.relation_deductions >= 1
@assert rep_cheap.star_triangle_deductions == 0
@assert :star_triangle in rep_cheap.optional_passes_disabled

# 2. Enabling optional :star_triangle on the same Workspace/Generation continues
#    incrementally and cascades the remaining degree-3/2/1/0 residual to 0 variables:
rep_star = schedule_reductions!(ws; enable_star_triangle=true)
@assert rep_star.stop_reason === :quiescent
@assert rep_star.star_triangle_deductions >= 1
@assert rep_star.residual_variables == 0
@assert verify_certificate(ws, export_certificate(ws)).valid

res = materialize(ws; coefficient_type=Rational{BigInt})
@assert QT.dimension(export_model(res)) == 0
rec = reconstruct(res, Int[])
@assert rec.energy.finite

# 3. Full 7-phase pipeline accounting (conversion/import, discovery, arithmetic
#    fallback, verification, export, reconstruction, and rollback/replay):
_, acct = audit_pipeline!(model; rules=:mixed, enable_star_triangle=true, domain=:bool, gauge=[-1, 1, -1, 1, -1, 1, -1])
@assert acct.stop_reason === :quiescent
@assert acct.verified
@assert acct.residual_variables == 0
@assert acct.conversion_import.stop_reason === :applied
@assert acct.discovery.stop_reason === :quiescent
@assert acct.verification.stop_reason === :verified
@assert acct.export_phase.stop_reason === :certified
@assert acct.reconstruction.stop_reason === :reconstructed
@assert acct.rollback_replay.stop_reason === :applied

