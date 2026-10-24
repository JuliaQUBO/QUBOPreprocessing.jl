# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
module QUBOPreprocessing

import QUBOTools as QT
using LinearAlgebra: UpperTriangular
using SparseArrays: SparseVector, SparseMatrixCSC
using UUIDs: UUID, uuid4

export Workspace, Generation, generation, reset!, materialize, ExportResult,
       export_model, original_variables, index_map, reconstruct, Reconstruction,
       EnergyEvaluation, preprocess, IdentityReport

export Checkpoint, checkpoint, assume!, rollback!, unfix!, changes, assumptions,
       UpdateReport, RollbackReport, ConditionedExport

export SubmodularComponent, MaxCutGraph,
       DominanceStep, RelationStep, EliminationStep, ProbingStep, RoofDualityStep, SubmodularCutStep, MaxCutStep,
       DominanceCertificate, ReductionCertificate,
       DominanceAttempt, RelationAttempt, EliminationAttempt, ProbingAttempt, RoofDualityAttempt, SubmodularCutAttempt, MaxCutAttempt,
       VerificationResult,
       recognize_submodular_component, recognize_submodular_components,
       maxcut_graph, maxcut_cut_weight, maxcut_energy, maxcut_to_spin, spin_to_maxcut,
       prove_dominance, prove_relation, prove_elimination, prove_probing, prove_roof_duality, prove_submodular_cut, prove_maxcut,
       verify_certificate, transport_certificate,
       step_guarantee, certificate_guarantee, persistency

export DomainGaugeMap, domain_map, map_value, lift_value, map_state, lift_state,
       degree, effective_field, incident_couplings, conditioned_constant

export propagate!, PropagationReport, ProbingReport, RoofDualityReport, SubmodularCutReport, MaxCutReport,
       deductions, reductions, export_certificate,
       apply_dominance!, apply_probing!, probe_variables!, apply_roof_duality!, apply_submodular_cut!, apply_maxcut!,
       contract_relation!, contract_relations!, relation_map,
       eliminate_variable!, eliminate_low_degree!, apply_weak_batch!,
       SchedulePassSummary, ScheduleReport, schedule_reductions!,
       PhaseAccounting, PipelineAccounting, audit_pipeline!
export sample_preprocessed, SolverResult

include("trail.jl")
include("identity.jl")
include("domain.jl")
include("workspace.jl")
include("flow.jl")
include("maxcut.jl")
include("certificates.jl")
include("propagation.jl")
include("consumer.jl")
end
