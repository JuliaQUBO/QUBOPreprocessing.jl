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

export DominanceStep, DominanceCertificate, DominanceAttempt, VerificationResult,
       prove_dominance, verify_certificate, transport_certificate

export DomainGaugeMap, domain_map, map_value, lift_value, map_state, lift_state,
       degree, effective_field, incident_couplings, conditioned_constant

export propagate!, PropagationReport, deductions, export_certificate
export sample_preprocessed, SolverResult

include("trail.jl")
include("identity.jl")
include("domain.jl")
include("workspace.jl")
include("certificates.jl")
include("propagation.jl")
include("consumer.jl")
end
