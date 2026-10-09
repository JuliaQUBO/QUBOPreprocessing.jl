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

include("identity.jl")
end
