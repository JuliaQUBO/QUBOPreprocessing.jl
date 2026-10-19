# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    SolverResult

Owned direct-consumer evidence. `samples` contain complete original-order
reconstructions and `reads` their multiplicities. `optimal` applies only to the
original scope; `scope_optimal` can instead certify the retained caller scope.
`stop_reason`, public `child_status`, generation, captured `exported` residual,
and `metadata` retain work/timing/proof/capacity information. `workspace` is the
live workspace used for the call; captured exports/samples remain historical
when that workspace changes. A timeout can retain validated samples without
an optimality claim. No missing free values are invented.
"""
struct SolverResult
    workspace::Union{Nothing,Workspace}
    generation::Union{Nothing,Generation}
    scope::Symbol
    stop_reason::Symbol
    samples::Vector{Reconstruction}
    reads::Vector{Int}
    optimal::Bool
    scope_optimal::Bool
    child_status::Symbol
    exported::Union{Nothing,ExportResult,ConditionedExport}
    metadata::NamedTuple
end
generation(r::SolverResult) = r.generation

"""
    sample_preprocessed(model_or_workspace, fresh_child_factory; kwargs...)

Optional direct consumer, available after loading QUBODrivers 0.6.5 or later.
Use an existing workspace or construct one with `rules=:dominance` (the model
default) / `:identity`. Explicitly capture a Float64-safe residual, verify its
proof chain, invoke a fresh Float64 QUBODrivers child, validate complete states,
and recompute original energies with one shared source evaluator per call.
All-fixed cases run locally. Return a [`SolverResult`](@ref).

Supported keywords include `max_work`, `max_deductions`, `max_exact_work`,
absolute `deadline_ns`, `max_child_variables=16`, `max_results=1024` and
`child_work_bound=nothing`. Work is one shared allowance for charged adapter
storage/update/verification/reconstruction units and a reserved child bound.
The built-in ExactSampler has a conservative bound; another finite-work child
requires a supplied `(child, residual, remaining_work, deadline_ns) -> nonnegative Int` bound that the child
honors, otherwise dispatch abstains. Deadline checks surround noninterruptible
copy boundaries; remaining seconds are passed through MOI.TimeLimitSec when
supported. A child is responsible for honoring its declared bounds/deadline.
There is no hard real-time/process-preemption guarantee.

Unsafe Float64 transport abstains before child dispatch. Exact residuals remain
available through the core materialization API. Valid heuristic/interrupted child
states do not gain optimality from certified preprocessing. The child's public
MOI.OPTIMAL is retained only for a verified complete chain, validated result1,
finite original energy and unexpired allowance. Caller scopes remain qualified.
Sampling distributions and physical-read semantics are not preserved.
"""
function sample_preprocessed end

"""
    QUBOPreprocessing.Optimizer(fresh_child_factory; kwargs...)

Optional QUBODrivers/MOI optimizer factory, available after loading QUBODrivers.
Use `() -> QUBOPreprocessing.Optimizer(child_factory; ...)` with MOI/JuMP/ToQUBO.
The factory is accessed by its qualified name to avoid solver namespace collisions. It shares the
[`sample_preprocessed`](@ref) implementation, snapshots the accepted compiled
QUBO on each solve, restores every logical QUBO variable before source decoding,
and reports the public child's proof status conservatively. A compiled optimum
does not establish source-model feasibility. Core workspace use has no mandatory
QUBODrivers, JuMP, ToQUBO or concrete solver dependency.
"""
function Optimizer end
