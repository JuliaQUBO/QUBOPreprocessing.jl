# Optional direct and ToQUBO consumers

The core workspace loads without QUBODrivers, MathOptInterface, JuMP, ToQUBO or a
concrete solver. Load QUBODrivers ≥0.6.5 to activate the Julia extension:

```julia
using QUBOPreprocessing, QUBODrivers
import QUBOTools as QT
model = QT.Model(Dict(:x=>3.0,:y=>1.0,:tie=>0.0),Dict((:x,:y)=>-2.0))
result = sample_preprocessed(model, QUBODrivers.ExactSampler.Optimizer;
                             max_child_variables=8)
best = first(result.samples) # complete original-order state and original energy
```

`sample_preprocessed` accepts a finite Float64 QUBOTools model or an existing
workspace, plus a zero-argument factory returning a **fresh empty Float64
QUBODrivers sampler**. Model input constructs a new dominance workspace; choose
`rules=:identity` to disable inference. Existing workspaces retain their selected
rule and current caller scope. Each call resumes propagation, explicitly captures
and verifies the residual chain, invokes the child only if free variables remain,
validates complete child states and recomputes original energies. One original
source evaluator is built per call and reused for all samples. No missing free
value is supplied from a previous solve or guessed optimum. Original labels,+sense, domain, scale, offset and fixed-value proof records remain in the result.
The returned workspace is live; exports, samples and report metadata retain their
captured identities. Use its generation and verifier before reusing historical
proofs after branch/reset operations.

The adapter uses **Float64 transport only**. If any conditioned coefficient or
constant cannot be represented exactly, `:unsafe_export` returns before child
dispatch. It neither rounds nor silently switches the child precision. Consumers
that support `Rational{BigInt}` can separately use the core exact materialization
path. Relabeling the residual to MOI variable indices copies its checked form
without a normalizing floating constructor. The guarantee begins at the accepted
QUBOTools objective; a compiler/model parser's own numerical transformations and
a child's numerical solver claims retain their respective contracts.

## Validity, scope and status

`SolverResult.samples` are complete original-domain reconstructions; their
Float64 energies include the original scale and offset, with a finite flag.
Malformed/partial/out-of-domain child rows and nonfinite original energies are
rejected. `reads` retains available multiplicities. Preprocessing does not
preserve a sampling distribution, diversity or physical-read interpretation.

Certified preprocessing does not upgrade a heuristic child's status. A public
`MOI.OPTIMAL` from the child can survive only with a verified exact reduction and
export, valid result 1, finite original energy, completed reconstruction and an
unexpired allowance. The adapter trusts the supplied solver's public certificate;
it does not independently prove an arbitrary solver optimal. QUBODrivers 0.6.5's
generic ExactSampler public status is `LOCALLY_SOLVED`, so the direct result
remains `:feasible` despite its exhaustive implementation or metadata name.
Tests use a separately guarded exact child whose public certificate is explicitly
backed by exact enumeration. If all variables are fixed, the adapter handles the
zero-dimensional residual locally and needs no child certificate or dispatch.

`optimal` applies to the accepted original QUBO only. Under external caller
assumptions, `scope_optimal` can be true while `optimal` remains false; the reason
is `:scope_optimal` and the scope is `:assumptions`. This does not establish that
the branch contains an original global optimum. Stops/failures retain only
samples already validated within the remaining allowance. `:child_timeout` or
`:child_failure` can retain a complete incumbent, without an optimality claim.
If a child returns too late for reconstruction, no free state is invented.
Only public result 1 supports its usual optimality claim; rejection of that row
does not promote another row to optimal.

## Shared limits and costs

One `max_work` allowance spans the adapter's source/storage passes, propagation
candidate/adjacency work, independent verifier term visits, child reservation and
per-result reconstruction/original-energy work. Source construction and the
export/evaluator boundary each conservatively reserve eight storage units per
source position/entry (plus proof records for export). The budget is structural;
integer bit complexity, label-copy/hash cost and allocation details are additional.
The plain workspace's hot queries keep their separate documented costs.

The known built-in ExactSampler reserves conversion/storage plus a bound for
all `2^n` scalar evaluations; it is refused above 20 free variables **before**
exponentiation or dispatch. `max_child_variables=16` is a separately configurable
consumer capacity guard. Another child with a finite work allowance requires
`child_work_bound(child, residual, remaining_work, deadline_ns)` to configure it
and return a nonnegative conservative reservation it honors. Without that
contract, finite-work dispatch returns `:unsupported_work_limit`. An unbounded
work allowance does not claim an unknown child's internal work was measured.
The same reservation is charged even when the child fails. `max_results=1024`
bounds the number of rows reconstructed; maximum supported setting is one million.

`max_deductions` and `max_exact_work` constrain propagation. A stopped sound
prefix can still be sent to the child if the shared allowance remains. The
unfinished queue stays resumable. Export and independent verification are
explicit full-source boundaries; a small inference budget need not leave enough
work to build or verify a solver model. `metadata` records used/remaining work,
child reservation/dispatch/capacity, rejected rows, propagation report, stopping
phase and phase/total seconds. Complete timings include source preparation,
proof, model capture, child solving and reconstruction; source compilation
before the accepted QUBO and user analysis afterward are outside this boundary.

`deadline_ns` is an absolute UInt64 monotonic deadline. The remaining seconds are
passed to the public `MOI.TimeLimitSec` setter immediately before child dispatch;
unsupported setters abstain. QUBODrivers0.6.5 provides that setter even where its
generic supports query is conservative. A child remains responsible for honoring
it. Deadline checks surround noninterruptible copy boundaries and each result;
there is no hard real-time or process-preemption guarantee. A completed boundary
that crosses the deadline cannot retain an optimality claim. Work/deadline refusals
report the valid prefix/evidence available at that point.

## MOI and ToQUBO

Use `() -> QUBOPreprocessing.Optimizer(child_factory; options...)` as a supplied
MOI/JuMP optimizer, or inside `ToQUBO.Optimizer`. It uses QUBODrivers' public
model-copy/sampler interfaces, snapshots the accepted compiled QUBO afresh each
solve, and returns all its logical variables before ToQUBO decodes source values.
MOI fixed-variable/parser algebra belongs to the existing QUBODrivers input
boundary; the new workspace certifies its accepted stored objective. A new
compilation/penalty objective creates a new generation, even with the same shape.
Inspect the last owned `SolverResult` through
`MOI.RawOptimizerAttribute("preprocessing_result")` on the raw adapter. Explicit
post-sample transformations lose any inherited optimality claim.

The example `examples/consumer.jl` solves both a plain QUBO and a ToQUBO source
with two binary variables and a bounded integer represented by two bits. All
four compiled bits are restored before decoding; source objective and feasibility
are independently checked. The integration test also deliberately weakens a
penalty: the new compiled QUBO has a certified optimum but violates the source
constraint. That diagnostic is an explicitly insufficient configuration, not a
default compiler failure. A compiled energy may include such a penalty and must
not replace independent source objective/feasibility evaluation.

Run the real optional profile separately:

```sh
julia --project=test/integration -e 'using Pkg; Pkg.develop(path=pwd()); Pkg.instantiate()'
julia --project=test/integration test/integration/runtests.jl
julia --project=test/integration examples/consumer.jl
```

It requires QUBODrivers, MOI, JuMP and ToQUBO and must fail if any declared import
or initialization fails. It runs public QUBODrivers conformance plus exact/scoped,
heuristic, malformed, interrupted, capacity/export and ToQUBO controls. The core
suite/profile remains independent of these optional packages. No decomposition
package, foreign runtime or production timing benefit is required or claimed.
