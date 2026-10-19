# Bounded strict dominance

After constructing a workspace, dominance is the inference step that may reduce
the solver input. This page explains which signs justify a fixing and how to
resume a bounded pass. See the [solve walkthrough](guide.md#guide-solve)
for what to do with its residual and report.

Select `Workspace(model; rules=:dominance)` and call `propagate!` explicitly,
or use `preprocess(model; rules=:dominance, limits...)`. Identity remains the
default. Neither path dispatches a solver or implicitly materializes a residual.
Only strong unary dominance is enabled: every reported value holds in **all**
optima within the current caller scope. Pair relations, weak ties, elimination,
roof duality and heuristic choices are separate methods.

For minimization of the normalized objective, a binary derivative has bounds
`aᵢ + Σ min(0,bᵢⱼ)` and `aᵢ + Σ max(0,bᵢⱼ)` over free neighbors.
A strictly positive lower bound fixes 0; a strictly negative upper bound fixes 1.
For spins the field bounds are `aᵢ ± Σ abs(bᵢⱼ)`, fixing -1/+1 respectively.
The boundary field includes fixed neighbors. Maximization and negative scale
reverse the sign; positive scale magnitude does not alter optima. Zero scale
and equality yield no fixing. The binary/spin rules are equivalent under
`x=(s+1)/2`, rather than independent strengthening methods.

```@example dominance
using QUBOPreprocessing
import QUBOTools as QT
ws = Workspace(QT.Model(Dict(:x=>3.0,:y=>1.0,:isolate=>0.0),
                        Dict((:x,:y)=>-2.0)); rules=:dominance)
root = checkpoint(ws)
first = propagate!(ws; max_deductions=1)
@assert first.stop_reason == :deduction_limit
@assert verify_certificate(ws,export_certificate(ws)).valid
last = propagate!(ws)
@assert last.stop_reason == :quiescent
@assert isempty(assumptions(ws))
@assert length(deductions(ws)) == 2
result = materialize(ws)
@assert verify_certificate(ws,result.certificate.proof).valid
@assert QT.variables(export_model(result)) == [:isolate]
deductions(ws), last
```

## Incremental work and interruption

Construction prepares exact `Rational{BigInt}` fields and derivative-bound
caches once, plus an initial original-index-order queue. Unlike the standalone
`prove_dominance` interval/fallback helper, propagation reads its exact caches
and records `method=:exact`. Installing one deduction updates only its free
neighbors and queues each dirty neighbor once. No QUBOTools constructor, full
conversion, source copy or proof export occurs per deduction. Bit complexity
is additional to structural counts. After the initial scan, an unchanged call
performs no candidate or adjacency work. Genuine cascades may touch the graph.

Per-call limits are nonnegative machine-sized integers:

| Limit | Charged work |
| :-- | :-- |
| `max_work` | candidate checks plus deduction-update adjacency visits |
| `max_deductions` | committed deductions |
| `max_exact_work` | cached sign checks and conservative reservations of one constant plus three exact values per incident edge for an attempted update |
| `deadline_ns` | absolute `UInt64` monotonic `time_ns()` deadline |

A complete update is reserved before commitment. Fixed-neighbor skips can make
exact reservations conservative. If a deduction cannot fit, its queue entry
remains pending; its examined candidate/sign check is charged again on resume.
Deadline checks surround preparation and run per incident edge; the short
commit/queue-journal boundary finishes without interruption. These are
algorithmic limits, not hard real-time or asynchronous process-cancellation guarantees.

Reports use `:work_limit`, `:deduction_limit`, `:verification_limit`, `:deadline`
or `:quiescent`. Every stop retains a sound committed prefix. A later call
continues the pending queue. `pending` includes queued entries already fixed
by a cascade until they are consumed. Report totals count executed/reserved
propagation work even if the model is later rolled back. Initialization, caller
updates, replay, explicit export, verifier and solver costs are separate.

Queue consumption and fixings both have undo records. Rollback restores exact
fields, bounds, constant, pending cursor/flags, caller and deduction provenance.
`changes(ws, cp)` returns caller pins; `deductions(ws; since=cp)` returns only
inferences. Both inspect fixing records, skipping queue-only history. Checkpoints
are constant-size, and stale branches/resets are rejected. Arbitrary `unfix!`
conservatively discards deductions and replays only retained explicit callers;
it is a documented full rebuild. Resume propagation explicitly afterward.

## Proof and consumer boundaries

`export_certificate(ws)` explicitly copies the original source and ordered proof
chain, or returns `nothing` in constant-size work when there are no deductions.
Each step records its caller-prefix length: adding a later assumption does not
rewrite an earlier bound or constant. The independent verifier substitutes the
birth scope and validated predecessor chain in the original polynomial. A
root-global step has caller-prefix length zero. Captured certificates require
the exact current trail tip; historical branch evidence is rejected after rollback,
replay or reset even if the same assignments are reapplied.

`materialize` captures an owned residual, label map, complete fixed assignment
and proof chain. Root deductions have `certificate.scope == :original`; explicit
caller pins produce `:assumptions`. Caller pins do not prove the branch contains
a global optimum of the original problem. Default Float64 export still requires
exactly representable residual coefficients/constants; otherwise request
`coefficient_type=Rational{BigInt}` and a compatible consumer. Certified inference
does not authorize rounding. Reconstruction validates every free residual value
and restores all fixed values in original order. With no free variables, the
zero-dimensional residual is handled locally with an empty child state.
When free variables remain, propagation does not prove an arbitrary state optimal.

## Bounded evidence

The exhaustive tests independently enumerate original/scoped optima on guarded
tiny fixtures, compare every residual energy, verify all deductions, and check
binary/spin equivalence. Sparse local-change tests compare n=10 and n=2000
work/allocation shape without wall-time thresholds. Run
`examples/dominance.jl` for the resumable cascade and
`scripts/dominance_pilot.jl` for a tiny paired on/off CPU pilot. The pilot charges
workspace construction, propagation, proof capture/verification, model export,
the same bounded exhaustive child, reconstruction and audit. It retains every
paired repetition and separates phases. Reduced variables/edges and total
costs are reported together, including no-reduction controls. This pilot is
not the accepted operating envelope or an ecosystem adoption decision; those
remain with QUBOBenchmarks issue #30.

The retained source artifact `docs/evidence/dominance-pilot.md` records the
producing revision and all paired raw rows. In that tiny warm run, the all-fixed
case reduced total time, while the cascade and both no-reduction controls were
slower with preprocessing. Variable reduction alone did not predict payoff.
