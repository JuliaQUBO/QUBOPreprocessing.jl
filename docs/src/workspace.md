# Reversible conditioning

Use a workspace directly when a search or neighborhood method revisits the same
model under different assumptions. The [branch walkthrough](guide.md#guide-branches)
shows the complete loop; this reference explains what each update captures and
which costs you need to budget.

The workspace prepares signed sparse adjacency once and stores exact integer
numerators for boundary fields and constants on a shared dyadic grid in both binary and spin coordinates, plus per-variable
free interaction degrees (`degree(ws, label)`). Stored zero quadratic entries do
not inflate degrees, and linear fields (`effective_field(ws, label; map=...)`)
are tracked separately from remaining nonzero interactions
(`incident_couplings(ws, label; map=...)`). It retains the original domain, sense, scale
and label order; no full QUBO–Ising casts occur during updates. Dense input is
read once during initialization. `rules=:identity` has no inference;
[dominance](dominance.md) separately records inferred values.

```@example workspace
using QUBOPreprocessing
import QUBOTools as QT
ws = Workspace(QT.Model(Dict(:x=>1.0,:y=>-2.0),Dict((:x,:y)=>0.5)))
root = checkpoint(ws)
assume!(ws,:x,1; max_work=1)
changes(ws,root)
```

```@example workspace
result = materialize(ws)
residual = export_model(result)
restored = reconstruct(result,[1])
@assert restored.energy.value == -0.5
rollback!(ws,root)
@assert isempty(assumptions(ws))
restored.state
```

`assume!` takes an original **label**, including when labels are integers; it
does not take a compact residual index. Duplicate assignments are no-ops and
conflicts or invalid values fail before mutation. A duplicate of an inferred
value is also a no-op and does not create an independent caller premise; however,
if a subsequent `assume!` on a structurally reduced variable (or with an active
marginal weak step) rolls back that inferred deduction, the recorded matching
request is replayed in chronological order as an explicit caller assumption so the
requested conditioning is preserved (`rollback!` and `unfix!` discard such
recorded requests when their checkpoint or underlying deduction is removed).
Roll back before imposing an unconditional caller premise directly. Caller assumptions only
describe a restricted problem. A residual optimum lifts to an optimum within
that scope, which need not contain any original global optimum. The residual
export has `certificate.scope == :assumptions`; an empty reduction chain makes
no inference claim when only callers are present. With deductions, a separate
ordered strong proof is included. Source fields/scale/offset are exact binary values of the
accepted finite Float64 input (unless opt-in tolerance-based decimal rounding with
`integerize_scale=true` and `atol > 0` accepts a multiplier that changes any
effective objective coefficient or scaled offset, in which case `ws.perturbed == true`
and `ws.max_perturbation` records the largest absolute effective change).
Conditioning uses integer arithmetic with a common power-of-two denominator
to prevent cancellation drift. Public coefficient queries still return owned
`Rational{BigInt}` values in the same unscaled units. Algebraic preservation and
inference remain separate: inference additionally records independently verifiable proof evidence.

`checkpoint` is constant-size. Nested `rollback!` restores prior fields,
constant, fixed flags, pending dirty queue and assumption provenance exactly.
Discarded future checkpoints are rejected even if a later branch reaches the
same depth. Other workspaces and new `reset!` generations cannot reuse them.
Original model edits never alter a workspace; accept coefficient/penalty changes
through transactional `reset!`, which rebuilds state and changes generation.
Historical exports keep their original objective and scope.

`unfix!` on the most recent assumption uses local rollback. Removing an older
assumption conservatively builds fresh state and replays retained assumptions
in their application order. Replacement happens only on success and invalidates
all old checkpoints. It costs O(n+m + total retained adjacency visits), plus
exact arithmetic, and allocates a fresh state. It is not a local-cost promise.
Non-LIFO replay discards all deductions, retains only explicit caller pins,
and creates a fresh checkpoint epoch. The caller resumes propagation explicitly.
Local unfix removes the last caller and deductions after it; earlier proofs
remain valid. `unfix!` rejects inferred variables; roll back before their deduction.

## Work, allocation and interruption boundaries

Sparse initialization costs O(n+m) structural work/storage; raw dense input
costs O(n²) to read/copy. Each assumption visits its source degree (including
already fixed neighbors), updates only free neighbors, and appends compact undo
records and dirty queue entries. Each affected neighbor is queued at most once;
propagation consumes and trails the queue cursor. Rollback costs undone field/trail/queue
work, without a graph scan or floating subtraction. Mutable state is private to
each serial workspace. Exact integer bit complexity, allocations and label
hash/copy costs are additional to structural counts.

Each live integer numerator ``n`` denotes ``n/2^k`` for one workspace exponent
``k``. The actual field, adjacency, bound, dual-cache and numeric undo containers
use either `Int128` throughout or `BigInt` throughout. A checked construction
bound includes fields, edges and the offset. Boolean input reserves two extra
denominator bits so its spin fields and constants fit on that same grid.
The representation preserves every input coefficient and the snapshot scale with
`integerize_scale=false`, including represented binary64 values `0.1` and `0.3`.

Productive conditioning, contractions and eliminations prepare integer updates
before committing. Updates that exceed the fixed-width range promote the numeric
payload to `BigInt`; a fractional Spin elimination can increase ``k``. Such a
change rescales every live numerator and every numeric undo entry together.
It costs O(n+m+numeric undo history), in addition to the local update cost.
An ordinary rollback restores values, topology and scope and can retain the finer
grid or wider integer type. Checkpoint identity does not depend on this private
representation choice. Non-LIFO replay and reset rebuild from the source snapshot.

Proof records, domain-map cursor constants and public/export boundaries retain
exact rational physical units. Certificate replay uses a separate rational
polynomial implementation. Expensive proof search and local flow networks still
convert coefficients to rational values; persistent integer storage does not
claim that those algorithms are integer kernels or that their conversion costs
are absent. Cached strict-dominance, degree-three checks and relation screening
use the integer state directly; their floating intervals enclose the shared-grid
values without constructing a rational per edge. Full schedules retain their
existing families and order.

`max_work` is a nonnegative integer adjacency-visit budget for an update.
`deadline_ns` is an absolute UInt64 monotonic `time_ns()` deadline. An update
reserves all incident work, prepares changes separately, checks deadlines
during preparation, then commits at one algorithmic boundary. `:work_limit`
and `:deadline` return without mutation; allocation failures during preparation
likewise leave state unchanged. Rollback and the short commit phase complete
without deadline interruption. Asynchronous process interrupts and out-of-memory
termination are not transactional cancellation mechanisms. Non-LIFO unfix
charges replay adjacency visits to `max_work`; initialization still costs
O(n+m), and deadline checks surround rather than interrupt initialization.

`changes(ws, cp)` and `assumptions(ws)` allocate owned pairs proportional to
the fixing records in the requested range, without scanning the graph or
queue-only history. `deductions(ws; since=cp)` separately returns inferred pairs. No-change `changes`
and duplicate assumptions avoid graph traversal. `index_map` explicitly scans
n original positions, returning zero for fixed variables and compact positive
indices for free variables. The source's original label order is preserved.

`materialize` and `export_model` are explicit O(n+m) boundaries. With no
fixings, coordinate map or normalization, the original bit-preserving identity export is retained. Under
caller or inferred fixings, default Float64 export requires **every** transformed coefficient
and constant to be exactly representable, otherwise it raises `ArgumentError`.
Use `materialize(ws; coefficient_type=Rational{BigInt})` for the exact residual;
a solver must explicitly support that type. Alternatively, explicitly request
`materialize(ws; normalization=:integer)` to factor all mapped coefficients and
the constant into primitive integers and an adjusted common scale. It succeeds
only when every integer and the scale fit exactly as finite Float64; it adds no
perturbation. See [exact residuals and recorded solver rounding](@ref "Exact residuals and recorded solver rounding")
for examples and limits. Original
reconstruction still reports ordinary Float64 energy with a finite flag, not
an exact energy or proof that the supplied solution is optimal.

Future elimination/contraction passes can change graph topology. Their extension
point is the internal trail in `src/trail.jl`: they must add trailed topology
and reconstruction records before modifying adjacency. This slice deliberately
trails only conditioning and does not pretend to implement those later passes.

Run `examples/workspace.jl` and `scripts/workspace_costs.jl` for usage and bounded
warm measurements. Structural/allocation tests guard local work independently
of wall time. Measured end-to-end adoption and the accepted operating envelope
remain with QUBOBenchmarks issue #30; a reduced variable count is not evidence
that preprocessing pays off.

Use `rollback!(ws, cp; report=true)` for owned original-index/value removal
reports separated by caller/deduction provenance. See [branch workloads](scopes.md)
for its query costs, bounded branch search and replay stress tests.
