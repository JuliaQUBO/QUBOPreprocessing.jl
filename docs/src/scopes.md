# Repeated branch workloads

Temporary caller decisions restrict the optimization problem. A conditional
deduction is strong within that branch; it does not certify an unconditional
original-global reduction. The workspace distinguishes caller pins, root-global
deductions and later scoped deductions throughout propagation, export and rollback.
There is no in-place overwrite of a proof premise. Restore/unfix first, then
impose a new value. Source coefficient or ToQUBO penalty edits require `reset!`.

```@example scopes
using QUBOPreprocessing
import QUBOTools as QT
ws = Workspace(QT.Model(Dict(:x=>1.0,:y=>0.0),Dict((:x,:y)=>-2.0));rules=:dominance)
@assert propagate!(ws).deductions == 0
root = checkpoint(ws)
assume!(ws,:y,0)
propagate!(ws;max_deductions=1)
@assert deductions(ws) == [:x=>0]
old = export_certificate(ws)
undo = rollback!(ws,root;report=true)
@assert undo.caller_unfixed == [2=>0]
@assert undo.deduction_unfixed == [1=>0]
@assert !verify_certificate(ws,old).valid
assume!(ws,:y,1)
propagate!(ws)
@assert deductions(ws) == [:x=>1]
deductions(ws)
```

`changes(ws, cp)` and `deductions(ws; since=cp)` return owned original-label/value
pairs for new caller pins and deductions respectively. Before rollback, these
describe the branch's added fixings. `rollback!(ws, cp; report=true)` additionally
returns a `RollbackReport` containing `caller_unfixed` and `deduction_unfixed`:
owned **original-index => removed-value** vectors in reverse application order.
Indices are independent of compact residual order and do not imply that integer
labels have the same values. The report retains generation/restored checkpoint.
Without the keyword, rollback still returns the workspace.

Capture visits only removed fixing records; it does not scan the source graph,
all n positions or queue-only history. Rollback itself restores all undone queue,
field, bound, constant and provenance records and costs that actual undo work.
No-change capture allocates only constant-size empty vectors. A small caller
change can trigger a large genuine cascade; its trail/undo cost is unavoidable.
Historical reports/exports remain owned evidence about their captured source;
they do not authorize applying an old proof to a changed branch. The verifier
rejects stale tip/generation certificates. Changing the source with the same
dimension still creates a fresh generation.

`unfix!` removes caller pins only. Removing the most recent caller rolls back
locally, including its later deductions. Arbitrary removal rebuilds exact state
and replays retained caller pins in order, discarding all deductions, including
independent root deductions. Repropagation can recover those facts. This
conservative O(n+m+replay adjacency work) path invalidates all prior checkpoints
and reports replay visits through `UpdateReport.edge_visits`; initialization is
separate. No stale inferred value becomes an independent caller premise.
Matching already inferred values are no-ops without promotion; impose a truly
independent premise only after restoring a state where that variable is free.
Conflicts are rejected before mutation. Work/deadline refusals of caller updates
leave state unchanged; interrupted propagation retains a sound resumable prefix.

The executable `examples/branch_search.jl` is a guarded exact depth-first search
using one workspace. It repeatedly imposes caller decisions, resumes propagation
with one-deduction budgets, captures removed fixings and backtracks. The example
caps the model at eight binary variables before sizing its search tree, bounds
nodes and propagation calls, verifies branch proof chains, handles all-fixed
leaves locally and audits original energies exactly. Its `index_map` decisions
explicitly scan n; leaf export/proof verification costs remain explicit.
This illustrates a caller algorithm rather than a production solver adapter.

The bounded trace suite measures actual executed pin, conflict, repeat,
propagate, rollback and non-LIFO replay coverage for each seed/domain/sense/scale.
After every operation, independent original-scalar enumeration checks all scoped
optima and residual energies, and a fresh workspace supplies a second complete
propagation comparison. No timing threshold is used. Sparse warmed capture cycles
compare allocation/work shape at n=10 and n=2000. Independent workspaces retain
their own state; no parallel scheduler is part of this contract.

This supported boundary covers fixed-value conditioning only. Future relations,
domain maps and elimination records need their own proof-aware translations or
rollback/replay when callers refer to removed variables; see issues #14–#17.
