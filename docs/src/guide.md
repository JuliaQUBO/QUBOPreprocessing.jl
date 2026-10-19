# Use preprocessing in a solver workflow

Preprocessing sits between your model and your solver. It can remove variables
whose values are certified, then restore those variables after the solver returns
a state for the smaller problem. If your algorithm repeatedly changes assumptions,
you can keep the same workspace and undo a branch before trying the next one.

This guide starts with a complete core-only solve. It then reuses a workspace
across two branches and finishes with the optional solver adapters. The
[model reference](representation.md) collects the input, ownership and numerical
contracts used throughout.

## [Preprocess, solve and reconstruct](@id guide-solve)

Consider a binary minimization problem with objective `3bias - x*y`. The positive
coefficient forces `bias=0` in every optimum. Neither `x` nor `y` can be fixed by
strict dominance at the root: ties remain until the other variable is known.

```@example guide_solve
using QUBOPreprocessing
import QUBOTools as QT

model = QT.Model(Dict(:bias => 3.0, :x => 0.0, :y => 0.0),
                 Dict((:x, :y) => -1.0))
ws, report = preprocess(model; rules=:dominance)
@assert report.stop_reason == :quiescent
reduced = materialize(ws)
residual = export_model(reduced)
@assert QT.variables(residual) == [:x, :y]
@assert verify_certificate(ws, reduced.certificate.proof).valid
QT.variables(residual)
```

There are three different objects here. `ws` holds reusable working state;
`reduced` captures an owned snapshot of the reduction and its maps; `residual`
is the QUBOTools model to give your solver. Creating and exporting the snapshot
are explicit full-model operations, so you choose when to pay for them.

For this two-variable residual, we can solve the whole problem by evaluating its
four states. This small enumeration is here to make the example self-contained;
use your solver for a larger residual. Its returned vector must contain every
free variable in the order shown by `QT.variables(residual)`.

```@example guide_solve
candidates = [[0, 0], [0, 1], [1, 0], [1, 1]]
residual_state = argmin(state -> QT.value(residual, state), candidates)
restored = reconstruct(reduced, residual_state)
original_state = Dict(zip(original_variables(reduced), restored.state))
@assert original_state == Dict(:bias => 0, :x => 1, :y => 1)
@assert restored.energy.finite && restored.energy.value == -1.0
(original_state, restored.energy.value)
```

`reconstruct` uses the captured maps to restore `bias`, validates the complete
state, and evaluates the original objective. It does not itself decide whether
the residual state is optimal. Here the four-state enumeration supplies that
step; with another solver, keep that solver's guarantee. Without caller
assumptions, a global residual optimum lifts to an original global optimum.

Select `rules=:dominance` when you want deductions. `Workspace` and `preprocess`
default to `rules=:identity`, which preserves the model without inference and
is useful for an off/on comparison.

Sometimes every variable is removed. There is then no free state for a solver
to return; reconstruct with an empty vector:

```@example guide_solve
fixed_ws, _ = preprocess(QT.Model(Dict(:z => 2.0),
    Dict{Tuple{Symbol,Symbol},Float64}()); rules=:dominance)
fixed_result = materialize(fixed_ws)
fixed_state = reconstruct(fixed_result, Int[])
@assert fixed_state.state == [0]
fixed_state.energy.value
```

## [Explore assumptions and undo a branch](@id guide-branches)

A branch decision has a different meaning from a deduction. For `x - 2x*y`,
assuming `y=0` makes `x=0` optimal in that branch. The original problem instead
has its minimum at `x=y=1`. The workspace keeps your assumptions and its
conditional deductions separate so undoing the branch also removes the facts
that depended on it.

```@example guide_branch
using QUBOPreprocessing
import QUBOTools as QT

model = QT.Model(Dict(:x => 1.0, :y => 0.0), Dict((:x, :y) => -2.0))
ws = Workspace(model; rules=:dominance)
@assert propagate!(ws).deductions == 0
root = checkpoint(ws)
update = assume!(ws, :y, 0; max_work=10)
@assert update.stop_reason == :applied
report = propagate!(ws; max_work=100)
@assert report.stop_reason == :quiescent
@assert changes(ws, root) == [:y => 0]
@assert deductions(ws; since=root) == [:x => 0]
(changes(ws, root), deductions(ws; since=root))
```

Use original labels with `assume!`; a label is not a residual index. The two
queries above return only fixing records added since the checkpoint, without
building a residual. That is enough when a surrounding algorithm only needs
to learn which values changed.

To solve or inspect this branch, explicitly capture its residual. Both variables
are now fixed, so reconstruction needs no child state. The scope records why
this result cannot be treated as a root-global deduction.

```@example guide_branch
branch = materialize(ws)
branch_state = reconstruct(branch, Int[])
@assert branch.certificate.scope == :assumptions
@assert branch_state.energy.value == 0.0
rollback!(ws, root)
@assert isempty(assumptions(ws)) && isempty(deductions(ws))
branch_state.energy.value
```

The snapshot remains a historical result after rollback; it does not describe
the current workspace. Captured proof certificates require the matching current
trail and generation when verified against a workspace. See
[certificate scope and verification](certificates.md) before reusing proof evidence.

A search can repeat this pattern. Keep rollback in a `finally` block so an error
in export or solver handling does not leave the next branch conditioned by the
previous one. This tiny example covers both values of `y`; a larger search must
supply its own branch coverage, incumbent and termination policy.

```@example guide_branch
branch_energies = Dict{Int,Float64}()
for y_value in (0, 1)
    cp = checkpoint(ws)
    try
        update = assume!(ws, :y, y_value; max_work=10)
        @assert update.stop_reason == :applied
        report = propagate!(ws; max_work=100)
        @assert report.stop_reason == :quiescent
        snapshot = materialize(ws)
        branch_energies[y_value] = reconstruct(snapshot, Int[]).energy.value
    finally
        rollback!(ws, cp)
    end
end
@assert branch_energies == Dict(0 => 0.0, 1 => -1.0)
@assert isempty(assumptions(ws)) && isempty(deductions(ws))
branch_energies
```

The limits in this example fit its tiny graph. In a real loop, inspect each
report: a refused `assume!` leaves the workspace unchanged, whereas interrupted
`propagate!` retains a sound prefix that you can resume with another call.
Each call has its own limits; your search is responsible for its total budget.
[Branch workloads](scopes.md) explains the complete pattern and guarded search
example. [Bounded dominance](dominance.md) describes stop reasons and charged work.

Nested rollback undoes the work since a checkpoint. Removing an older assumption
with `unfix!` instead rebuilds and replays retained assumptions, discarding old
deductions and invalidating old checkpoints. Budget that full operation separately;
it is not a local update. Use `reset!` when model coefficients or compiler penalties
change. The [workspace reference](workspace.md) explains both paths.

## [Let the direct adapter handle the solver boundary](@id guide-direct)

If your solver follows QUBODrivers, `sample_preprocessed` performs propagation,
export, proof verification, child dispatch and reconstruction for you. This is
convenient for a complete solve, but it deliberately pays those full boundaries
on each call. Prefer the workspace pattern above when an inner loop only needs
changed fixings. Consult the [measured costs](performance.md) before choosing a default.

Install QUBODrivers with `Pkg.add("QUBODrivers")`. Loading it activates the optional
extension; the core examples above do not need a solver package.

```julia
using QUBOPreprocessing
import QUBODrivers as QD
import QUBOTools as QT

model = QT.Model(Dict(:bias => 3.0, :x => 0.0, :y => 0.0),
                 Dict((:x, :y) => -1.0))
solved = sample_preprocessed(model, QD.ExactSampler.Optimizer;
                            rules=:dominance, max_child_variables=8)
if !isempty(solved.samples)
    best = first(solved.samples)
    @assert length(best.state) == 3
    @assert best.energy.value == -1.0
end
```

Pass a factory for a fresh empty child, not a sampler that already holds a model.
Model input defaults to dominance in this adapter; an existing workspace retains
its chosen rule and caller scope. Samples already contain original-order states
and original numerical energies.

Always inspect `stop_reason`, `optimal` and `scope_optimal` as well as the samples.
A stop or refusal may return no sample. A heuristic child stays heuristic; a
conditional optimum stays conditional. In particular, the supported QUBODrivers
0.6.5 floor reports its generic ExactSampler as locally solved; 0.6.6 corrects its
completed public status. The adapter follows that public status, not the solver's
name. It also does not preserve a sampling distribution. The
[consumer reference](consumers.md) explains shared work/deadline limits, capacity
and result caps, Float64 transport refusals and status handling.

## [Compose with JuMP and ToQUBO](@id guide-toqubo)

For a constrained JuMP model, place the qualified factory inside `ToQUBO.Optimizer`.
ToQUBO compiles the source model, preprocessing works on that compiled QUBO, and
reconstruction restores every compiled bit before ToQUBO decodes source values.
Install JuMP and ToQUBO with `Pkg.add(["JuMP", "ToQUBO"])` as well as QUBODrivers.

```julia
using QUBOPreprocessing, JuMP
import QUBODrivers as QD
import ToQUBO

source = Model(() -> ToQUBO.Optimizer(() -> QUBOPreprocessing.Optimizer(
    QD.ExactSampler.Optimizer; max_child_variables=8)))
@variable(source, x, Bin)
@variable(source, y, Bin)
@objective(source, Min, x - 2y)
@constraint(source, x >= 1)
optimize!(source)
@assert has_values(source)
chosen = round.(Int, value.((x, y)))
@assert chosen == (1, 1) && chosen[1] >= 1
@assert objective_value(source) == -1.0
```

Check feasibility and objective values in the original source model, as shown
here. A certified optimum of an inadequately penalized QUBO can still violate a
source constraint. The [consumer example](consumers.md#MOI-and-ToQUBO) and
`examples/consumer.jl` extend this to a bounded integer with several compiled bits.

## Choose the next reference

Use [models and ownership](representation.md) for accepted input forms, label maps
and numerical evaluation, [workspaces](workspace.md) for update/undo costs,
[dominance](dominance.md) for inference limits, and [certificates](certificates.md)
for independent verification. Full export, verification and reconstruction can
scan the source model even when a recent update touched only a small neighborhood.
Exact proof arithmetic does not make the reported Float64 energy an exact value.
