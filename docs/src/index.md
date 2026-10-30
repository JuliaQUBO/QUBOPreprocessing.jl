# Certified preprocessing

QUBOPreprocessing helps you reduce a QUBO before solving it and restore the
solver's answer to the original variables. Its strict-dominance rule fixes values
that hold in every optimum within the current scope. Reusable workspaces also
support algorithms that repeatedly impose assumptions, propagate deductions and
undo a branch.

Start with the [user guide](guide.md). It solves a small residual, reconstructs
its original state, reuses one workspace across branches, and then composes the
optional solver adapters. The reference pages explain the detailed guarantees
behind those steps.

## Install and run

Install QUBOPreprocessing and QUBOTools with Julia 1.10 or later:

```julia
using Pkg
Pkg.add(["QUBOPreprocessing", "QUBOTools"])
using QUBOPreprocessing
```

The guide's first example needs only these packages. Add QUBODrivers when you
want the [direct solver adapter](guide.md#guide-direct),
and JuMP/ToQUBO when working from a constrained source model.

## Representation and ownership

A workspace keeps its own snapshot of your model. An exported residual and its
reconstruction maps belong to that captured state, so you can inspect them after
undoing a branch. Assumptions restrict the problem: their deductions do not prove
that the selected branch contains an original global optimum.

Read [models, ownership and numerical evaluation](representation.md) for accepted
Float64 QUBOTools forms, label semantics, generations and identity-preserving export.
The original identity example is retained there as a reference demonstration.

## Reconstruction and numerical evaluation

A solver returns a complete state for the free residual variables. Reconstruction
restores fixed values in original order and evaluates the original objective.
It does not prove an arbitrary solver state optimal, and the returned energy
uses ordinary Float64 arithmetic even though reduction proofs use exact stored values.

The [complete solve walkthrough](guide.md#guide-solve) shows
this boundary; the [numerical reference](representation.md#Reconstruction-and-numerical-evaluation)
explains validation, rounding and finite-result reporting.

## Costs and composition

Use a fresh workspace for a one-shot reduction, or checkpoint/rollback when an
algorithm revisits the same model under different assumptions. Workspace and
`preprocess` calls default to `rules=:identity`; select `:dominance` to infer values.
Explicit materialization, proof verification and reconstruction have full-model
costs, and arbitrary non-LIFO unfixing rebuilds state. The
[operating envelope](performance.md) shows when reuse paid off and when preprocessing
added cost, and the [QUBOLib, QOBLIB & MINLPLib corpus benchmarks](benchmarks.md) report
size reductions, ground-state verification, and heuristic solution repairs across
6,292 benchmark instances.

For the individual contracts, read [conditioning](workspace.md),
[bounded dominance](dominance.md), [proof verification](certificates.md),
[branch workloads](scopes.md) and [optional consumers](consumers.md). For decomposition,
select a QUBODecomposition version documenting opt-in root preprocessing and follow
that package's installation and support policy.
