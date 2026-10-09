# Identity foundation

This candidate package implements the repository and identity foundation of the
[accepted certified preprocessing design](https://github.com/JuliaQUBO/QUBO.jl/blob/c0ab77d34e2281cfd6bd06e6c9c2f5ce13994670/docs/src/design.md#certified-preprocessing).
The implemented rule is **`rules=:identity`**, which performs no inference.
`rules=:dominance` raises `ArgumentError`. Candidate version 0.1.0 is not a
release, and the planned dominance/incremental API is not available yet.

## Install and run from source

Until General registration actually occurs, use an explicitly selected source
revision, preferably the reviewed commit SHA:

```julia
using Pkg
Pkg.add(url="https://github.com/JuliaQUBO/QUBOPreprocessing.jl",
        rev="feat/identity-bootstrap")
Pkg.add("QUBOTools") # Declare the model dependency in the consumer project.
using QUBOPreprocessing
```

The branch can change during review. Use its commit SHA for reproducible use.
Do not use an unqualified package-name installation before registration.
Build this manual locally; there is no advertised hosted manual.

```@example identity
using QUBOPreprocessing
import QUBOTools as QT
model = QT.Model(Dict(:x=>1.5, :y=>-2.0, :isolate=>0.0),
                 Dict((:x,:y)=>0.25); scale=-2.0, offset=0.5,
                 sense=:max, domain=:bool)
ws, report = preprocess(model; rules=:identity)
result = materialize(ws)
solver_model = export_model(result)
state = [label === :y ? 1 : 0 for label in original_variables(result)]
restored = reconstruct(result, state)
@assert restored.state == state
@assert restored.energy.value == 3.0
@assert result.certificate.reduction_chain == ()
(original_variables(result), restored.state, restored.energy)
```

The standalone `examples/identity.jl` uses the same public path.

## Representation and ownership

Accepted inputs are concrete `QUBOTools.Model` objects with finite Float64
objective coefficients, scale and offset, integer model state type, and the
built-in sparse, dense or dictionary forms. The quadratic form must already be
in strict upper triangular normal form (zero diagonal). Unsupported wrappers,
coefficient types and nonfinite data are rejected without conversion. Binary
and spin domains, both senses, arbitrary ordered labels, empty models,
isolates, constants, and finite positive/negative/nonunit/zero scales are supported.

The mathematical source is the exact binary value of each stored Float64:

```math
E(x)=\alpha\left(\beta+\sum_i L_i x_i+\sum_{i<j}Q_{ij}x_i x_j\right).
```

Identity export preserves coefficients, signed stored zeros, label/index order,
scale, offset, sense, domain and every variable. No arithmetic, normalization,
zero dropping or scale folding occurs. Exact representation identity proves
that source and export represent the same problem, with an empty reduction
chain and original scope. **It does not prove that a supplied state is optimal.**

A workspace privately freezes scalar storage and copies labels. Labels must
have stable equality/hash semantics and an owned `deepcopy` that preserves
those semantics. Identity-based mutable labels whose copies compare unequal
are rejected with `ArgumentError`, including transactionally by `reset!`.
Mutable labels with copy-stable value equality/hash are supported; their mutable
payloads must be correctly copied by `deepcopy`. Do not mutate a label identity
while it is retained. Model metadata, warm starts and attached solutions are
outside the snapshot and are omitted from exported solver models. One workspace is used
serially; independent workspaces share no mutable state.

`materialize` captures an owned historical export. `export_model(result)` returns
a fresh mutable QUBOTools model on each call. `original_variables` and `index_map`
return fresh owned data. Editing returned models/maps/states does not change the
workspace or export. Reconstruction refers to the captured objective, so a caller
who edits a solver model must independently verify that model still matches the
export before treating solver results as evidence about the original problem.
Private underscored fields are implementation details, not mutation APIs.

`generation(ws)` identifies both workspace and accepted source generation.
`reset!(ws, model)` validates before committing a fresh snapshot; invalid input
leaves the previous generation valid. Success creates a new generation even
with unchanged dimension or identical source data. Historical exports and their
reconstructed states retain their original generation. Consumers must compare
identities explicitly before treating them as evidence for a current workspace.

## Reconstruction and numerical evaluation

`reconstruct(result, y)` accepts a complete one-based vector in residual/original
index order. Each entry must be a finite real exactly in `{0,1}` or `{-1,1}`
according to the original domain. It rejects missing, malformed, partial and
out-of-domain states and returns an owned `Vector{Int}`.

`restored.energy` is an ordinary QUBOTools Float64 evaluation with `method=:float64`
and a `finite` flag. Floating rounding, cancellation, overflow and summation
order apply; exact stored-value preservation does not imply exact numerical
energy evaluation. Nonfinite numerical results are reported without upgrading
them to proof. Tests use independent exact binary-value rational references on
guarded tiny fixtures; production does not implement exact proof arithmetic.

## Implemented costs and deferred API

Snapshotting, materialization and model retrieval copy stored objective/label
data explicitly. Sparse structural work/storage is O(n+m); dense storage copying
can cost O(n²). Reconstruction validates all n entries, constructs evaluation
storage and evaluates the original objective. Dictionary iteration and numerical
summation order can differ between copies. No benchmark performance envelope,
work/deadline enforcement or hard timing guarantee is claimed by this slice.
Generation/report inspection is constant-size. `preprocess` constructs a workspace
and a no-inference report; it does not materialize a model implicitly.

| Work | Owning issue / delivered state |
| :-- | :-- |
| Accepted architecture/API/acceptance contract | [QUBO PR #94](https://github.com/JuliaQUBO/QUBO.jl/pull/94), already merged |
| Repository and identity foundation | [#1](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/1), this slice |
| Adjacency, dirty queue, checkpoints, reversible conditioning and bounded work | [#2](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/2), deferred |
| Enclosures, bounded dyadic proofs, verifier and non-identity safe transport | [#3](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/3), deferred |
| Strict dominance | [#4](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/4), deferred |
| Assumptions, conditional provenance, rollback/unfix/replay and resumption | [#5](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/5), deferred |
| Optional QUBODrivers/MOI/direct/ToQUBO consumer | [#6](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/6), deferred |
| Performance envelope | [QUBOBenchmarks #30](https://github.com/JuliaQUBO/QUBOBenchmarks.jl/issues/30), deferred |
| Decomposition integration | [QUBODecomposition #16](https://github.com/JuliaQUBO/QUBODecomposition.jl/issues/16), deferred |
| Full manual, release/registration and ecosystem adoption | [#7](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/7), deferred |

`checkpoint`, `assume!`, `propagate!`, `changes`, `rollback!` and `unfix!` are
neither exported nor implemented. `materialize` accepts Float64 only and does
not accept future `limits` arguments. No placeholder consumer or inference API
claims these later features work.
