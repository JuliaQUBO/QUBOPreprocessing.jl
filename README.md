# QUBOPreprocessing.jl

Certified preprocessing for the [accepted certified preprocessing design](https://github.com/JuliaQUBO/QUBO.jl/pull/94).
**`rules=:identity` and `rules=:dominance` are implemented.** Explicit assumptions
and certified deductions use reusable sparse conditioning, exact bound caches,
checkpoints and rollback. An optional QUBODrivers/MOI consumer supports direct
solving and ToQUBO composition; decomposition integration remains separate.
Individual strong-dominance bounds, budgeted exact fallback and independent
certificate verification are available through `prove_dominance` and
`verify_certificate`; they do not mutate the workspace. `propagate!` commits strict dominance
cascades with resumable work/deduction/exact/deadline limits.
Candidate version 0.1.0 is unreleased and unregistered.

Install from a selected source revision, substituting its exact reviewed SHA:

```julia
using Pkg
Pkg.add(url="https://github.com/JuliaQUBO/QUBOPreprocessing.jl", rev="feat/direct-sampler-composition")
Pkg.add("QUBOTools") # Declare the model dependency in the consumer project.
using QUBOPreprocessing
import QUBOTools as QT
model = QT.Model(Dict(:x=>1.5, :y=>-2.0), Dict((:x,:y)=>0.25))
ws, report = preprocess(model; rules=:identity)
result = materialize(ws)
solver_model = export_model(result)
restored = reconstruct(result, [0,1])
```

Supported concrete QUBOTools models have finite Float64 objective data and
built-in sparse, dense or dictionary normal forms. Identity export preserves
stored data, all variables, ordered labels, domain, sense, scale and offset
without numerical transformation. Labels must preserve equality/hash under
owned deep copies; unsupported identity-based mutable labels are rejected.
It certifies representation identity with
an empty reduction chain; it does not certify a supplied state's optimality.
Reconstruction validates a complete state and reports ordinary numerical energy,
including a finite-result flag. Source and returned mutable data are isolated.
`reset!` validates transactionally and creates a new generation; existing exports
keep their historical source/generation.

For repeated boundary changes, use `checkpoint(ws)`, `assume!(ws, label, value)`,
`changes(ws, checkpoint)` and `rollback!(ws, checkpoint)`. Assumptions restrict
the problem; they never certify an original global optimum. `unfix!` supports
local LIFO removal and a documented full rebuild/replay for arbitrary removal.
`materialize(ws)` rejects conditioned coefficients that Float64 cannot represent
exactly; `coefficient_type=Rational{BigInt}` exports the exact residual. Full
materialization and original-energy evaluation are explicit O(n+m) boundaries.
See the [workspace example](examples/workspace.jl) and
[workspace contracts](docs/src/workspace.md), including limits and costs.

Read the [source manual](docs/src/index.md), [API](docs/src/api.md),
[runnable example](examples/identity.jl) and [release instructions](RELEASE.md).
There is no advertised hosted manual. Core dependencies are QUBOTools and used
Julia standard libraries; QUBOTools has its own transitive dependencies.
The supported floors are Julia 1.10 and QUBOTools 0.16.2.

Run tests and the example from a checkout:

```sh
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
julia --project=. examples/identity.jl
julia --project=. examples/workspace.jl
julia --project=. examples/certificates.jl
julia --project=. examples/dominance.jl
julia --project=. examples/branch_search.jl
julia --project=docs -e 'using Pkg; Pkg.develop(path=pwd()); Pkg.instantiate()'
julia --project=docs docs/make.jl
```

Accepting maintainer and release authority: [@bernalde](https://github.com/bernalde).
The public JuliaQUBO organization owns the repository and retains access for
continuity. Human review is required before merging AI-assisted contributions.
Source is licensed under MPL-2.0; respective contributors retain ownership.

The [bootstrap issue #1](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/1)
tracks the bootstrap. See the manual's acceptance matrix for later owners.
The reversible conditioning slice addresses [#2](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/2).
The [certificate manual](docs/src/certificates.md) and
[runnable proof example](examples/certificates.jl) address
[#3](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/3).

The [dominance manual](docs/src/dominance.md), [cascade example](examples/dominance.jl)
and [bounded on/off pilot](scripts/dominance_pilot.jl) address
[#4](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/4).

[Branch workloads](docs/src/scopes.md) and the [bounded search example](examples/branch_search.jl)
exercise scoped fix/unfix and resumable inference for
[#5](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/5). Optional
`rollback!(ws, cp; report=true)` reports removed caller and inferred fixings as
original-index/value pairs in reverse application order without materializing a residual.

Load `QUBODrivers` to activate the optional `sample_preprocessed` and `Optimizer`
consumer methods. See [consumer guarantees and limits](docs/src/consumers.md) and
the [direct/ToQUBO example](examples/consumer.jl) for
[#6](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/6). Core workspace use
does not load QUBODrivers, MOI, JuMP or ToQUBO.
