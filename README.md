# QUBOPreprocessing.jl

Identity foundation for the [accepted certified preprocessing design](https://github.com/JuliaQUBO/QUBO.jl/pull/94).
**Only `rules=:identity` is implemented.** No dominance, reversible assumptions,
proof arithmetic, solver adapter or decomposition integration is available yet.
Candidate version 0.1.0 is unreleased and unregistered.

Install from the implementation branch, or substitute its exact reviewed SHA:

```julia
using Pkg
Pkg.add(url="https://github.com/JuliaQUBO/QUBOPreprocessing.jl", rev="feat/identity-bootstrap")
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

Read the [source manual](docs/src/index.md), [API](docs/src/api.md),
[runnable example](examples/identity.jl) and [release instructions](RELEASE.md).
There is no advertised hosted manual. Core dependencies are QUBOTools and used
Julia standard libraries; QUBOTools has its own transitive dependencies.
The supported floors are Julia 1.10 and QUBOTools 0.16.2.

Run tests and the example from a checkout:

```sh
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
julia --project=. examples/identity.jl
julia --project=docs -e 'using Pkg; Pkg.develop(path=pwd()); Pkg.instantiate()'
julia --project=docs docs/make.jl
```

Accepting maintainer and release authority: [@bernalde](https://github.com/bernalde).
The public JuliaQUBO organization owns the repository and retains access for
continuity. Human review is required before merging AI-assisted contributions.
Source is licensed under MPL-2.0; respective contributors retain ownership.

The [bootstrap issue #1](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/1)
tracks this slice. See the manual's acceptance matrix for later owners.
