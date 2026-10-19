# QUBOPreprocessing.jl

[![CI](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/actions/workflows/ci.yml/badge.svg)](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://juliaqubo.github.io/QUBOPreprocessing.jl/dev/)
[![Coverage](https://codecov.io/gh/JuliaQUBO/QUBOPreprocessing.jl/branch/main/graph/badge.svg)](https://app.codecov.io/github/JuliaQUBO/QUBOPreprocessing.jl)

QUBOPreprocessing removes variables using certified strict-dominance deductions
and restores solver states to the original QUBO. Reusable workspaces support
assumptions, bounded propagation, checkpoints and rollback, so a search algorithm
can update a boundary without rebuilding the whole problem at every step.

With Julia 1.10 or later, install QUBOPreprocessing and QUBOTools:

```julia
using Pkg
Pkg.add(["QUBOPreprocessing", "QUBOTools"])
```

Declare QUBOTools directly in the consumer project when constructing its models.

```julia
using QUBOPreprocessing
import QUBOTools as QT

model = QT.Model(Dict(:x => 3.0, :y => -1.0), Dict((:x, :y) => -1.0))
ws, report = preprocess(model; rules=:dominance)
result = materialize(ws)
restored = reconstruct(result, Int[]) # Both variables were certified and removed.
@assert Dict(zip(original_variables(result), restored.state)) == Dict(:x => 0, :y => 1)
@assert restored.energy.value == -1.0
```

For a nonempty residual, solve `export_model(result)` and pass its complete state
in residual index order to `reconstruct`. `rules=:identity` disables inference.
Assumptions restrict the problem; their certificates do not establish an original
global optimum. Exact arithmetic certifies the stored Float64 objective, while
reported numerical energies retain ordinary floating-point limits. Materializing
a residual, checking a full certificate and restoring a state are explicit costs;
Float64 exports reject coefficient rounding, with exact rational export available.

Start with the [manual](https://juliaqubo.github.io/QUBOPreprocessing.jl/dev/), [workspace example](examples/workspace.jl)
and [branch search example](examples/branch_search.jl). Load QUBODrivers to activate
the optional direct sampler and MOI optimizer; the [consumer manual](docs/src/consumers.md)
and [ToQUBO example](examples/consumer.jl) explain budgets, solver guarantees and
sampling limits. Core workspace use does not load QUBODrivers, MOI, JuMP or ToQUBO.
See the [performance envelope](docs/src/performance.md) before selecting repeated
or one-shot preprocessing, and [release notes](CHANGELOG.md) for supported scope.

Tests, documentation builds and contribution policy are in [CONTRIBUTING.md](CONTRIBUTING.md).
Source is licensed under
[MPL-2.0](LICENSE); respective contributors retain ownership.
