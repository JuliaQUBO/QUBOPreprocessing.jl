# API

For a complete sequence of calls, start with the [user guide](guide.md). This
page lists individual interfaces for looking up arguments and return contracts.

## Qualified optimizer factory

The optional solver factory is used as `QUBOPreprocessing.Optimizer` so that it
can share a session with other solver packages. It becomes available after
loading QUBODrivers.

```@docs
QUBOPreprocessing.Optimizer
```

## Exported API

```@autodocs
Modules = [QUBOPreprocessing]
Private = false
```
