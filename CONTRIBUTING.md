# Contributing

Follow the [accepted design](https://github.com/JuliaQUBO/QUBO.jl/blob/c0ab77d34e2281cfd6bd06e6c9c2f5ce13994670/docs/src/design.md#certified-preprocessing)
and the [ecosystem maintenance policy](https://github.com/JuliaQUBO/QUBO.jl/blob/main/docs/src/maintenance.md).
Keep functional changes on a feature branch and focused draft pull request.
Use Refs until the linked issue acceptance criteria are fully met. Include
independent tests, user documentation and actual verification evidence.

Disclose AI assistance. A human maintainer must review AI-assisted changes before
merge; automated reviews do not satisfy that requirement. Preserve accurate
contributor ownership and upstream notices when adapting material. Importing a
dependency does not transfer its copyright to newly authored files.

Accepting maintainer and release authority: @bernalde. Organization administrators
retain access for continuity; future maintainership/access changes need a separate
handoff. Registration, tagging, releases, hosted documentation and repository
settings changes are separate maintainer actions.

The core is QUBOTools plus used Julia standard libraries. Run
`julia --project=. -e 'using Pkg; Pkg.test()'`, the runnable core examples,
and the separate documentation build (`julia --project=docs docs/make.jl --skip-deploy`).
The test oracle uses independent scalar
and exact binary-value rational references on explicitly guarded tiny fixtures.
Run the workspace, certificate and dominance examples for their changed paths.
For optional consumer changes, develop the checkout into `test/integration`,
instantiate that environment, and run `test/integration/runtests.jl` and
`examples/consumer.jl` there. CI retains minimum/current core and consumer lanes.
Source coverage reports include both core and optional extension execution.

Documentation PRs build without publishing. The trusted main publisher uses the
`github-pages` environment and one shared destination lock; a manually selected
release must match its real tag, published GitHub release and General package tree.
Never treat a build, coverage badge or uploaded report as proof of deployment,
visible service results or package registration. Release preparation is tracked in
[RELEASE.md](RELEASE.md) and issue #7.
