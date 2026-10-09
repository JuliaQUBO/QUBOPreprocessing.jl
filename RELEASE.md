# Release instructions

Maintainer and release authority: @bernalde, with organization-admin access
continuity. The project version 0.1.0 is a candidate, not a release. Identity-only
bootstrap does not satisfy the planned first-release dominance/incremental scope.
No registration, tag, hosted manual or release is performed by this PR.

Before proposing a release, complete the [release issue #7](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/7):

1. Obtain human approval and merge the reviewed functional source. Configure
   main protection with human review and strict required checks matching the
   actual minimum/current CI contexts, following the ecosystem policy; do not
   weaken controls. Verify accepting maintainer and organization access.
2. Complete the workspace, arithmetic, dominance, reversible scope and direct
   consumer criteria in #2–#6, and accept the performance envelope in
   QUBOBenchmarks#30. Validate all numerical/ownership/transport guarantees.
3. Check UUID, version, MPL notices, root/docs compatibility and release notes
   against the intended source. Write Changelog and Breaking changes sections
   suitable for General review. No dependency license ownership transfers.
4. Run package tests, documentation and examples, minimum/current fresh installs
   at the exact candidate SHA, optional consumer/conformance/integration tests,
   and current-head CI. Record resolved versions, source identity and results.
5. Under a separate explicit release request, use the normal Julia General route:
   reviewed merged source → Registrator submission → General merge → matching
   tag/release through a separately reviewed TagBot setup or maintainer procedure.
   Follow the current General/Registrator checks; submission is not registration.
6. Verify a fresh unqualified `Pkg.add("QUBOPreprocessing")` only after the registry
   entry exists. Confirm installed version/source, imports and executable examples.
7. Under separate authorization, deploy/verify package documentation, then refresh
   QUBO discovery/canary and the normally resolving QUBODecomposition integration.

Keep source-based instructions until registration. Record source, tag, registry,
installed identity and served documentation as separate evidence. Do not release
other ecosystem packages unless their runtime/compat changes require it.
