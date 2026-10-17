# Release instructions

Distribution uses Julia General. Maintainer and release authority is @bernalde,
with organization-admin access for continuity. The 0.1.0 scope is bounded strict
dominance, independent certificates, reversible workspaces and optional direct/MOI
composition. Later structural/probing/roof-duality work is outside that milestone.
Current acceptance and publication evidence belongs in
[issue #7](https://github.com/JuliaQUBO/QUBOPreprocessing.jl/issues/7), rather than
mutable status claims in the README or frozen manual.

## Before selecting a release source

1. Complete independent review and all current-head CI for the functional source.
   Follow CONTRIBUTING.md and any explicit maintainer exception recorded for the
   release. Verify accepting maintainer/org access. Main protection must enforce
   strict checks matching the actual minimum/current core, optional consumer and
   documentation contexts; coverage adds its own reported check. Settings changes
   require separate authorization and readback.
2. Verify #2–#6 and accept the bounded QUBOBenchmarks #30 envelope. Keep no-benefit,
   dense/cascade/replay costs and cheap off/bounded paths explicit. A smaller
   residual alone does not establish a performance benefit. Downstream candidate
   experiments can use source pins before registration.
3. Verify the final README's authorship condition in #7, or an explicit maintainer
   revision of that condition. Check the actual user example, real badges/links,
   source/license/UUID/version/compatibility and Changelog/Breaking changes notes.
   Keep bookkeeping here and in issue evidence.
4. Require real coverage generation, successful upload and a visible Codecov report
   for the selected source. CI retains core and optional-extension LCOV artifacts.
   Test jobs remain read-only; only the report uploader requests OIDC. Public fork
   PRs use Codecov's tokenless fork route; Dependabot may need its separate upload
   secret if OIDC cannot authenticate. Do not create/change credentials implicitly.
5. Run package tests, minimum/current optional conformance/ToQUBO tests, all core
   examples and strict documentation. Use a fresh project/depot for exact-SHA
   candidate installation and `scripts/install_smoke.jl`; the cheap core must not
   activate QUBODrivers/MOI/JuMP/ToQUBO. Record installed source/tree/versions.

## Infrastructure and tagging order

Merge reviewed coverage/docs/TagBot infrastructure before the final release-notes
and README source commit. With `GITHUB_TOKEN`, TagBot cannot tag a commit that
changes workflow files. Do not add a broad token or an empty version bump to evade
that restriction. Select a meaningful, independently reviewed final source whose
commit does not change workflows, and verify its default-branch push CI.

TagBot listens for JuliaTagBot comments and manual dispatch and uses the existing
GitHub token. Its tags do not trigger downstream workflows. The manual release-docs
refresh below supplies the explicit publication path without an SSH key. Confirm
Registrator/TagBot app scope and permissions before submission; repository write
access alone does not prove app installation.

Under the separately authorized release workflow, submit `@JuliaRegistrator register`
with a short `Release notes:` block on the verified release source. Observe the
registry PR/checks and General merge, then let TagBot finish the matching tag/release.
Submission, source merge and registry merge are distinct states. Do not retarget an
existing tag. If TagBot reports a concrete failure, diagnose it before selecting a
documented manual recovery path.

After General propagation, use a fresh project and fresh depot with the default
package server: `Pkg.Registry.update(); Pkg.add("QUBOPreprocessing")`. Assert version,
UUID/import behavior and equality of the registered tree, selected source tree,
installed manifest tree and tag's dereferenced commit. Run the installed smoke
example/tests. A version field or version-pinned install alone is insufficient.

## Hosted documentation

The prepared publisher targets Actions Pages at
`https://juliaqubo.github.io/QUBOPreprocessing.jl/`. Configure Pages with
`build_type=workflow` and the `github-pages` environment for main under separately
authorized settings work. A missing configuration/service activation remains an
explicit deployment gate; a successful PR build does not activate hosting.

PRs build without publishing. Trusted upstream main push/manual events append
Documenter's versioned `gh-pages` history under one destination lock, then deploy
the complete layout through Actions Pages. No preview or force push is enabled.
After a real published General release, dispatch `docs.yml` on main with
`release_tag=v0.1.0` and its verified full `release_commit`. The provenance gate
checks ancestry, package identity/version, tag target, non-draft release and General
tree before building that exact source. `docs/make.jl` requires committed source
and writes `buildinfo.toml` with version/commit/tree/channel for served-byte checks.

Verify the actual deployment record and served dev/version/stable pages, navigation,
search and rendered fragment links. Preserve dev and release aliases. Never infer
hosted content or coverage report visibility from a green upload/build alone.

## Ecosystem closeout

After unqualified installation/import works, refresh QUBO discovery and registry
canary, remove QUBODecomposition #16's temporary pin and verify its actual published
dependency floor before its own review/merge/release. Keep the default-off adoption
decision tied to measured costs. No QUBOTools/QUBODrivers/ToQUBO/QUBO version is forced
without a runtime/compatibility change. Close trackers only when their complete
acceptance criteria have evidence, and name any remaining admin/adoption tasks.
