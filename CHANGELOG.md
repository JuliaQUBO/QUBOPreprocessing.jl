# Changelog

## 0.1.1

Second public release adding the Phase 2 certified reduction passes, composed proof
chains, and multi-pass scheduling:

- Certified QUBO-to-Ising domain conversion and spin gauge maps with reversible
  certificate translation (#13, #34).
- Composed elimination, relation, and persistency certificates with universal
  original-state lifting (#14, #35).
- Exact degree-0, degree-1, and degree-2 local variable elimination (#15, #36),
  certified signed pair relations and contractions (#16, #37), and guarded
  zero-field degree-3 Ising star-triangle reduction (#17, #38).
- Mixed exact reduction pass scheduling and 7-phase work/allocation accounting
  (#20, #39).
- Optional certified probing with reversible branch bounds and feasible witnesses
  (#11, #40), roof-duality strong persistency (#12, #41), gauge-submodular
  component recognition and minimum-cut fixing (#19, #42), weighted Max-Cut edge
  and triangle reductions (#18, #43), and exact coefficient compression and
  sparsification (#21, #44).

## 0.1.0

First public release of the bounded certified preprocessing API.

- Identity-preserving exports and strict-dominance preprocessing for finite
  Float64 QUBOTools models, with independently verifiable proof chains.
- Reusable sparse workspaces with explicit assumptions, exact conditioning,
  checkpoints, LIFO rollback, arbitrary-unfix rebuild/replay and resumable
  propagation limits.
- Exact coefficient-preserving Float64 or rational residual export and complete
  original-state reconstruction, including scope and generation provenance.
- Optional QUBODrivers direct sampling and MOI/ToQUBO composition with shared
  budgets, final original-objective evaluation and qualified solver statuses.
- Executable manuals, core and optional compatibility lanes, source coverage,
  and a measured operating envelope with explicit no-benefit regimes.

### Breaking changes

This is the first public release; there is no earlier release to migrate from.
The optional solver factory is accessed as `QUBOPreprocessing.Optimizer`; it is
not exported into the caller's namespace.

### Compatibility and limits

Julia 1.10 and QUBOTools 0.16.2 are the supported floors. Optional consumers require
QUBODrivers 0.6.5 or later in the supported 0.6 series. Future incompatible workspace,
checkpoint or certificate contracts require an explicit compatibility decision.

Assumptions certify a restricted scope. Numerical energy evaluation is Float64;
exact stored-value proofs do not remove numerical evaluation limits. Approximate
or local child results do not become global optima. General probing, roof duality,
weak persistency and later structural reduction families are outside this release.
