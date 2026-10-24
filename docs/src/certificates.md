# Sound bounds and proof verification

A solver result and a reduction proof answer different questions. Use this page
when another consumer needs to check why a variable was fixed, or when you need
to decide whether a captured proof still applies. The [user guide](guide.md) shows
where verification fits in a complete solve.

`prove_dominance(ws, label)` checks one strict unary reduction without changing
the workspace. [Bounded dominance](dominance.md) separately provides the queue,
propagation and inference undo trail. The standalone helper provides an
interval/exact witness seam and an independently structured verifier, with no
mandatory external backend.

```@example certificates
using QUBOPreprocessing
import QUBOTools as QT
ws = Workspace(QT.Model(Dict(:x=>3.0,:y=>0.0),Dict((:x,:y)=>-1.0)))
attempt = prove_dominance(ws,:x; max_exact_work=0)
@assert attempt.method == :interval
@assert verify_certificate(ws,attempt.certificate).valid
@assert isempty(assumptions(ws))
only(attempt.certificate.steps).value
```

## The exact represented problem

For stored finite Float64 coefficients, the mathematical objective is
``E(x)=\alpha(\beta+\sum_i L_i x_i+\sum_{i<j}Q_{ij}x_i x_j)`` with each
Float64 interpreted as its exact binary rational value. Both domains and senses
are supported directly; this check does not cast between domains.

Let ``\sigma=\operatorname{sign}(\alpha)`` for minimization and its negative
for maximization. Multiplication by its sign normalizes the direction without
forming an overflowing scaled coefficient. Zero/negative-zero scale yields no
strict proof because all states tie. Under the current fixed values, the
normalized derivative is ``D_i=\sigma(L_i+\sum_j Q_{ij}x_j)``. For a binary
free neighbor, its contribution lies between ``\min(0,\sigma Q_{ij})`` and
``\max(0,\sigma Q_{ij})``. For a spin neighbor it lies between
``-|Q_{ij}|`` and ``|Q_{ij}|``. Fixed neighbors contribute their exact value.

A strictly positive lower bound proves binary 0 / spin -1 in every scoped
optimum; a strictly negative upper bound proves 1. For spin, the energy
difference from -1 to +1 is twice this derivative, preserving its sign. Ties
never produce a strict fixing. Unscaled constants do not affect this test but
are bound in the witness and recomputed by the verifier.

The fast path starts with an enclosure checked against the exact cached field,
then expands each Float64 sum outward with `prevfloat`/`nextfloat`. Original
adjacency coefficients retain their represented Float64 values. It changes no
process-global rounding mode. Nonfinite enclosures or an unresolved sign trigger
budgeted exact rational fallback; no epsilon or ordinary rounded sum is used as
a proof. Exact fields are imported once and updated locally by the workspace;
no whole-model BigInt conversion occurs at each numerical check.

`DominanceAttempt` reports method, visited adjacency entries, fallback count
and exact work. `max_work` bounds adjacency visits across both passes;
`max_exact_work` reserves the field plus incident coefficient contributions for
fallback. A deadline, exhausted budget, zero scale or non-strict bound returns
no certificate. Work counts are structural, with integer bit complexity and
allocation costs additional. Public proof export copies source/scope explicitly
after a successful numeric check; deadline checks surround that atomic copy.

## Guarantee, scope, composition and verifier

Each reduction step or coordinate map carries an explicit guarantee class
queried with `step_guarantee` and `certificate_guarantee`, and a persistency
tag (`:strong` or `:weak`) queried with `persistency`:

- **`:energy_identity` (`DomainGaugeMap`):** bijective coordinate and gauge
  transformation ``F(x) = F'(T(x))`` preserving every state and its exact energy.
- **`:exact_elimination` (`EliminationStep`):** local variable elimination of a
  bounded-degree (`0 <= d <= 3`, default `max_degree=2` in `prove_elimination`,
  `eliminate_variable!` and `eliminate_low_degree!`) variable ``u`` certifying
  ``F'(y) = \operatorname{opt}_{x_u} F(y, x_u)`` (equivalent in normalized Ising
  spin coordinates to ``-|h_u + \sum_{j \in \partial u} J_{uj} s_j|``) across all
  ``2^d`` boundary assignments of `neighbors`, with an exact argmin reconstruction
  `table` (`tie_break=:low` or `:high`) and exact quadratic polynomial deltas
  (`constant_delta`, `linear_deltas`, `quadratic_deltas`). For `d == 3`
  (Boettcher–Davidheiser (2008) Section II Rule V Eq. (4) zero-field Ising
  star–triangle reduction), ``u`` must have three distinct free neighbors with
  nonzero couplings and an exact zero effective Ising field ``h_u = 0`` at the
  moment of application so that spin-flip symmetry makes the local minimum an even
  function of its three neighbors (pure constant + pair representation in Ising
  coordinates, with zero cubic interaction ``\alpha_{123} = 0`` and zero neighbor
  Ising field shifts). Nonzero cubic interactions are refused with
  `:nonquadratic_elimination`, and nonzero center effective fields at `d == 3` are
  refused with `:nonzero_field`. `unique_argmin` records whether the minimizing
  value of ``u`` is strict on all boundary states. Higher-degree variables are
  skipped/refused (`:degree_too_high`) with no higher-order truncation.
- **`:optimum_preserving_restriction` (`DominanceStep`, `RelationStep`, `ProbingStep`, `RoofDualityStep`, `SubmodularCutStep`, `MaxCutStep`):**
  unary value fixing (`DominanceStep`), signed pair contraction
  ``s_u = \sigma_{\text{orig}} s_v`` (`RelationStep`, proved via single-endpoint
  `:interval` / `:exact` coupling dominance or Glover–Lewis–Kochenberger (2018)
  Theorems 3.1–3.4 cross-endpoint `:glk_pair` implication bounds with favoring
  coupling ``-\sigma \tilde{J}_{uv} > 0``), trial-branch probing fixing
  (`ProbingStep`, proved via `prove_probing` / `apply_probing!` / `probe_variables!`
  when the trial branch lower bound ``L`` after reversible trial conditioning and
  bounded trial dominance propagation strictly exceeds the verified parent-scope
  feasible witness upper bound ``U``, ``L > U``), exact implication-network
  roof-duality strong persistency fixing (`RoofDualityStep`, proved via
  `prove_roof_duality` / `apply_roof_duality!` from an independently verified
  exact rational maximum ``S``–``T`` flow ``f`` and dual minimum cuts
  ``(\mathcal{R}_S, V \setminus \mathcal{R}_S)`` and
  ``(V \setminus \mathcal{R}_T, \mathcal{R}_T)`` where literal ``2u - 1 \in \mathcal{R}_S \land 2u \in \mathcal{R}_T``
  for ``s_u = +1`` or ``2u \in \mathcal{R}_S \land 2u - 1 \in \mathcal{R}_T``
  for ``s_u = -1``), direct gauge-submodular component cut fixing
  (`SubmodularCutStep`, proved via `prove_submodular_cut` / `apply_submodular_cut!`
  on a closed active residual component ``C`` with verified bipartite spin gauge
  ``\sigma_a \in \{-1, +1\}`` making all active couplings ``\tilde{J}'_{ab} \le 0``
  and verified ``(|C| + 2)``-vertex maximum ``S``–``T`` flow and minimum cut), or
  weighted Max-Cut edge/triangle restriction (`MaxCutStep`, proved via
  `prove_maxcut` / `apply_maxcut!` on ``G_{\text{MC}} = (\{0\} \cup F, E_{\\text{cut}}, w)``
  from the exact subset-flip margin ``M_{ab}(\sigma) = -\sigma J_{ab} + \sum_{c \in C_{\text{tri}}} \gamma_{abc}(\sigma) - \sum_{d \notin \{a, b\} \cup C_{\text{tri}}} |J_{ad}|``
  with verified external triangle slack ``R_c^{(ab)}``). Tagged `:strong` when
  every optimum of the current residual satisfies the restriction, or `:weak`
  when at least one optimum of the current residual satisfies the restriction.

Each `DominanceCertificate` (aliased as `ReductionCertificate`) owns a source
snapshot, generation, branch-specific checkpoint, explicit caller assumptions
and an ordered chain of `DominanceStep`, `RelationStep` and `EliminationStep`
records. Because steps are composed sequentially:

1. If ``F_k`` preserves all (or at least one) optima of ``F_{k-1}`` and step ``k``
   is certified on the evolved residual ``F_k``, then ``F_{k+1}`` preserves all
   (or at least one) optima of ``F_0``.
2. Weak restrictions are **not** closed under simultaneous application: if two
   weak steps hold individually on ``F_k``, the second must be re-certified on
   ``F_{k+1}`` after the first updates the residual. Default `propagate!(ws)`
   remains strong-only (`allow_weak=false`); `apply_weak_batch!` and
   `propagate!(ws; allow_weak=true)` apply weak steps sequentially on the
   evolving residual.
3. Reconstruction (`reconstruct`) walks `reduction_chain` in **reverse**
   application order so every `DominanceStep`, `RelationStep` and
   `EliminationStep` reads only survivor/representative/boundary values that have
   already been reconstructed.

`verify_certificate(ws, certificate)` compares actual source data as well as
generation, checks the live caller scope and exact current trail-tip checkpoint
(generation, epoch, depth and serial), then independently evolves the exact
original polynomial from raw source storage step by step across caller
assumptions, `DominanceStep`, `RelationStep` and `EliminationStep` records.
Later caller assumptions restrict still-free variables;
they are not retroactively substituted into earlier bound/constant evidence. It does not trust cached fields, adjacency, constant or queue and
does not call the producer's bound/conditioning helper. Exact bounds must match
exact recomputation; interval bounds must enclose the exact range and prove the
claimed strict sign; elimination steps must match all ``2^d \le 8`` boundary
states and argmin table values. A wider but still sound enclosure remains mathematically
valid; forged strict bounds, values, signs, tables, deltas, constants, predecessors,
reordered steps, unconditioned weak batches and source identity are rejected.
This is mathematical verification, not just hash authentication.

```@example certificates
root = checkpoint(ws)
assume!(ws,:y,0)
conditional = prove_dominance(ws,:x).certificate
@assert verify_certificate(ws,conditional).valid
rollback!(ws,root)
@assert !verify_certificate(ws,conditional).valid
```

A branch assumption does not certify that the branch contains an original global
optimum. Removing/replacing its scope invalidates applicability, including when
the same values are later reapplied on another branch. Source/penalty edits
require `reset!` and a new generation. A root-global proof never depends on caller
assumptions. Heuristic solvers and source ToQUBO feasibility retain their own
separate correctness requirements.

Verification is an explicit boundary: source identity costs O(n+m), and each
step scans original storage, potentially O(steps*(n+m)) with sparse input and
O(steps*n²) for dense storage. `term_visits` reports charged storage work,
including a reserved full scan if interruption follows storage reconstruction.
Work/deadline exhaustion always yields `valid=false`. Proof capture, verification
and residual materialization costs must be included in consumer measurements;
the cheap witness helper alone is not whole-solve cost evidence.

A valid fixing proof does not authorize rounding the residual. Workspace
Float64 export still rejects coefficients/constants that cannot be represented
exactly; exact `Rational{BigInt}` transport is an explicit supported alternative.
Re-evaluating a lifted state's Float64 energy cannot repair an unsound transport.
Domain- and gauge-transported proofs (`prove_dominance(ws, label; map=...)`,
`export_certificate(ws; map=...)` and `transport_certificate(ws, cert, map)`)
bind the same source generation and caller assumptions; `verify_certificate`
independently recomputes the converted and gauged polynomial from raw source
storage and rejects wrong gauges, mismatched domains, stale maps or altered
variable ordering. Run `examples/certificates.jl`, `examples/domain.jl` and
`scripts/certificate_costs.jl` for executable examples and separate numeric-path,
proof-export and verification measurements.
