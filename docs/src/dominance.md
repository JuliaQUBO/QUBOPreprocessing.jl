# Bounded strict dominance

After constructing a workspace, dominance is the inference step that may reduce
the solver input. This page explains which signs justify a fixing and how to
resume a bounded pass. See the [solve walkthrough](guide.md#guide-solve)
for what to do with its residual and report.

Select `Workspace(model; rules=:dominance)` and call `propagate!` explicitly,
or use `preprocess(model; rules=:dominance, limits...)`. For queue-driven
degree-0/1/2 exact local elimination (including arbitrary local fields, fill-edge
merging/cancellation and optional alternating dominance/elimination cascades),
select `Workspace(model; rules=:elimination)` or call
`eliminate_low_degree!(ws; cascade_dominance=true, ...)`. For queue-driven
certified pair relations and reversible signed contractions (`:interval`, `:exact`
and Glover–Lewis–Kochenberger cross-endpoint `:glk_pair`), select
`Workspace(model; rules=:relations)` or call
`contract_relations!(ws; max_fill=..., cascade_dominance=..., ...)` and inspect
active representatives/parities via `relation_map(ws)`. For deterministic mixed
pass scheduling across all four reduction families on one shared `Workspace`
and `Generation` without alternating QUBO↔Ising materializations, select
`Workspace(model; rules=:mixed)` or `preprocess(model; rules=:mixed, ...)` and
call `schedule_reductions!(ws; ...)`. Identity remains the
default. Neither path dispatches a solver or implicitly materializes a residual.
In pure dominance mode (`propagate!(ws)`), only strong unary dominance is enabled:
every reported value holds in **all** optima within the current caller scope.
Local variable elimination (`eliminate_variable!`, `eliminate_low_degree!`)
records an `EliminationStep` in `reductions(ws)` with its conditional argmin
reconstruction table rather than reporting the variable in `deductions(ws)` as a
globally fixed constant; when boundary ties occur (`tie_break=:low` or `:high`),
`persistency(step)` is `:weak` and preserves the optimal objective value and at
least one optimal reconstruction without claiming that all original optima or
their multiplicities are represented by a single tie choice. Pair relations,
weak ties, roof duality and heuristic choices are separate methods.

For minimization of the normalized objective, a binary derivative has bounds
`aᵢ + Σ min(0,bᵢⱼ)` and `aᵢ + Σ max(0,bᵢⱼ)` over free neighbors.
A strictly positive lower bound fixes 0; a strictly negative upper bound fixes 1.
For spins the field bounds are `aᵢ ± Σ abs(bᵢⱼ)`, fixing -1/+1 respectively.
The boundary field includes fixed neighbors. Maximization and negative scale
reverse the sign; positive scale magnitude does not alter optima. Zero scale
and equality yield no fixing. The binary/spin rules are equivalent under
`x=(s+1)/2`, rather than independent strengthening methods.

## Certified pair relations and Glover–Lewis–Kochenberger rules

For two free variables ``u \ne v`` and candidate parity ``\sigma \in \{-1, +1\}``
(representing ``t_u = \sigma t_v`` in normalized gauged spin coordinates, or
``x_u = x_v`` for ``\sigma_{\text{orig}} = +1`` and ``x_u = 1 - x_v`` for
``\sigma_{\text{orig}} = -1`` in binary coordinates), the two violating spin
configurations are ``V_1 = (t_u = -\sigma, t_v = +1)`` and
``V_2 = (t_u = +\sigma, t_v = -1)``. Let ``\tilde{h}_i`` and ``\tilde{J}_{ij}``
denote the direction-normalized spin fields and couplings, and let
``R_u = \sum_{w \notin \{u, v\}} |\tilde{J}_{uw}|`` and
``R_v = \sum_{w \notin \{u, v\}} |\tilde{J}_{vw}|``.

1. **Single-endpoint coupling dominance (`:interval`, `:exact`):** generalizes
   Boettcher–Davidheiser (2020) Section II Rule VI to arbitrary local fields by
   requiring flips of ``t_u`` alone to improve both ``V_1`` and ``V_2``:
   ``-\sigma \tilde{J}_{uv} - |\tilde{h}_u| - R_u > 0`` (`:strong`) or ``\ge 0``
   (`:weak` with `allow_weak=true`).
2. **Glover–Lewis–Kochenberger (2018) Section 3 Theorems 3.1–3.4 cross-endpoint
   pair rule (`:glk_pair`):** translated from GLK's maximization of
   ``\sum_i c_i x_i + \sum_{i \ne j} Q_{ij} x_i x_j`` (with symmetric off-diagonal
   ``Q_{ij} = Q_{ji} = q_{ij}/2``) to normalized minimization in spin coordinates,
   and requiring a favoring coupling ``\text{center} = -\sigma \tilde{J}_{uv} > 0``:
   - **Branch A** rules out ``V_1`` by flipping ``t_u \to +\sigma``
     (half-margin ``m_u(V_1) = -\sigma \tilde{J}_{uv} - \sigma \tilde{h}_u - R_u``)
     and ``V_2`` by flipping ``t_v \to +1``
     (half-margin ``m_v(V_2) = -\sigma \tilde{J}_{uv} - \tilde{h}_v - R_v``),
     mapping both violating states directly to ``(+\sigma, +1)`` in one flip.
   - **Branch B** rules out ``V_1`` by flipping ``t_v \to -1``
     (half-margin ``m_v(V_1) = -\sigma \tilde{J}_{uv} + \tilde{h}_v - R_v``)
     and ``V_2`` by flipping ``t_u \to -\sigma``
     (half-margin ``m_u(V_2) = -\sigma \tilde{J}_{uv} + \sigma \tilde{h}_u - R_u``),
     mapping both violating states directly to ``(-\sigma, -1)`` in one flip.
   Taking the branch with the larger lower bound ``\text{lo}_{\text{glk}}``,
   ``\text{lo}_{\text{glk}} > 0`` certifies `:strong` persistency and
   ``\text{lo}_{\text{glk}} == 0`` (when `allow_weak=true` and ``\text{center} > 0``)
   certifies `:weak` persistency.
3. **Explicitly deferred GLK rules:** single-branch inequality implications
   (``x_u + x_v \ge 1``, ``x_u + x_v \le 1``, ``x_u \le x_v`` when only one of
   ``V_1, V_2`` is ruled out) do not induce an unconstrained parity substitution
   ``s_u = \pm s_v`` without auxiliary slack variables or penalty terms, and GLK
   Section 4 multi-neighbor matrix rules require higher-order neighborhood scans;
   both are explicitly deferred outside unconstrained quadratic pair contraction.

## Guarded zero-field degree-3 Ising star–triangle reduction

Eliminating a degree-three vertex ``s_u \in \{-1, +1\}`` with neighbors
``s_1, s_2, s_3 \in \{-1, +1\}`` generally introduces a cubic term
``J_{123} s_1 s_2 s_3``. When the current effective Ising field of the center is
rigorously zero (``h_u = 0``), spin-flip symmetry implies that the local optimal
contribution (for minimization with positive scale, ``\operatorname{dir} = +1``;
negated when ``\operatorname{dir} = -1``),
```math
\phi(s_1, s_2, s_3) = -\operatorname{dir} \cdot |J_1 s_1 + J_2 s_2 + J_3 s_3|,
```
is an even function ``\phi(-s_1, -s_2, -s_3) = \phi(s_1, s_2, s_3)`` of the three
neighbors. Consequently, both its linear Fourier terms and its cubic Fourier term
vanish identically, yielding the pure constant + pairwise triangle representation
of Boettcher–Davidheiser (2008), Section II Rule V Eq. (4) (translated from the
paper's leading-minus Hamiltonian ``H = -\sum J_{ij} \sigma_i \sigma_j`` to this
package's ``\min_s (s^T J s + h^T s + c)`` convention):
```math
\begin{aligned}
\varepsilon_0 &= |J_1 + J_2 + J_3|, \quad
\varepsilon_1 = |-J_1 + J_2 + J_3|, \quad
\varepsilon_2 = |J_1 - J_2 + J_3|, \quad
\varepsilon_3 = |J_1 + J_2 - J_3|, \\
\Delta c_{\text{spin}} &= -\operatorname{dir} \cdot \frac{\varepsilon_0 + \varepsilon_1 + \varepsilon_2 + \varepsilon_3}{4}, \\
\Delta J_{12} &= -\operatorname{dir} \cdot \frac{\varepsilon_0 - \varepsilon_1 - \varepsilon_2 + \varepsilon_3}{4}, \quad
\Delta J_{13} = -\operatorname{dir} \cdot \frac{\varepsilon_0 - \varepsilon_1 + \varepsilon_2 - \varepsilon_3}{4}, \quad
\Delta J_{23} = -\operatorname{dir} \cdot \frac{\varepsilon_0 + \varepsilon_1 - \varepsilon_2 - \varepsilon_3}{4}.
\end{aligned}
```
Neighbor fields ``h_1, h_2, h_3`` may be arbitrary (`spin_field_deltas` on
``w_1, w_2, w_3`` are zero); the zero-field precondition is strictly local to the
eliminated center ``u`` at the moment of application. Conditioning a fourth
neighbor can induce a nonzero field ``h'_u \ne 0`` (which invalidates degree-3
eligibility in ``O(1)`` via the cached exact Ising field) or cancel an existing
field to ``h'_u = 0`` (which unlocks degree-3 eligibility). Small floating-point
fields are converted to exact `Rational{BigInt}` without rounding to zero.
When `max_degree=3` is requested in `eliminate_low_degree!`, `max_fill` bounds
the number of new triangle edges introduced per step and defers blocked vertices
reversibly on the trail so progressive `max_fill` increases reconsider them
without rescanning the graph.

```@example dominance
using QUBOPreprocessing
import QUBOTools as QT
ws = Workspace(QT.Model(Dict(:x=>3.0,:y=>1.0,:isolate=>0.0),
                        Dict((:x,:y)=>-2.0)); rules=:dominance)
root = checkpoint(ws)
first = propagate!(ws; max_deductions=1)
@assert first.stop_reason == :deduction_limit
@assert verify_certificate(ws,export_certificate(ws)).valid
last = propagate!(ws)
@assert last.stop_reason == :quiescent
@assert isempty(assumptions(ws))
@assert length(deductions(ws)) == 2
result = materialize(ws)
@assert verify_certificate(ws,result.certificate.proof).valid
@assert QT.variables(export_model(result)) == [:isolate]
deductions(ws), last
```

## Incremental work and interruption

Construction prepares exact `Rational{BigInt}` fields and derivative-bound
caches once, plus an initial original-index-order queue. Unlike the standalone
`prove_dominance` interval/fallback helper, propagation reads its exact caches
and records `method=:exact`. Installing one deduction updates only its free
neighbors and queues each dirty neighbor once. No QUBOTools constructor, full
conversion, source copy or proof export occurs per deduction. Bit complexity
is additional to structural counts. After the initial scan, an unchanged call
performs no candidate or adjacency work. Genuine cascades may touch the graph.

Per-call limits are nonnegative machine-sized integers:

| Limit | Charged work |
| :-- | :-- |
| `max_work` | candidate checks plus deduction-update adjacency visits |
| `max_deductions` | committed deductions |
| `max_exact_work` | cached sign checks and conservative reservations of one constant plus three exact values per incident edge for an attempted update |
| `deadline_ns` | absolute `UInt64` monotonic `time_ns()` deadline |

A complete update is reserved before commitment. Fixed-neighbor skips can make
exact reservations conservative. If a deduction cannot fit, its queue entry
remains pending; its examined candidate/sign check is charged again on resume.
Deadline checks surround preparation and run per incident edge; the short
commit/queue-journal boundary finishes without interruption. These are
algorithmic limits, not hard real-time or asynchronous process-cancellation guarantees.

Reports use `:work_limit`, `:deduction_limit`, `:verification_limit`, `:deadline`
or `:quiescent`. Every stop retains a sound committed prefix. A later call
continues the pending queue. `pending` includes queued entries already fixed
by a cascade until they are consumed. Report totals count executed/reserved
propagation work even if the model is later rolled back. Initialization, caller
updates, replay, explicit export, verifier and solver costs are separate.

Queue consumption and fixings both have undo records. Rollback restores exact
fields, bounds, constant, pending cursor/flags, caller and deduction provenance.
`changes(ws, cp)` returns caller pins; `deductions(ws; since=cp)` returns only
inferences. Both inspect fixing records, skipping queue-only history. Checkpoints
are constant-size, and stale branches/resets are rejected. Arbitrary `unfix!`
conservatively discards deductions and replays only retained explicit callers;
it is a documented full rebuild. Resume propagation explicitly afterward.

## Proof and consumer boundaries

`export_certificate(ws)` explicitly copies the original source and ordered proof
chain, or returns `nothing` in constant-size work when there are no deductions.
Each step records its caller-prefix length: adding a later assumption does not
rewrite an earlier bound or constant. The independent verifier substitutes the
birth scope and validated predecessor chain in the original polynomial. A
root-global step has caller-prefix length zero. Captured certificates require
the exact current trail tip; historical branch evidence is rejected after rollback,
replay or reset even if the same assignments are reapplied.

`materialize` captures an owned residual, label map, complete fixed assignment
and proof chain. Root deductions have `certificate.scope == :original`; explicit
caller pins produce `:assumptions`. Caller pins do not prove the branch contains
a global optimum of the original problem. Default Float64 export still requires
exactly representable residual coefficients/constants; otherwise request
`coefficient_type=Rational{BigInt}` and a compatible consumer. Certified inference
does not authorize rounding. Reconstruction validates every free residual value
and restores all fixed values in original order. With no free variables, the
zero-dimensional residual is handled locally with an empty child state.
When free variables remain, propagation does not prove an arbitrary state optimal.

## Bounded evidence

The exhaustive tests independently enumerate original/scoped optima on guarded
tiny fixtures, compare every residual energy, verify all deductions, and check
binary/spin equivalence. Sparse local-change tests compare n=10 and n=2000
work/allocation shape without wall-time thresholds. Run
`examples/dominance.jl` for the resumable cascade and
`scripts/dominance_pilot.jl` for a tiny paired on/off CPU pilot. The pilot charges
workspace construction, propagation, proof capture/verification, model export,
the same bounded exhaustive child, reconstruction and audit. It retains every
paired repetition and separates phases. Reduced variables/edges and total
costs are reported together, including no-reduction controls. This pilot is
not the accepted operating envelope or an ecosystem adoption decision; those
remain with QUBOBenchmarks issue #30.

The retained source artifact `docs/evidence/dominance-pilot.md` records the
producing revision and all paired raw rows. In that tiny warm run, the all-fixed
case reduced total time, while the cascade and both no-reduction controls were
slower with preprocessing. Variable reduction alone did not predict payoff.

For degree-0/1/2 local elimination (`eliminate_low_degree!`, `examples/elimination.jl`,
`scripts/elimination_pilot.jl`, and retained artifact `docs/evidence/elimination-pilot.md`
with raw rows in `docs/evidence/elimination-pilot.tsv`), the per-degree queues
`elim_queues[1..4]` track only vertices with active degree `0..3` so calls with
a smaller `max_degree` cutoff leave higher-degree buckets untouched for subsequent
calls with a larger `max_degree` without any rescan:
- **Dense / high-degree no-benefit control (`dense_k5`, 5-vertex `K_5`):**
  `elim_queues` are initially empty (`0` candidates examined, `0` edge visits, `32 -> 32`
  states). End-to-end `on` (including workspace construction and residual export)
  takes `1100.78 µs` (`401.4 KiB`) vs `650.26 µs` (`327.5 KiB`) `off` (median paired
  `+431.42 µs`).
- **Tiny sparse instances (`whisker_5`, 4-clique core + 1 leaf, `n = 5 -> 4`):**
  eliminating 1 degree-`<= 2` vertex halves the exhaustive child search (`32 -> 16`
  states), but workspace construction, exact `Rational{BigInt}` table certification,
  proof verification and residual materialization take `481.00 µs` (`255.2 KiB`)
  vs `287.09 µs` (`257.4 KiB`) `off` (median paired `+199.98 µs`).
- **Break-even and sparse payoff (`whisker_7`, `whisker_10`, and `cycle_8`):**
  each eliminated degree-`<= 2` vertex halves the downstream exponential search
  space at `O(touched)` local cost (`<= 4` boundary evaluations per vertex),
  crossing end-to-end break-even against the exact-enumeration child at 3
  eliminated variables (`whisker_7`, `128 -> 16` states, `1824.74 -> 1054.68 µs`,
  median paired `−754.36 µs`, `1274.6 -> 353.7 KiB`), reaching a ~14x total time
  and ~27x allocation reduction at 6 eliminated variables (`whisker_10`, `1024 -> 16`
  states, `29738.92 -> 2094.45 µs`, median paired `−18940.16 µs`, `13622.6 -> 502.2 KiB`),
  and solving `cycle_8` completely where strict dominance removes 0 variables
  (`256 -> 1` state, `2920.62 -> 1436.53 µs`, median paired `−1518.64 µs`).

For guarded zero-field degree-3 Ising star–triangle reduction (`max_degree=3`,
`scripts/star_triangle_pilot.jl`, and retained artifact
`docs/evidence/star-triangle-pilot.md` with raw rows in
`docs/evidence/star-triangle-pilot.tsv`), `max_degree=2` remains the default
policy and `max_degree=3` is opt-in:
- **Zero-field instances (`zero_field_k4`, `zero_field_wheel_w6`, `zero_field_subdivided_10`):**
  on `zero_field_k4` (`n = 4`), `deg3` solves the graph completely (`16 -> 1`
  state, `10/20/37` candidate/edge/exact work), but on 16 states the 8-state
  `Rational{BigInt}` table certification costs more than direct enumeration
  (`+1707.74 µs` vs `off`, `+667.38 µs` vs `deg2`). On `zero_field_wheel_w6`
  (`n = 6`, `64 -> 16` states, `−552.97 µs` vs `deg2`) and
  `zero_field_subdivided_10` (`n = 10`, `1024 -> 256` states under `deg2` vs
  `1024 -> 32` states under `deg3`, `10192.32 -> 2173.07 µs`, median paired
  `−7903.97 µs` vs `deg2` and `−133860.71 µs` vs `off`), eliminating zero-field
  degree-3 stars pays off.
- **Conditioned-field instances (`conditioned_invalidated_8`, `conditioned_unlocked_8`):**
  when a leaf fixing drops a degree-4 hub to degree 3 while inducing a nonzero
  center field (`conditioned_invalidated_8`), `deg3` rejects the hub in `O(1)`
  with `0` additional edge visits and `0` additional exact table work (`12/1/13`
  vs `10/1/13`); when the induced shift cancels the center field to `0`
  (`conditioned_unlocked_8`), `deg3` unlocks star–triangle reduction and cascades
  (`128 -> 16` states, `4635.77 -> 1958.97 µs`, median paired `−2799.52 µs` vs `deg2`).
- **No-benefit nonzero-field control (`no_benefit_cubic_8`):** on a 3-regular
  cube where all 8 degree-3 vertices have nonzero fields, `deg3` rejects all 8
  candidates in `O(1)` with `0` edge visits and `0` exact table work (`8/0/0`
  work vs `0/0/0` under `deg2`, `+926.23 µs` vs `deg2`).

## Mixed exact reduction pass scheduling and 7-phase pipeline accounting

`schedule_reductions!(ws; ...)` (invoked automatically by
`preprocess(model; rules=:mixed, ...)`) runs a deterministic cheap-first fixpoint
loop on one shared `Workspace` and `Generation` without alternating QUBO↔Ising
model materializations:

1. **Cheap dirty-neighborhood propagation (`:dominance`):** drains all dirty
   unary dominance candidates (`st.queue`).
2. **Degree-`<= 2` local elimination (`:elimination`):** drains buckets 1..3
   (degrees 0, 1, 2) under `max_fill` / `max_total_fill`, immediately cascading
   back to `:dominance` whenever an elimination dirties a neighbor's derivative
   bounds.
3. **Optional guarded degree-3 star–triangle (`:star_triangle`):** disabled by
   default (`enable_star_triangle=false`); when enabled and cheap passes are
   quiescent, applies at most one zero-field degree-3 elimination before returning
   to `:dominance` and `:elimination`.
4. **Bounded pair relations (`:relations`):** when earlier passes are quiescent,
   examines active relation candidates under `relation_work_budget` and
   `max_fill` / `max_total_fill`, applying at most one signed contraction before
   returning to `:dominance` and `:elimination`.

`ScheduleReport` records per-pass summaries (`passes::Vector{SchedulePassSummary}`),
per-family deduction counts (`dominance_deductions`, `elimination_deductions`,
`star_triangle_deductions`, `relation_deductions`), introduced `fill_edges`,
initial/residual variable and edge counts, `optional_passes_disabled`, and exact
stop reasons (`:quiescent`, `:work_limit`, `:verification_limit`,
`:deduction_limit`, `:deadline`, `:unsupported_arithmetic`, `:fill_limit`,
`:optional_pass_disabled`).

`audit_pipeline!(model_or_ws; ...)` measures and reports `PipelineAccounting`
with `PhaseAccounting` across all seven lifecycle boundaries
(`conversion_import`, `discovery`, `arithmetic_fallback`, `verification`,
`export_phase`, `reconstruction`, `rollback_replay`). Run `examples/scheduler.jl`
for the resumable mixed schedule and `scripts/scheduler_pilot.jl` for the 6-mode
paired ablation study (`off`, `dominance`, `elimination`, `relations`,
`mixed_cheap`, `mixed_star`), retained in `docs/evidence/scheduler-pilot.md` and
`docs/evidence/scheduler-pilot.tsv`.

## Optional certified probing with reversible branch bounds and feasible witnesses

When cheap unary dominance is quiescent on a frustrated instance, optional
trial-branch probing (`prove_probing`, `apply_probing!`, `probe_variables!`)
can certify additional strong constant fixings using the existing reversible
checkpoint/rollback trail and a verified parent-scope feasible witness:

1. **Witness validation (`witness_upper = U`):** validates a complete
   parent-scope assignment (original-order `AbstractVector`, label `AbstractDict`,
   or [`Reconstruction`](@ref)) for domain membership and compatibility with all
   active caller assumptions and committed workspace reductions, then evaluates
   its exact direction-normalized objective ``U = d \cdot E(w)``.
2. **Reversible trial conditioning and bounded cascade (`branch_steps`):**
   takes a constant-size checkpoint, temporarily conditions on the opposite
   branch ``x_i = \bar{w}_i``, and propagates up to `max_rounds` (and
   `max_trial_fixes`) of certified strict unary dominance steps on the trial
   branch.
3. **Conservative canonical branch lower bound (`branch_lower = L`):** evaluates
   the canonical spin and positive/negative-gauge Boolean coefficient lower
   bounds (`:interval` outward-rounded `Float64` first, falling back to `:exact`
   `Rational{BigInt}` under `max_exact_work`) on the propagated trial residual.
   Because the bound is defined on the canonical spin representation
   ``(c_{\text{spin}}, h_{\text{spin}}, J_{\text{spin}})``, it is invariant
   under QUBO↔Ising domain conversion and `DomainGaugeMap` transformations.
4. **Strict exclusion contract (`L > U`):** only when ``L > U`` is the opposite
   branch refuted and ``x_i = w_i`` certified with `:strong` persistency in a
   [`ProbingStep`](@ref) (after rolling back all trial mutations to the exact
   pre-probe checkpoint). Equal bounds (``L = U``), inconclusive bounds
   (``L < U``), poor witnesses, or budget/deadline interruptions (`max_candidates`,
   `max_work`, `max_exact_work`, `deadline_ns`) abstain and restore the workspace
   to its pre-probe checkpoint while charging executed work in [`ProbingAttempt`](@ref)
   or [`ProbingReport`](@ref).

Probing is disabled in default `preprocess` and `schedule_reductions!` passes so
callers who do not invoke `probe_variables!` or `apply_probing!` pay zero overhead.
Because each candidate probe visits the active graph to evaluate ``L``, probing
only pays off when a strong primal witness is already available and cheap
dominance is blocked by local frustration on a small candidate set (`candidates`,
`max_candidates`, `max_rounds=1`).
