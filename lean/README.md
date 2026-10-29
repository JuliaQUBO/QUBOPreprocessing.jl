# Kernel-checked Lean 4 formalization for `QUBOPreprocessing.jl`

This directory contains a standalone Lean `v4.33.1` / Mathlib `v4.33.1` formalization of the four
core mathematical results underlying `QUBOPreprocessing.jl` (Issue `#54` and `docs/src/dominance.md`):

1. **Proposition 1 (`QUBOPreprocessing.GaugeCoercive`)**: Exact affine bijection $s_i = 2 x_i - 1$
   ($x_i = (s_i + 1) / 2$) between Boolean variables $x_i \in \{0, 1\}$ and Ising spins
   $s_i \in \{-1, +1\}$; exact $n$-variable QUBO-to-Ising Hamiltonian identity; invariance of
   Ising energies, field magnitudes $|h_i|$, coupling magnitudes $|J_{ij}|$, $\ell_1$ interaction
   norms $\sum_{j \neq i} |J_{ij}|$, and coercive-field ratios
   $\rho_i = |h_i| / \sum_{j \neq i} |J_{ij}|$ under arbitrary spin-flip gauge transformations
   $g \in \{-1, +1\}^n$; equivalence between the Hammer–Hansen–Simeone (1984) QUBO first-order
   persistence bounds and the Ising coercive-field criteria $\pm h_i > \sum_{j \neq i} |J_{ij}|$;
   and soundness of coercive-field spin fixing across all neighbor configurations.
2. **Theorem 2 & Corollary 2.1 (`QUBOPreprocessing.CompositionRepair`)**: Abstract weak and strong
   preprocessing reduction steps (`ReductionStep` and `StrongReductionStep`); closure under
   composition (`ReductionStep.comp`, `StrongReductionStep.comp`); preservation of global minimum
   values and global minimizers (`ReductionStep.preserves_global_min`,
   `StrongReductionStep.image_global_min_eq`); monotonic and strictly improving post-processing
   solution repair (`repair_monotone`, `repair_strict_improvement`); and exact Walsh–Hadamard
   star–triangle elimination for a zero-field degree-3 Ising spin (`starMin_even`,
   `starMin_cubic_walsh_zero`, `starTriPoly_eq_starMin`, corresponding to Eq. (4) of
   `docs/src/dominance.md`).
3. **Proposition 3 (`QUBOPreprocessing.MaxCutTriangle`)**: Single-spin and joint triangle co-flip
   energy-reduction identities (`triEnergy_flip_a`, `triEnergy_flip_ac`); external-degree-aware
   triangle slack $\gamma_{abc}(\sigma)$ (`gammaTriangle`) and its closed forms in the supportive
   ($\sigma J_{ac} J_{bc} \ge 0$), frustrated ($\sigma J_{ac} J_{bc} \le 0$), and zero-residual
   ($R_c = 0$) regimes (`gammaTriangle_supportive`, `gammaTriangle_frustrated`,
   `gammaTriangle_zero_residual`); soundness of external-degree-aware Max-Cut triangle dominance
   (`maxcut_triangle_dominance_sound`, `maxcut_triangle_strict_improvement`); and the formal
   refutation of the uncorrected multicut triangle rule on signed weighted Max-Cut when
   $R_c > 0$ (`uncorrected_multicut_triangle_counterexample`).
4. **Theorem 4 (`QUBOPreprocessing.CompressionAudit`)**: Formal audit of Mücke, Gerlach &
   Piatkowski (2023), *Optimum-Preserving QUBO Parameter Compression* (`arXiv:2307.02195`,
   Theorem 2), including closed-endpoint suboptimal-tie counterexamples
   (`endpoint_tie_counterexample`, `quadratic_endpoint_tie_counterexample`), the open-interior
   ($\tau = 1/10 > 0$) negative-coupling lost-optimum counterexample where
   $\operatorname{opt}(F) = \{(1, 1)\}$ and $\operatorname{opt}(F') = \{(0, 0)\}$ are disjoint
   (`negative_quadratic_lost_optimum_counterexample`), subsumption of valid open-interior diagonal
   compression and positive-coupling sparsification by strict unary dominance
   (`diagonal_compression_subsumed_by_dominance`,
   `positive_quadratic_sparsification_subsumed_by_dominance`), and non-constant energy transport of
   nonzero in-place coefficient perturbations (`in_place_compression_nonconstant_shift`).

## Reproducing Verification

With Lean `v4.33.1` and the pinned Mathlib `v4.33.1` cache available:

```sh
cd lean
lake exe cache get
./verify.sh
```

If `lake` is installed in a non-default location, pass `QUBO_LAKE=/path/to/lake ./verify.sh`.

`./verify.sh` invokes `verify.py`, which:
1. Snapshots all project `.lean` sources and configuration files (`lean-toolchain`, `lakefile.toml`,
   `lake-manifest.json`, `verify.py`, `verify.sh`, `test/AxiomAudit.lean`) and enforces source-level
   policy checks forbidding `sorry`, `admit`, `sorryAx`, `native_decide`, `decide +native`,
   `axiom`, `unsafe`, `partial`, `opaque`, `extern`, `implemented_by`, and `unsafeCast`.
2. Compiles every module reachable from `QUBOPreprocessing` in topological order using
   `lean -DautoImplicit=false` inside an isolated temporary directory while treating the pinned
   Mathlib `.olean` cache as read-only.
3. Runs `test/AxiomAudit.lean` at private visibility across all compiled constants originating from
   project modules and verifies that transitive axiom dependencies are restricted to Lean's three
   standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
4. Writes machine-readable audit artifacts to `lean/verification/` (`result.json`,
   `environment.json`, `axioms.log`, `imports.json`, `sources.before.json`, `sources.after.json`).

The current verified audit (`lean/verification/result.json`) checks **58 public source theorems**
and **112 total project constants** across **5 modules**, with zero compiler warnings and only
Lean's three standard foundational axioms (`Classical.choice`, `Quot.sound`, `propext`).

## Module and Theorem Summary

| Module | Key Declarations | Paper / Doc Reference |
| :--- | :--- | :--- |
| `QUBOPreprocessing.GaugeCoercive` | `spinToBool_boolToSpin`, `boolToSpin_spinToBool`, `isSpin_boolToSpin_iff`, `isBool_spinToBool_iff`, `quboEnergy_eq_isingEnergy`, `isingEnergy_gauge_invariant`, `couplingNorm1_gauge_invariant`, `coerciveRatio_gauge_invariant`, `qubo_persist_zero_iff_ising_coercive_pos`, `qubo_persist_one_iff_ising_coercive_neg`, `coercive_pos_strictly_favors_neg_one`, `coercive_neg_strictly_favors_pos_one` | Proposition 1 (`docs/src/dominance.md`) |
| `QUBOPreprocessing.CompositionRepair` | `ReductionStep.id`, `ReductionStep.comp`, `ReductionStep.preserves_global_min`, `ReductionStep.global_min_value_eq`, `StrongReductionStep.comp`, `StrongReductionStep.image_global_min_eq`, `conditional_elimination_is_reduction`, `repair_monotone`, `repair_strict_improvement`, `starMin_le`, `starMin_achieved`, `starMin_even`, `starMin_cubic_walsh_zero`, `starTriPoly_eq_starMin` | Theorem 2, Corollary 2.1, Eq. (4) (`docs/src/dominance.md`) |
| `QUBOPreprocessing.MaxCutTriangle` | `triEnergy_flip_a`, `triEnergy_flip_ac`, `gammaTriangle_supportive`, `gammaTriangle_frustrated`, `gammaTriangle_zero_residual`, `maxcut_triangle_dominance_sound`, `maxcut_triangle_strict_improvement`, `uncorrected_multicut_triangle_counterexample` | Proposition 3 (`docs/src/dominance.md`, `src/maxcut.jl`, `test/maxcut.jl`) |
| `QUBOPreprocessing.CompressionAudit` | `endpoint_tie_counterexample`, `quadratic_endpoint_tie_counterexample`, `negative_quadratic_lost_optimum_counterexample`, `diagonal_compression_subsumed_by_dominance`, `pair_excluded_lower_eq_full_of_pos`, `positive_quadratic_sparsification_subsumed_by_dominance`, `in_place_compression_nonconstant_shift` | Theorem 4 (`docs/src/dominance.md`, `src/compression.jl`, `test/compression.jl`) |
