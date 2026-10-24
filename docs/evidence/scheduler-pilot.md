# Mixed exact reduction pass scheduling and 7-phase accounting pilot

This bounded smoke and ablation pilot addresses issue #20; it is not the accepted
performance or adoption envelope owned by QUBOBenchmarks #30. Eight deterministic
spin minimization fixtures (`sparse_mixed_cascade_10`, `dense_no_reduction_8`,
`zero_field_star_gadget_10`, `nonzero_field_relations_10`,
`high_dynamic_range_8`, `degenerate_optima_8`, `repeated_fix_unfix_8`, and
`gauge_equivalent_cascade_8`), five paired repetitions each across `off`,
`dominance`, `elimination`, `relations`, `mixed_cheap` (`schedule_reductions!`
with `enable_star_triangle=false`), and `mixed_star` (`schedule_reductions!` with
`enable_star_triangle=true`), no randomness. CPU timings and byte allocations are
machine observations with no pass/fail speed threshold or universal claim.

Producing commit: `579025a47faf35df91890891ad23e707f68190a4` (branch `feat/issue-20-mixed-scheduler`, base `fc12b2ac94252bad07363ae762695fd8a7fb3879`).
Julia 1.10.11, QUBOTools 0.16.3, Linux x86_64, CPU target sapphirerapids,
one Julia/OpenBLAS thread, clean git checkout.
No child/model exceeds ten spin variables; oversized input is rejected before
exponentiation. The same exact scalar exhaustive spin child is used for all
six modes. Workspace construction, pass execution (`propagate!`,
`eliminate_low_degree!`, `contract_relations!`, or `schedule_reductions!`),
proof export and independent `verify_certificate` verification, residual
`materialize` and `export_model`, child enumeration, `reconstruct` lifting and
exact original-energy audit are all included in total time and allocations for
active modes. `off` sends the original model directly to the same child and
charges state copying and the same exact original-energy audit. Two warmups per
fixture and mode precede measurement; measured dispatch order alternates across
repetitions.

| Case | Removed (`dom` / `elim` / `rel` / `mixed_cheap` / `mixed_star`) | Work `cand/edge/exact` (`mixed_cheap` → `mixed_star`) | States (`off` → `mixed_cheap` → `mixed_star`) | Median `off` / `mixed_cheap` / `mixed_star` µs | Median paired (`mixed_cheap−off` / `mixed_star−off`) µs | Median `off` / `mixed_cheap` / `mixed_star` KiB |
| :-- | --: | --: | --: | --: | --: | --: |
| `sparse_mixed_cascade_10` | 3 / 10 / 4 / 10 / 10 | `45/27/83` → `46/27/83` | 1024 → 1 → 1 | 13613.72 / 676.97 / 574.43 | −13145.27 / −13116.85 | 12448.4 / 549.5 / 549.9 |
| `dense_no_reduction_8` | 0 / 0 / 0 / 0 / 0 | `16/1176/680` → `16/1176/680` | 256 → 256 → 256 | 5798.64 / 5417.71 / 7341.80 | −380.93 / +2145.32 | 6041.8 / 7550.0 / 7550.0 |
| `zero_field_star_gadget_10` | 0 / 2 / 1 / 2 / 5 | `26/448/302` → `39/286/249` | 1024 → 256 → 32 | 57823.76 / 3924.03 / 1320.86 | −10411.83 / −56258.47 | 17285.3 / 4793.6 / 1371.8 |
| `nonzero_field_relations_10` | 0 / 5 / 4 / 5 / 5 | `35/270/225` → `35/270/225` | 1024 → 32 → 32 | 21585.78 / 1863.51 / 3159.73 | −19722.26 / −18323.70 | 19253.3 / 1217.8 / 1217.8 |
| `high_dynamic_range_8` | 3 / 8 / 2 / 8 / 8 | `34/30/76` → `34/30/76` | 256 → 1 → 1 | 2146.38 / 522.49 / 454.90 | −1623.88 / −1678.20 | 2845.3 / 462.6 / 462.6 |
| `degenerate_optima_8` | 0 / 8 / 1 / 8 / 8 | `36/26/73` → `38/26/73` | 256 → 1 → 1 | 1262.89 / 662.95 / 636.23 | −659.65 / −626.66 | 1669.7 / 503.8 / 504.4 |
| `repeated_fix_unfix_8` | 1 / 8 / 3 / 8 / 8 | `38/27/73` → `38/27/73` | 256 → 1 → 1 | 2681.96 / 944.89 / 950.79 | −1731.62 / −1745.99 | 2530.9 / 625.8 / 625.8 |
| `gauge_equivalent_cascade_8` | 1 / 8 / 3 / 8 / 8 | `38/27/73` → `38/27/73` | 256 → 1 → 1 | 3166.67 / 1292.60 / 1268.57 | −1894.63 / −1911.74 | 2531.5 / 744.9 / 744.9 |

Paired differences are computed per repetition before taking their median. All
240 paired exact optimal energies agree across `off`, `dominance`, `elimination`,
`relations`, `mixed_cheap`, and `mixed_star`:
- **Sparse cascading vs single-pass ablations (`sparse_mixed_cascade_10`, `nonzero_field_relations_10`):**
  on `sparse_mixed_cascade_10` (`n = 10, m = 11`), `dominance` alone removes 3
  variables (`1024 → 128` states) and `relations` alone removes 4 variables
  (`1024 → 64` states), whereas `mixed_cheap` and `mixed_star` interleave
  dominance with degree-`≤ 2` elimination to collapse all 10 variables (`1024 → 1`
  state, `−13145.27 µs` vs `off`, `12448.4 → 549.5 KiB`). On
  `nonzero_field_relations_10` (`n = 10, m = 20`), `dominance` removes 0
  variables and `relations` removes 4 variables (`1024 → 64` states), while
  `mixed_cheap` removes 5 variables (`1024 → 32` states, `−19722.26 µs` vs `off`,
  `19253.3 → 1217.8 KiB`).
- **Guarded degree-3 star–triangle (`zero_field_star_gadget_10`):**
  with `enable_star_triangle=false` (`mixed_cheap`), only the 2 degree-2 bridges
  are eliminated (`1024 → 256` states, `448` edge visits as `:relations` scans the
  surviving degree-3 stars). Enabling `enable_star_triangle=true` (`mixed_star`)
  eliminates the zero-field degree-3 stars before `:relations` runs, removing 5
  variables (`1024 → 32` states), reducing edge visits (`448 → 286`), median time
  (`3924.03 → 1320.86 µs`, `−56258.47 µs` vs `off`), and memory (`4793.6 → 1371.8 KiB`).
- **Dense frustrated control (`dense_no_reduction_8`):**
  on frustrated $K_8$ (`n = 8, m = 28`), no reduction applies in any pass
  (`256 → 256` states); `:relations` inspects all 56 directed pairs (`1176` edge
  visits, `84` exact fallbacks), increasing memory from `6041.8 KiB` to
  `7550.0 KiB`. Callers on dense instances can bound or disable `:relations` via
  `relation_work_budget`, `max_fill`, or `enable_relations=false`.
- **High dynamic range, degenerate optima, rollback/unfix, and gauge invariance
  (`high_dynamic_range_8`, `degenerate_optima_8`, `repeated_fix_unfix_8`,
  `gauge_equivalent_cascade_8`):**
  all four 8-variable stress fixtures reduce to `0` residual variables (`256 → 1`
  state) under `mixed_cheap` and `mixed_star` with identical work counts
  (`38/27/73` on `repeated_fix_unfix_8` and its gauge-transformed counterpart
  `gauge_equivalent_cascade_8`) and exact energy parity.

Raw artifact: [scheduler-pilot.tsv](scheduler-pilot.tsv)

SHA-256: `8348f6875f936133c729ee3f738b3c512ef3f0775f5bea5e009541690500cc4b`

Reproduce from a clean selected checkout:

```sh
OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/scheduler_pilot.jl > /tmp/scheduler-pilot.tsv
cp /tmp/scheduler-pilot.tsv docs/evidence/scheduler-pilot.tsv
```
