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

Producing commit: `b619ba19d1b683555c76b78edbd8000006a5f2ef` (branch `feat/issue-20-mixed-scheduler`, base `fc12b2ac94252bad07363ae762695fd8a7fb3879`).
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
| `sparse_mixed_cascade_10` | 3 / 5 / 2 / 6 / 10 | `33/133/128` → `46/45/98` | 1024 → 16 → 1 | 36304.14 / 766.89 / 932.67 | −35558.45 / −35607.42 | 14756.7 / 658.4 / 645.2 |
| `dense_no_reduction_8` | 0 / 0 / 0 / 0 / 0 | `16/1176/680` → `16/1176/680` | 256 → 256 → 256 | 3976.86 / 5420.60 / 5944.22 | +1066.49 / +2195.24 | 6041.8 / 7550.0 / 7550.0 |
| `zero_field_star_gadget_10` | 0 / 2 / 1 / 2 / 5 | `26/448/302` → `39/286/249` | 1024 → 256 → 32 | 56509.84 / 6480.09 / 1670.45 | −10480.57 / −53682.01 | 17285.3 / 4793.6 / 1371.8 |
| `nonzero_field_relations_10` | 0 / 2 / 4 / 5 / 5 | `42/376/301` → `42/376/301` | 1024 → 32 → 32 | 23003.39 / 1270.46 / 1419.52 | −20976.09 / −21288.25 | 21345.4 / 1367.8 / 1367.8 |
| `high_dynamic_range_8` | 3 / 8 / 2 / 8 / 8 | `34/30/76` → `34/30/76` | 256 → 1 → 1 | 1972.80 / 531.14 / 456.48 | −1469.89 / −1434.08 | 2845.3 / 462.6 / 462.6 |
| `degenerate_optima_8` | 0 / 8 / 1 / 8 / 8 | `36/26/73` → `38/26/73` | 256 → 1 → 1 | 1196.81 / 571.80 / 513.27 | −575.51 / −726.40 | 1669.7 / 503.8 / 504.4 |
| `repeated_fix_unfix_8` | 1 / 8 / 3 / 8 / 8 | `38/27/73` → `38/27/73` | 256 → 1 → 1 | 1676.77 / 608.61 / 591.30 | −1031.20 / −1092.64 | 2530.9 / 625.8 / 625.8 |
| `gauge_equivalent_cascade_8` | 1 / 8 / 3 / 8 / 8 | `38/27/73` → `38/27/73` | 256 → 1 → 1 | 1909.07 / 1010.93 / 871.15 | −898.14 / −1037.92 | 2531.5 / 744.9 / 744.9 |

Paired differences are computed per repetition before taking their median. All
240 paired exact optimal energies agree across `off`, `dominance`, `elimination`,
`relations`, `mixed_cheap`, and `mixed_star`:
- **Sparse cascading vs single-pass ablations (`sparse_mixed_cascade_10`, `nonzero_field_relations_10`):**
  on `sparse_mixed_cascade_10` (`n = 10, m = 15`), `dominance` alone removes 3
  variables (`1024 → 128` states), `elimination` alone removes 5 variables
  (`1024 → 32` states), and `relations` alone removes 2 variables (`1024 → 256`
  states). Under `mixed_cheap`, `:dominance`, `:elimination`, and `:relations`
  (`relation_deductions >= 1`) combine to remove 6 variables (`1024 → 16` states,
  `−35558.45 µs` vs `off`, `14756.7 → 658.4 KiB`), and enabling
  `enable_star_triangle=true` (`mixed_star`) eliminates the zero-field degree-3
  center unlocked by the pair contraction and cascades the remaining triangle to
  0 residual variables (`1024 → 1` state, `133 → 45` edge visits, `−35607.42 µs`
  vs `off`, `645.2 KiB`). On `nonzero_field_relations_10` (`n = 10, m = 23`),
  `dominance` removes 0 variables, `elimination` removes only the 2 degree-2
  whiskers (`1024 → 256` states), and `relations` removes 4 variables
  (`1024 → 64` states), while `mixed_cheap` and `mixed_star` combine degree-2
  whisker elimination with 3 signed relation contractions to remove 5 variables
  (`1024 → 32` states, `−20976.09 µs` vs `off`, `21345.4 → 1367.8 KiB`).
- **Guarded degree-3 star–triangle (`zero_field_star_gadget_10`):**
  with `enable_star_triangle=false` (`mixed_cheap`), only the 2 degree-2 bridges
  are eliminated (`1024 → 256` states, `448` edge visits as `:relations` scans the
  surviving degree-3 stars). Enabling `enable_star_triangle=true` (`mixed_star`)
  eliminates the zero-field degree-3 stars before `:relations` runs, removing 5
  variables (`1024 → 32` states), reducing edge visits (`448 → 286`), median time
  (`6480.09 → 1670.45 µs`, `−53682.01 µs` vs `off`), and memory (`4793.6 → 1371.8 KiB`).
- **Dense frustrated control (`dense_no_reduction_8`):**
  on frustrated $K_8$ (`n = 8, m = 28`), no reduction applies in any pass
  (`256 → 256` states); `:relations` inspects all 56 directed pairs (`1176` edge
  visits, `84` exact fallbacks), increasing memory from `6041.8 KiB` to
  `7550.0 KiB` (`+1066.49 µs` vs `off` under `mixed_cheap`). Callers on dense
  instances can bound or disable `:relations` via `relation_work_budget`,
  `max_fill`, or `enable_relations=false`.
- **High dynamic range, degenerate optima, rollback/unfix, and gauge invariance
  (`high_dynamic_range_8`, `degenerate_optima_8`, `repeated_fix_unfix_8`,
  `gauge_equivalent_cascade_8`):**
  all four 8-variable stress fixtures reduce to `0` residual variables (`256 → 1`
  state) under `mixed_cheap` and `mixed_star` with identical work counts
  (`38/27/73` on `repeated_fix_unfix_8` and its gauge-transformed counterpart
  `gauge_equivalent_cascade_8`) and exact energy parity.

Raw artifact: [scheduler-pilot.tsv](scheduler-pilot.tsv)

SHA-256: `01ce2a169e11853781ff796b08a7285b69bdd88b40ce7597de4376330ddf2962`

Reproduce from a clean selected checkout:

```sh
OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/scheduler_pilot.jl > /tmp/scheduler-pilot.tsv
cp /tmp/scheduler-pilot.tsv docs/evidence/scheduler-pilot.tsv
```
