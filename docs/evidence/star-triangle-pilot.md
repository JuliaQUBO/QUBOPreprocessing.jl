# Guarded zero-field degree-3 star–triangle pilot

This bounded smoke pilot addresses issue #17; it is not the accepted performance
or adoption envelope owned by QUBOBenchmarks #30. Six deterministic spin
minimization fixtures (`zero_field_k4`, `zero_field_wheel_w6`,
`zero_field_subdivided_10`, `conditioned_invalidated_8`,
`conditioned_unlocked_8`, and `no_benefit_cubic_8`), five paired repetitions
each across `off`, `deg2` (`max_degree=2`), and `deg3` (`max_degree=3`), no
randomness. CPU timings and byte allocations are machine observations with no
pass/fail speed threshold or universal claim.

Producing commit: `7d3757a3e9b9779dcbe9decd9fd80a8978741625` (branch `feat/issue-17-star-triangle`, base `cf542b202c7e9d68474db68456e95c0977aaf818`).
Julia 1.10.11, QUBOTools 0.16.3, Linux x86_64, CPU target sapphirerapids,
one Julia/OpenBLAS thread, 16 GiB cgroup memory cap (`MemorySwapMax=0`).
No child/model exceeds ten spin variables; oversized input is rejected before
exponentiation. The same exact scalar exhaustive spin child is used for all
three modes. Workspace construction, `eliminate_low_degree!`, proof export and
independent `verify_certificate` verification, residual `materialize` and
`export_model`, child enumeration, `reconstruct` lifting and exact
original-energy audit are all included in `deg2` and `deg3` total time and
allocations. `off` sends the original model directly to the same child and
charges state copying and the same exact original-energy audit. Two warmups per
fixture and mode precede measurement; measured dispatch order alternates across
repetitions.

| Case | Removed (`deg2` / `deg3`) | Work `cand/edge/exact` (`deg2` → `deg3`) | States (`off` → `deg2` → `deg3`) | Median `off` / `deg2` / `deg3` µs | Median paired (`deg3−off` / `deg3−deg2`) µs | Median `off` / `deg2` / `deg3` KiB |
| :-- | --: | --: | --: | --: | --: | --: |
| `zero_field_k4` | 0 / 4 | `0/0/0` → `10/20/37` | 16 → 16 → 1 | 311.30 / 489.60 / 1986.03 | +1707.74 / +667.38 | 107.8 / 171.5 / 353.1 |
| `zero_field_wheel_w6` | 0 / 2 | `0/0/0` → `6/24/36` | 64 → 64 → 16 | 2231.72 / 2695.32 / 2166.74 | +687.00 / −552.97 | 644.6 / 729.0 / 494.1 |
| `zero_field_subdivided_10` | 2 / 5 | `2/12/22` → `6/46/76` | 1024 → 256 → 32 | 135996.61 / 10192.32 / 2173.07 | −133860.71 / −7903.97 | 17285.3 / 4215.2 / 1020.6 |
| `conditioned_invalidated_8` | 1 / 1 | `10/1/13` → `12/1/13` | 256 → 128 → 128 | 6412.80 / 3759.53 / 3678.54 | −3007.87 / −754.54 | 3355.3 / 1900.0 / 1900.1 |
| `conditioned_unlocked_8` | 1 / 4 | `10/1/13` → `26/37/76` | 256 → 128 → 16 | 7629.47 / 4635.77 / 1958.97 | −5938.87 / −2799.52 | 3480.3 / 1901.1 / 660.6 |
| `no_benefit_cubic_8` | 0 / 0 | `0/0/0` → `8/0/0` | 256 → 256 → 256 | 3419.65 / 4513.22 / 6173.81 | +3302.21 / +926.23 | 3192.1 / 3287.0 / 3287.7 |

Paired differences are computed per repetition before taking their median. All
thirty paired exact optimal energies agree across `off`, `deg2` and `deg3`:
- **Zero-field instances (`zero_field_k4`, `zero_field_wheel_w6`, `zero_field_subdivided_10`):**
  on `zero_field_k4` (`n = 4`), `deg3` eliminates vertex 1 (`actual_fill == 0`)
  and cascades vertices 2–4 (`16 → 1` state), but on 16 states the 8-state
  `Rational{BigInt}` table certification and proof verification cost more than
  direct enumeration (`+1707.74 µs` vs `off`). On `zero_field_wheel_w6` (`n = 6`),
  `deg3` removes 2 zero-field degree-3 vertices (`64 → 16` states) and beats
  `deg2` (`−552.97 µs`, `729.0 → 494.1 KiB`). On `zero_field_subdivided_10`
  (`n = 10`), `deg2` removes only the 2 degree-2 bridges (`1024 → 256` states),
  whereas `deg3` also eliminates the zero-field degree-3 stars (`1024 → 32`
  states), reducing median total time to `2173.07 µs` (`−133860.71 µs` vs `off`,
  `−7903.97 µs` vs `deg2`, `4215.2 → 1020.6 KiB`).
- **Conditioned-field instances (`conditioned_invalidated_8`, `conditioned_unlocked_8`):**
  when leaf 8 (`s_8 = +1`) is fixed by unary dominance (`cascade_dominance=true`),
  hub 5 drops from degree 4 to degree 3. In `conditioned_invalidated_8`, the
  induced shift creates a nonzero center field `h_5 = +1.0 != 0`, which `deg3`
  rejects in `O(1)` via the cached exact Ising field with `0` additional edge
  visits and `0` additional exact table work (`12/1/13` vs `10/1/13`). In
  `conditioned_unlocked_8`, the induced shift cancels the initial field
  `h_5 = -1.0` to `0.0`, unlocking star–triangle elimination on hub 5 and
  cascading zero-field hubs 6 and 7 (`1 → 4` variables removed, `128 → 16`
  states, `−2799.52 µs` vs `deg2`, `1901.1 → 660.6 KiB`).
- **No-benefit control (`no_benefit_cubic_8`):** on a 3-regular cube where all 8
  degree-3 vertices have nonzero fields, `deg3` pops all 8 candidates from
  `elim_queues[4]` and rejects each in `O(1)` with `0` edge visits and `0`
  exact table evaluations (`8/0/0` work, `256 → 256` states, `+926.23 µs` vs
  `deg2`). Consequently, `max_degree=2` remains the default policy and
  `max_degree=3` is opt-in.

Raw artifact: [star-triangle-pilot.tsv](star-triangle-pilot.tsv)

SHA-256: `759dfcc2fb2ed89e67c3583f635d36b2db142201fd663c37b4795f65a487a93e`

Reproduce from a clean selected checkout:

```sh
OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/star_triangle_pilot.jl > /tmp/star-triangle-pilot.tsv
cp /tmp/star-triangle-pilot.tsv docs/evidence/star-triangle-pilot.tsv
```

