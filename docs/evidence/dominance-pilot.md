# Strict-dominance pilot

This bounded smoke pilot addresses issue #4; it is not the accepted performance
or adoption envelope owned by QUBOBenchmarks #30. Four hand-selected binary
minimization fixtures, five paired repetitions each, no randomness. CPU timings
are machine observations with no pass/fail speed threshold or universal claim.

Producing commit: `b43db34d3f1c0fa24cf306f957ac67abd1fc0c8a` (clean tree).
Julia 1.10.11, QUBOTools 0.16.2, Linux x86_64, CPU target sapphirerapids,
one Julia/OpenBLAS thread, 8 GiB process address-space cap, 300 s process timeout.
No child/model exceeds eight binary variables; oversized input is rejected
before exponentiation. The same exact scalar exhaustive child is used for both
modes. Construction, propagation, proof export/verification, materialization,
solver-model copying, child enumeration, reconstruction and exact original-energy
audit are included in `on` total. `off` sends the original model directly to the
same child and charges state copying and the same audit. Source fixture creation
and the cross-mode optimum comparison are outside both totals. Per-phase durations
are retained for each row; outer total includes timing/call overhead. Two warmups
per fixture and mode precede measurement; measured dispatch order alternates.

| Case | Removed variables/edges | Enumerated states off → on | Median off/on µs | Median paired (on−off) µs |
| :-- | --: | --: | --: | --: |
| cascade | 2 / 1 | 16 → 4 | 63.84 / 248.82 | +191.99 |
| all_fixed | 8 / 0 | 256 → 1 | 729.25 / 293.31 | −486.62 |
| tie_chain | 0 / 0 | 256 → 256 | 947.38 / 1024.80 | +77.41 |
| small_no_reduction | 0 / 0 | 4 → 4 | 10.55 / 51.17 | +41.77 |

Paired differences are computed before taking their median. The phase costs,
reductions, states and energies remain paired by case/repetition in the raw TSV.
All twenty paired exact optimal energies agree. The all-fixed case pays for
preprocessing here; the cascade removes half its variables but is slower overall.
Both no-reduction controls incur overhead. This small, warm exact-enumeration
child cannot establish behavior for production solvers or larger instances.

Attempt ledger: attempt 1 at `7236f84` stopped before any measurement because the
pilot used an unsupported Julia 1.10 `Cmd` keyword form. Attempt 2 at the producing
commit corrected command construction and completed all forty mode rows. No
failed timing rows were pooled into the successful campaign. The source library
was unchanged between these attempts.

Raw artifact: [dominance-pilot.tsv](dominance-pilot.tsv)

SHA-256: `4ce818f2fc069af07805e0fedd169444bacf6606a05b91081d24a5e6b6d94032`

Reproduce from a clean selected checkout:

```sh
OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/dominance_pilot.jl > pilot.tsv
```

Timings need not reproduce byte-for-byte. To audit this retained table, parse TSV
rows after the two metadata lines, require exactly the Cartesian product of four
cases × repetitions 1:5 × modes on/off, compare paired `energy`, then compute
`median(on.total-off.total)*1e6` per case. Do not subtract mode medians to obtain
the paired statistic.
