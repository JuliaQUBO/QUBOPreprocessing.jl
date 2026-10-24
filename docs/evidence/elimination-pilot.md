# Degree-0/1/2 elimination pilot

This bounded smoke pilot addresses issue #15; it is not the accepted performance
or adoption envelope owned by QUBOBenchmarks #30. Five deterministic spin
minimization fixtures, five paired repetitions each, no randomness. CPU timings
and byte allocations are machine observations with no pass/fail speed threshold
or universal claim.

Producing commit: `ff61c25f09cae1a1944141e9fe102e76a9c5178f` (clean tree).
Julia 1.10.11, QUBOTools 0.16.3, Linux x86_64, CPU target sapphirerapids,
one Julia/OpenBLAS thread, 16 GiB cgroup memory cap (`MemorySwapMax=0`).
No child/model exceeds ten spin variables; oversized input is rejected before
exponentiation. The same exact scalar exhaustive spin child is used for both
modes. Workspace construction, `eliminate_low_degree!`, proof export and
independent `verify_certificate` verification, residual `materialize` and
`export_model`, child enumeration, `reconstruct` lifting and exact
original-energy audit are all included in `on` total time and allocations.
`off` sends the original model directly to the same child and charges state
copying and the same exact original-energy audit. Two warmups per fixture and
mode precede measurement; measured dispatch order alternates across repetitions.

| Case | Removed variables/edges | Enumerated states off → on | Median off/on µs | Median paired (on−off) µs | Median off/on KiB |
| :-- | --: | --: | --: | --: | --: |
| dense_k5 | 0 / 0 | 32 → 32 | 441.84 / 947.15 | +409.88 | 327.5 / 388.5 |
| whisker_5 | 1 / 1 | 32 → 16 | 460.29 / 1173.34 | +713.05 | 257.4 / 241.4 |
| whisker_7 | 3 / 3 | 128 → 16 | 2138.64 / 1359.81 | −642.35 | 1274.6 / 401.0 |
| whisker_10 | 6 / 6 | 1024 → 16 | 23469.22 / 2316.66 | −21152.56 | 13622.6 / 639.6 |
| cycle_8 | 8 / 8 | 256 → 1 | 4204.97 / 1817.25 | −2303.33 | 2491.8 / 593.4 |

Paired differences are computed per repetition before taking their median. All
twenty-five paired exact optimal energies agree. On `dense_k5`, `elim_queue`
is empty (`0` candidates examined, `0` edge visits), so the `+409.88 µs`
overhead comes from workspace construction and residual export. On `whisker_5`
(4-clique core plus 1 leaf), eliminating 1 variable halves the state count
(`32 → 16`), but exact table construction, proof verification and
materialization cost more than evaluating the 16 saved states directly
(`+713.05 µs`). End-to-end break-even against this exact-enumeration child is
crossed by `whisker_7` (3 eliminated variables, `128 → 16` states, `−642.35 µs`,
`1274.6 → 401.0 KiB`), and `whisker_10` (6 eliminated variables, `1024 → 16`
states) reduces median total time from `23469.22 µs` to `2316.66 µs`
(`−21152.56 µs`, `13622.6 → 639.6 KiB`). On `cycle_8`, strict dominance removes
0 variables while degree-`<= 2` elimination solves the model completely
(`256 → 1` state, `−2303.33 µs`).

Raw artifact: [elimination-pilot.tsv](elimination-pilot.tsv)

SHA-256: `245933c6dd8b01bc49add8906fd972a80c7d5ddc06a355b2adba3a6a98a1ab5e`

Reproduce from a clean selected checkout:

```sh
OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/elimination_pilot.jl > pilot.tsv
```
