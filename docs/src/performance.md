# Measured operating envelope

On 2026-10-17, a bounded study accepted repeated sparse local/short-cascade reuse
for the first release. It does not establish that preprocessing benefits every
one-shot solve. The measured decomposition candidate keeps root preprocessing default off, and full certificate verification/export and detailed rollback reports
remain explicit operations.

The [shareable aggregate](assets/performance-envelope.json) contains all 440
paired cost summaries, all five differences per regime, workflow outcomes, source
revisions and machine/dependency metadata. It supports checking the table arithmetic.
The producing QUBOBenchmarks harness is private; this aggregate is not a claim that
public users can independently rerun that private source. The retained private
campaign includes raw archives, manifests, source hashes, failed preflights and
archive-member digests.

## Repeated boundary updates

Each comparison performs ten identical branch/propagate/rollback cycles. Reuse
pays for one cold construction and first-growth allocations; the baseline pays
for a fresh workspace and root propagation at each cycle. Both include returned
fixing data and trace construction/hashing; the recorded traces are checked for
equality outside timing. Five paired
deterministic trials alternate execution order; labels 41–45 are not backend RNG seeds.
Hot paths have discarded warmups. Detailed reports are disabled in this table.

Negative differences favor reuse. Allocation totals are cumulative bytes allocated,
not peak resident memory. The range is the observed paired range, not a population
confidence interval.

| Sparse workload | n | Median complete time difference (ms) | Paired range (ms) | Median allocation difference (MiB) |
|:--|--:|--:|:--|--:|
| local | 2,000 | -105.301 | -134.781 to -49.322 | -277.496 |
| local | 10,000 | -3689.948 | -4735.476 to -2405.385 | -6391.492 |
| short cascade | 2,000 | -112.136 | -125.885 to -99.962 | -279.002 |
| short cascade | 10,000 | -3741.479 | -3789.532 to -2759.845 | -6397.117 |

All five paired time and allocation differences in each required regime favored
reuse. Cold initialization is charged over exactly ten cycles. Recorded break-even
estimates use average measured cycle costs; they are not observed first-crossover
positions or guarantees for a different workload.

Median per-trial average warmed no-change allocation was 3,873.6 bytes per cycle
at n=10, 2,000 and
10,000, including harness trace/output overhead. Median per-trial average latency
was 7.1, 11.3 and 14.0 microseconds respectively. Separate CI guards check that
no-change/local structural and allocation work does not scan unrelated graph data.
Cold construction still scales with the graph. Dense degree, unavoidable cascades
and non-LIFO rebuild/replay retain their full costs in the aggregate; they are not
promised constant-time updates. Retained object size is measured outside timing
and is not peak RSS.

## Complete direct and decomposition workflows

The nine tiny fixtures use the same deterministic Rational exhaustive child,
zero start, capacity and shared work allowances across each off/on comparison.
Exact enumeration refuses more than eight compiled variables before exponentiation.
Each run has 256 available assignment units, including a final original-state audit,
and bounded structural work. Complete totals include construction/compilation,
loading, solve, lifting and final original audit; independent reference enumeration
and campaign/archive/export are recorded separately. Direct off uses identity
preprocessing through the same adapter and therefore includes adapter overhead.

All 180 outcomes were retained: 135 completed jobs and 45 failed/refused jobs.
Only successful incumbents enter statistical exports. A capacity refusal is not
a speedup. On the split fixture, default-off decomposition stops at its capacity
limit with an incumbent, while certified root reduction permits two small children
and an original optimum. On no-reduction, near-fallback, constant and other fixtures,
preprocessing can add cost; the aggregate retains those losses. Unsafe Float64
export is refused by the direct path, and decomposition can fall back to the
original objective when its budget permits. Approximate/local results retain
their qualified status.

## Evidence limits and choices

The study used Julia 1.10.11 and one Julia/OpenBLAS thread, an 8 GiB address-space
limit and a 600-second command limit. The full measurement took 320.474 seconds
and retained about 8.72 MB of output. The first preflight exposed an archive
restriction and projected excessive cost for 100 cycles; the protocol was amended
and committed to ten cycles before measurement. A second status-recording failure
and the successful third preflight remain separate historical attempts.

Producer revisions were QUBOPreprocessing
`3aa2923a4b5fe6cda21fbb4e331e9198b603029f` and QUBODecomposition
`1a08bfbd14bca1eff6d6f80326ea5cc270282cec`, with QUBODrivers 0.6.6,
QUBOTools 0.16.2 and ToQUBO 0.7.1. Source-pinned candidate evidence does not prove
General installation. The 0.1.0 runtime algorithm code matches the source used for this
envelope; later release/documentation changes require their own publication checks.

Boundary observations include ordinary interval bounds, forced exact fallback,
certificate production/verification, materialization and reconstruction. These
observations have no separate per-boundary discarded warmup and may include
first-call compilation. They are inclusive measurements, not steady-state isolated
phase costs. Full verification/export remains an explicit consumer boundary;
expensive automatic use on every hot update is deferred. Structural units omit
arithmetic bit complexity and hashing/sorting overhead; elapsed times include them.

Choose reuse for the measured repeated sparse regime, preserve cheap off/bounded
paths for one-shot callers, and measure a new consumer before changing its default.
No universal speed ratio or noisy timing threshold is enforced by CI.
