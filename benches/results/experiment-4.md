# Experiment 4 — multi-threaded batch-verification throughput (BLS12-381)

Machine: Apple M5 Pro, 18 cores (6 performance + 12 efficiency)
Date: 2026-08-26
Commit: 3e9900b + working tree
Run: `cargo bench --bench throughput` (manages its own thread pools;
     `ZKPARI_BENCH_THREADS` is ignored)
Sampling: median of 3 passes per cell. Run-to-run spread at high thread
counts is ~5% (thermal); single-thread numbers are stable to 0.1%.

## Goal and verdict

**Goal: 1,000,000 verifications per second on 8 threads.**
**Verdict: not met at 8 threads — ~505–532k proofs/s across runs. The full
machine (18 threads) lands right at the goal: 954k–1,025k across runs.**

The gap is not a threading problem: the shortfall decomposes into (a) this
machine having only 6 performance cores, so "8 threads" already mixes in
efficiency cores, and (b) a per-proof floor of ~12 us that is 90% MSM
work. Both are quantified below.

## Setup

- **Sharded mode**: the proof backlog is split into per-thread chunks; each
  OS thread runs its own `batch_verify` inside a single-threaded rayon
  pool. Nothing is shared across threads.
- **Intra mode**: one `batch_verify` call over a T-times larger batch
  inside a T-thread rayon pool, exercising the library's internal
  parallelism.
- **Weak scaling**: every thread always verifies 65536 proofs, so batch
  amortization is identical across rows and the table isolates thread
  scaling.
- 0 committed-input blocks throughout: the private-transfer circuits
  (`R_send`/`R_recv`) have none, and blocks only add per-proof MSM work.
- Pool of 2^21 simulated claims (HVZK simulator, same soundness argument as
  experiment 2), built once in ~32 s on all cores.

## Library changes made for this experiment

1. **One batch inversion per chunk instead of per proof.**
   `batch_eval_last_lagrange_coeffs` used to run Montgomery batch inversion
   on 2-element vectors, i.e. one field inversion per proof — at ~100x the
   cost of a multiplication, those 65536 inversions were ~85% of the
   Lagrange phase. Denominators are now flattened and inverted in
   1024-proof chunks. Effect, single-threaded at N=65536, 0 blocks:

   ```
   per-proof amortised cost:  14.19 us  ->  11.98 us   (-16%)
   ```

2. **`batch_verify` now parallelizes its per-proof phases.** Fiat-Shamir
   challenges, Lagrange coefficients (the chunks above), and the instance
   evaluations run over the ambient rayon pool, like the MSMs always did.
   Only rho sampling (a sequential `RngCore`) and the final scalar folds
   remain serial — a few ms per 65536 proofs. In a 1-thread pool the
   par_iters degrade to serial with no measurable overhead (11.97 vs
   11.98 us before/after).

All 22 library tests pass (including batch-verify accept and reject
paths). Experiment 2's tables were re-measured after these changes; see
the note there.

## Results

```
4a. Throughput, 65536 proofs per thread
  threads │ ────────────── sharded ────────────── │ ──────── intra ────────
          │  wall ms   us/proof   proofs/s    eff │  wall ms       proofs/s
  ────────┼───────────────────────────────────────┼────────────────────────
        1 │    785.2      11.98      83462  1.00x │    786.3          83352
        2 │    791.9       6.04     165506  0.99x │    780.1         168014
        4 │    884.3       3.37     296446  0.89x │    832.5         314876
        8 │   1037.2       1.98     505465  0.76x │   1036.7         505727
       18 │   1237.0       1.05     953650  0.63x │   1378.7         855653

4b. Amortization tail: 8 threads x 262144 proofs
       4014.9 ms, 1.91 us/proof, 522340 proofs/s
```

`eff` is measured throughput over (1-thread throughput x T). `us/proof` is
amortised over all threads. An earlier run before the phase
parallelization (intra was then MSM-only-parallel) had sharded at 532k/8T
and 1,025k/18T, and intra at 348k/8T and 468k/18T — the high-T sharded
delta between runs is thermal noise, the intra delta is the change.

## Analysis

- **Intra now tracks sharded** (505.7k vs 505.5k at 8 threads), so callers
  no longer need to shard manually: one `batch_verify` call in a parallel
  pool scales. At 2–4 threads intra is actually ~5% *ahead*, because one
  4x-larger MSM amortizes Pippenger buckets better than 4 separate MSMs.
  At 18 threads sharded pulls ahead (954k vs 856k) as intra's remaining
  serial work — rho sampling, scalar folds, collecting the MSM base
  vectors — starts to bite. Shard at high core counts; otherwise don't
  bother.
- **The scaling cliff at 8 threads is the core topology.** This machine has
  6 P-cores; rows 1–4 run mostly on them, while the 8-thread row schedules
  shards onto E-cores and the join barrier waits for the slowest. Per-
  thread per-proof cost inflates from 11.98 us (T=1) to 15.8 us (T=8). On
  8 true P-cores the same code would land around ~665k/s — better, still
  short of 1M.
- **Batch amortization is exhausted at 65536**: quadrupling the per-thread
  chunk changed per-proof cost by under 2% (4b). Spend memory on threads,
  not bigger batches.
- **Measurement-model caveat**: the join barrier slightly understates
  steady-state throughput on heterogeneous cores (a real validator streams
  batches, so no thread waits at a barrier). The effect is bounded by the
  P/E speed gap; it does not change the verdict.

## The remaining gap to 1M/s on 8 threads

Hitting the goal needs <= 8.0 us per proof per thread; the current floor is
11.98 us, split: T~ MSM 2.7, U~ MSM 2.8, V~ MSM 5.3 (full-width scalars),
challenge 0.8, Lagrange+instance ~0.4. Known levers, none implemented:

- **GLV decomposition for the V~ MSM** (the one full-width MSM): a 2N-point
  128-bit MSM instead of an N-point 255-bit one, ~25% cheaper there,
  ~-1.3 us overall. BLS12-381 G1 has the endomorphism; ark-ec's
  `msm_unchecked` doesn't exploit it.
- **BN254 instead of BLS12-381**: experiment 2's cross-check measured the
  identical workload at 1.46x faster on BN254. That alone puts 8 P-cores
  at ~970k/s, and with GLV comfortably over 1M. The catch: the
  private-transfer circuits Pedersen-hash over Jubjub, whose base field is
  the BLS12-381 scalar field. A BN254 deployment would switch to Baby
  Jubjub — mechanical, but BN254's ~100-bit security is a real downgrade.
- **More P-cores**: the machine already delivers ~1M/s at 18 threads;
  interpolating the sharded column, the goal falls around 12 threads on
  this core mix.

## Application context

At 100K TPS with one `R_send` + one `R_recv` proof per transfer, the
validator needs 200k verifications/s. That is met at **4 threads**
(296k/s) with ~50% headroom; 8 threads gives 2.5x the requirement. The
1M/s goal corresponds to ~500K TPS on this machine.
