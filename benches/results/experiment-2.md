# Experiment 2 — batch vs individual verification (BLS12-381)

Machine: Apple M5 Pro, 18 cores
Date: 2026-08-24
Commit: 822027b + working tree
Profile: `cargo bench --bench batch_verify` (release)
Threads: **single-threaded** (the default). Set `ZKPARI_BENCH_THREADS=0` for
         all cores, or `=N` for N.
Circuit:  2^12 SR1CS constraints (batch cost is independent of circuit size).
Sampling: mean over a >=150 ms budget loop.

## Cross-check against the batch-pari reference

The [batch-pari benchmark](https://github.com/guruvamsi-policharla/zk-pari/pull/1)
reports, on an M5 MacBook Pro with `RAYON_NUM_THREADS=1` and **BN254**:
individual 584.5 us/proof, batch 644.5 ms at N=65536 = **9.83 us/proof**, 59.4x.

Running *this* implementation with 0 committed-input blocks — which reduces it
to the same three G1 MSMs (T, U, r*U) that reference measures — on both curves:

```
ZK-Pari, 0 committed blocks, N=65536, single-threaded
  BN254        individual    432.5 us/proof   batch(N=65536)     641.2 ms  =   9.78 us/proof   speedup  44.2x
  BLS12-381    individual    735.4 us/proof   batch(N=65536)     939.0 ms  =  14.33 us/proof   speedup  51.3x
```

On the same curve the numbers match: **641.2 ms vs the reference's 644.5 ms**
(0.5% apart), 9.78 vs 9.83 us/proof. There is no gap to explain. BLS12-381
costs 1.46x more than BN254 for identical work, which is the whole difference.

Two things worth noting for write-up:

- Our *individual* verification is faster than the reference's (432.5 vs 584.5
  us on BN254). That makes our **speedup ratio lower** (44.2x vs 59.4x) while
  the absolute per-proof cost is the same. Speedup-over-individual flatters a
  slow baseline; quote absolute us/proof as the primary figure.
- The reference sets `delta_1 = 1` (its note on Fig 6 step 4), dropping a term
  from the final multi-pairing. We keep delta_1 random and add a per-block
  delta_j, so at >0 blocks we are structurally doing more pairing work.

## Methodology: simulated proof pool

Timing 65536 proofs per block count would be dominated by *proving*, so the
pool is built with `ZkPari::simulate` (documented for verifier benchmarking and
load generation).

This is sound without needing to be checked empirically. The scheme is
statistically honest-verifier zero knowledge, so simulated and real proofs are
drawn from distributions at statistical distance at most `1/(q - m)` — around
`2^-255` here — and verification performs the same value-independent sequence
of MSMs and pairings over either. Their verification costs are identical by
construction, not by coincidence.

(An earlier version of this bench measured a real batch against a simulated one
on every run. It reported differences of 0.0%, -0.1%, and -0.3% across runs,
i.e. exactly the predicted result, and was removed as redundant.)

A genuine proof is still generated and verified at every block count, so the
keys under test are exercised by real proving.

```
Per-proof cost of individual verification
  blocks │ pairings │ verify us
  ───────┼──────────┼──────────
       0 │        3 │     732.9
       1 │        4 │     856.8
       2 │        5 │    1031.5
       4 │        7 │    1199.4

2a. Amortised batch cost per proof (us)
  blocks │         N=1       N=256      N=4096     N=65536
  ───────┼────────────────────────────────────────────────
       0 │      747.34       32.72       18.38       14.19
       1 │      841.03       39.41       22.30       17.15
       2 │     1051.93       47.40       26.85       20.60
       4 │     1191.92       63.52       34.69       26.44

2b. Where the time goes at N=65536 (ms)
  Phases are re-executed against the public API — the library carries no
  instrumentation — and their total is checked against `batch_verify`.
  blocks │ challenge │ lagrange │ instance │   C~ MSM │   T~ MSM │   U~ MSM │   V~ MSM │ pairing │    sum │ measured
  ───────┼───────────┼──────────┼──────────┼──────────┼──────────┼──────────┼──────────┼─────────┼────────┼─────────
       0 │      51.0 │    166.4 │      2.7 │      0.0 │    177.4 │    180.7 │    345.8 │    0.60 │  924.7 │    929.9
       1 │      67.5 │    164.7 │      2.6 │    176.6 │    176.1 │    178.1 │    346.5 │    0.69 │ 1112.7 │   1124.2
       2 │      78.7 │    171.0 │      2.9 │    357.0 │    180.9 │    177.3 │    355.0 │    0.87 │ 1323.7 │   1350.4
       4 │     105.3 │    161.0 │      2.7 │    716.5 │    177.7 │    178.3 │    349.1 │    1.07 │ 1691.7 │   1732.5

  C~ MSM is the only column that scales with the block count: one
  MSM over all N proofs per committed-input block. T~/U~ are the same
  MSM over T and U; V~ is the same again but with full-width scalars
  (rho_k * r^(k) rather than the 128-bit rho_k). The final pairing
  product is a fixed per-batch cost, which is what amortises away.
```
