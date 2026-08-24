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
       0 │        3 │     777.8
       1 │        4 │     869.5
       2 │        5 │    1043.3
       4 │        7 │    1224.0
       8 │       11 │    2437.3
      16 │       19 │    2794.0

2a. Amortised batch cost per proof (us)
  blocks │         N=1        N=16       N=256      N=4096     N=65536
  ───────┼────────────────────────────────────────────────────────────
       0 │      753.57      119.07       32.70       18.57       14.17
       1 │      850.06      141.95       40.00       23.04       17.28
       2 │     1018.33      170.25       47.57       26.79       20.09
       4 │     1240.27      221.65       61.64       34.80       26.12
       8 │     2423.47      439.45      128.08       71.66       40.39
      16 │     2588.99      598.12      210.40      106.78       61.99

2a. Speedup over verifying one by one (N x individual / batch)
  blocks │         N=1        N=16       N=256      N=4096     N=65536
  ───────┼────────────────────────────────────────────────────────────
       0 │        1.0x        6.5x       23.8x       41.9x       54.9x
       1 │        1.0x        6.1x       21.7x       37.7x       50.3x
       2 │        1.0x        6.1x       21.9x       38.9x       51.9x
       4 │        1.0x        5.5x       19.9x       35.2x       46.9x
       8 │        1.0x        5.5x       19.0x       34.0x       60.3x
      16 │        1.1x        4.7x       13.3x       26.2x       45.1x

Batch verification — total wall clock (ms)
  blocks │         N=1        N=16       N=256      N=4096     N=65536
  ───────┼────────────────────────────────────────────────────────────
       0 │        0.75        1.91        8.37       76.04      928.70
       1 │        0.85        2.27       10.24       94.39     1132.28
       2 │        1.02        2.72       12.18      109.74     1316.64
       4 │        1.24        3.55       15.78      142.55     1711.91
       8 │        2.42        7.03       32.79      293.53     2647.23
      16 │        2.59        9.57       53.86      437.35     4062.29

2b. Where the time goes at N=65536 (us, from batch_verify_timed)
  blocks │ challenge │ lagrange │ instance │   C~ MSM │   T~ MSM │   U~ MSM │   V~ MSM │  pairing
  ───────┼───────────┼──────────┼──────────┼──────────┼──────────┼──────────┼──────────┼─────────
       0 │     42707 │   161488 │     4655 │        0 │   178623 │   178663 │   352428 │      708
       1 │     60470 │   166875 │     4737 │   180835 │   180532 │   181036 │   354882 │      809
       2 │     70175 │   161355 │     4730 │   360225 │   179243 │   179320 │   352883 │      982
       4 │     97696 │   165863 │     4560 │   723341 │   179295 │   179726 │   348089 │     1152
       8 │    153974 │   171729 │     4837 │  1516100 │   189161 │   184940 │   413564 │     2435
      16 │    244951 │   170196 │     4882 │  2915356 │   175998 │   178945 │   352432 │     2557

  C~ MSM is the only column that scales with the block count: one
  MSM over all N proofs per committed-input block. T~/U~ are the same
  MSM over T and U; V~ is the same again but with full-width scalars
  (rho_k * r^(k) rather than the 128-bit rho_k). The final pairing
  product is a fixed per-batch cost, which is what amortises away.

```

## Remaining hot spots (single-threaded, N=65536, 0 blocks)

From the 2b breakdown, of ~929 ms total:

| term | cost | note |
|---|---|---|
| `V~` MSM | 352 ms (38%) | full-width scalars (rho_k * r^(k)); 2x the 128-bit MSMs |
| `T~`/`U~` MSMs | 179 ms each | 128-bit scalars |
| `lagrange` | 161 ms (17%) | `batch_inversion_and_mul` is explicitly single-threaded |
| `challenge` | 43 ms | per-proof transcript absorption |
| pairing | 0.7 ms | one multi-pairing, fully amortised |

`lagrange` is the clearest remaining target: it is 17% of batch time and is
sequential even in a parallel run.
