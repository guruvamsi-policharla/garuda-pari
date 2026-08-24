# Experiment 1 — ZK-Pari micro-benchmarks (BLS12-381)

Machine: Apple M5 Pro, 18 cores
Date: 2026-08-24
Commit: 822027b + working tree
Profile: `cargo bench` (release)
Threads: **single-threaded** (the default). Benches pin themselves to a
         1-thread rayon pool, which also governs arkworks' internal
         parallel iterators. Set `ZKPARI_BENCH_THREADS=0` for all cores,
         or `=N` for N.
Sampling: prove = median of 5 (2^10-2^14), 3 (2^16-2^18), 2 (2^20);
          verify/fs = mean over a >=100 ms budget loop;
          keygen = a single sample, so its scaling column carries noise.
Proof size: `proof B` counts elements, (2 + #blocks) G1 + 1 F. `wire B` is the
          CanonicalSerialize encoding, 8 bytes larger (a u64 length prefix on
          the c_ci vector, redundant since the vk fixes the block count).

## 1a. Prover cost vs circuit size (`cargo bench --bench prover`)

```
  size │ constraints │  domain │  keygen ms │   prove ms │ prove ns/cons │ verify us │ proof B
  ─────┼─────────────┼─────────┼────────────┼────────────┼───────────────┼───────────┼────────
  2^10 │        1024 │    1024 │       73.6 │       48.1 │       46973.7 │     823.6 │    176
  2^12 │        4096 │    4096 │      175.2 │      150.5 │       36737.7 │     829.5 │    176
  2^14 │       16384 │   16384 │      579.4 │      515.9 │       31485.4 │     839.6 │    176
  2^16 │       65536 │   65536 │     2190.8 │     1807.6 │       27581.8 │     821.7 │    176
  2^18 │      262144 │  262144 │     8079.4 │     6354.4 │       24240.2 │     827.7 │    176
  2^20 │     1048576 │ 1048576 │    31716.1 │    23423.9 │       22338.7 │     823.9 │    176

  Scaling factor per 4x circuit size (ideal linear = 4.00x)
  step          │ keygen │  prove
  ──────────────┼────────┼───────
  2^10 -> 2^12  │  2.38x │  3.13x
  2^12 -> 2^14  │  3.31x │  3.43x
  2^14 -> 2^16  │  3.78x │  3.50x
  2^16 -> 2^18  │  3.69x │  3.52x
  2^18 -> 2^20  │  3.93x │  3.69x

```

## 1b. Verifier cost vs committed-input blocks (`cargo bench --bench verifier`)

```
  blocks │ pairings │ verify us │   fs us │ algebra us │ proof B │ wire B │ prove ms
  ───────┼──────────┼───────────┼─────────┼────────────┼─────────┼────────┼─────────
       0 │        3 │     723.4 │     0.7 │      722.7 │     128 │    136 │   517.90
       1 │        4 │    1130.3 │     1.0 │     1129.3 │     176 │    184 │   522.52
       2 │        5 │    1098.2 │     1.2 │     1097.0 │     224 │    232 │   650.17
       4 │        7 │    1165.6 │     1.5 │     1164.1 │     320 │    328 │   525.13
       8 │       11 │    1635.3 │     2.3 │     1633.0 │     512 │    520 │   521.02
      16 │       19 │    2500.1 │     3.9 │     2496.2 │     896 │    904 │   521.89
      32 │       35 │    4214.2 │     6.8 │     4207.4 │    1664 │   1672 │   525.02
      64 │       67 │    7675.0 │    12.7 │     7662.3 │    3200 │   3208 │   529.95

  Marginal cost of each committed-input block (vs 0 blocks)
  blocks │ verify us │ d verify/block │ d algebra/block │ d fs/block
  ───────┼───────────┼────────────────┼─────────────────┼───────────
       1 │    1130.3 │         406.89 │          406.59 │       0.30
       2 │    1098.2 │         187.39 │          187.14 │       0.26
       4 │    1165.6 │         110.55 │          110.34 │       0.21
       8 │    1635.3 │         113.98 │          113.78 │       0.20
      16 │    2500.1 │         111.04 │          110.84 │       0.20
      32 │    4214.2 │         109.09 │          108.90 │       0.19
      64 │    7675.0 │         108.62 │          108.43 │       0.19

  Fiat-Shamir is now a rounding error: the verifying key is absorbed
  once at construction, so `fs us` only covers the per-proof material
  (public input, one c_ci per block, T) — a few us even at 64 blocks.
  Verification is now dominated by pairing algebra, which is what the
  (3 + #blocks) pairing count predicts. `algebra` is a *derived*
  difference of two separately timed loops, so it compounds both
  measurements' noise; read the trend, not the individual cells.

```
