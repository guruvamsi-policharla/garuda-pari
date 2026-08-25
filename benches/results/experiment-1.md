# Experiment 1a — prover cost vs circuit size (BLS12-381)

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
Proof size: `proof B` counts elements, (2 + #blocks) G1 + 1 F. The
          CanonicalSerialize encoding is 8 bytes larger (a u64 length prefix on
          the c_ci vector, redundant since the vk fixes the block count).

Experiment 1b (verifier cost vs committed-input blocks) was dropped: it is not
going in the paper, and per-block verifier cost is visible in experiment 2's
individual-verification column anyway.

## Results (`cargo bench --bench prover`)

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
