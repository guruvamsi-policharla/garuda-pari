//! Experiment 4 — multi-threaded batch-verification throughput (BLS12-381).
//!
//! Goal: 1,000,000 verifications per second on 8 threads.
//!
//! Deployment model: a validator with a backlog of proofs shards it across T
//! OS threads, each batch-verifying its own chunk inside a single-threaded
//! rayon pool ("sharded"). This parallelizes *everything* — Fiat-Shamir
//! challenges, Lagrange coefficients, rho sampling, MSMs, and the final
//! pairing — because the threads share nothing.
//!
//! The comparison mode hands one T-times-larger batch to a single
//! `batch_verify` call inside a T-thread rayon pool ("intra"). The library
//! parallelizes its per-proof phases (challenges, Lagrange coefficients,
//! instance evaluations) and its MSMs internally; only rho sampling and the
//! final scalar folds are sequential. The gap between the two columns is
//! that residual serial work plus rayon coordination overhead.
//!
//! Weak scaling: every thread always gets the same CHUNK of proofs, so
//! batch-size amortization is identical across rows and the table isolates
//! thread scaling. One extra row at 4x the chunk shows the remaining
//! amortization tail.
//!
//! 0 committed-input blocks throughout: the private-transfer circuits have
//! none (R_send/R_recv commit via in-circuit hashes), and blocks only add
//! per-proof MSM work. Circuit size is irrelevant to batch verification, so
//! the circuit is small and fixed.
//!
//! This bench manages its own thread pools; `ZKPARI_BENCH_THREADS` is ignored.
//!
//! Run with: cargo bench --bench throughput

mod common;

use ark_std::rand::{rngs::StdRng, SeedableRng};
use common::*;
use rayon::prelude::*;
use std::time::Instant;
use zkpari::{Proof, Trapdoor, VerifyingKey, ZkPari};

type Claim = (Proof<E>, Vec<Fr>);

/// Circuit size only affects keygen and the sanity proof, not batch cost.
const LOG2_CONSTRAINTS: u32 = 12;
/// Proofs per thread. Experiment 2 shows amortization is nearly flat past
/// this size (4096 -> 65536 gains 23%; the tail row below measures the rest).
const CHUNK: usize = 1 << 16;
/// The amortization-tail row: 8 threads at 4x the chunk.
const BIG_CHUNK: usize = 1 << 18;
const THREAD_COUNTS: &[usize] = &[1, 2, 4, 8];
const GOAL_PER_S: f64 = 1_000_000.0;
/// Samples per cell; the median absorbs the cold first pass.
const ITERS: usize = 3;

/// One simulated claim with no committed-input blocks. Fresh public input,
/// so every proof has its own Fiat-Shamir challenge.
fn simulated_claim(vk: &VerifyingKey<E>, td: &Trapdoor<E>, rng: &mut StdRng) -> Claim {
    use ark_std::UniformRand;
    let x = vec![Fr::rand(rng)];
    let proof = ZkPari::<E>::simulate(td, vk, &[], &x, rng);
    (proof, x)
}

/// Verify `threads` disjoint chunks on `threads` OS threads, one
/// single-threaded rayon pool each. Panics if any chunk fails.
fn sharded_pass(
    claims: &[Claim],
    vk: &VerifyingKey<E>,
    pools: &[rayon::ThreadPool],
    chunk: usize,
    seed: u64,
) {
    std::thread::scope(|s| {
        let handles: Vec<_> = pools
            .iter()
            .enumerate()
            .map(|(i, pool)| {
                let slice = &claims[i * chunk..(i + 1) * chunk];
                s.spawn(move || {
                    let mut rng = StdRng::seed_from_u64(seed ^ (0xD1CE << 8 | i as u64));
                    pool.install(|| ZkPari::<E>::batch_verify(slice, vk, &mut rng))
                })
            })
            .collect();
        for h in handles {
            assert!(h.join().unwrap(), "a shard failed to batch-verify");
        }
    });
}

/// One `batch_verify` over the whole slice inside a T-thread rayon pool.
fn intra_pass(claims: &[Claim], vk: &VerifyingKey<E>, pool: &rayon::ThreadPool, seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    assert!(
        pool.install(|| ZkPari::<E>::batch_verify(claims, vk, &mut rng)),
        "intra batch failed to verify"
    );
}

fn single_thread_pools(n: usize) -> Vec<rayon::ThreadPool> {
    (0..n)
        .map(|_| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(1)
                .build()
                .expect("failed to build a 1-thread pool")
        })
        .collect()
}

struct Cell {
    wall_ms: f64,
    proofs: usize,
}

impl Cell {
    fn per_s(&self) -> f64 {
        self.proofs as f64 / (self.wall_ms / 1000.0)
    }
    fn us_per_proof(&self) -> f64 {
        self.wall_ms * 1000.0 / self.proofs as f64
    }
}

fn main() {
    let all_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);
    let mut thread_counts: Vec<usize> = THREAD_COUNTS.to_vec();
    if all_threads > *THREAD_COUNTS.last().unwrap() {
        thread_counts.push(all_threads);
    }
    let max_threads = *thread_counts.last().unwrap();
    let pool_size = (max_threads * CHUNK).max(8 * BIG_CHUNK);

    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║  4. ZK-Pari multi-threaded batch-verification throughput — BLS12-381 ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Goal: {:.0}k proofs/s on 8 threads.", GOAL_PER_S / 1000.0);
    println!("Weak scaling: {CHUNK} proofs per thread, 0 committed-input blocks.");
    println!("Sampling: median of {ITERS} passes per cell.");
    println!();

    let mut rng = StdRng::seed_from_u64(20_260_826);
    let circuit = SquareChain::for_log2_constraints(LOG2_CONSTRAINTS, 0, 3);
    eprint!("keygen ...");
    let (pk, vk, td) = ZkPari::<E>::keygen_with_trapdoor(circuit, &mut rng);

    // Sanity: a genuine proof verifies under these keys.
    let real = ZkPari::<E>::prove(circuit, &pk, &mut rng).expect("proving failed");
    assert!(
        ZkPari::<E>::verify(&real, &vk, &circuit.public_input()),
        "real proof failed to verify"
    );

    eprint!(" simulating {pool_size} claims ...");
    let sim_start = Instant::now();
    let sim_pool = rayon::ThreadPoolBuilder::new()
        .build()
        .expect("failed to build the simulation pool");
    let claims: Vec<Claim> = sim_pool.install(|| {
        (0..pool_size)
            .into_par_iter()
            .map(|i| {
                let mut rng = StdRng::seed_from_u64(0x51_4D_00_00 + i as u64);
                simulated_claim(&vk, &td, &mut rng)
            })
            .collect()
    });
    drop(sim_pool);
    eprintln!(" done in {:.1}s", sim_start.elapsed().as_secs_f64());

    // Sanity: the pool batch-verifies at all.
    assert!(
        ZkPari::<E>::batch_verify(&claims[..CHUNK], &vk, &mut rng),
        "simulated pool failed to batch-verify"
    );

    // ---- Sweep ----
    let mut sharded: Vec<Cell> = Vec::new();
    let mut intra: Vec<Cell> = Vec::new();
    for &t in &thread_counts {
        eprint!("threads = {t}: sharded ...");
        let pools = single_thread_pools(t);
        let wall_ms = median_ms(ITERS, || {
            sharded_pass(&claims[..t * CHUNK], &vk, &pools, CHUNK, 7 + t as u64);
        });
        sharded.push(Cell { wall_ms, proofs: t * CHUNK });

        eprint!(" intra ...");
        let big_pool = rayon::ThreadPoolBuilder::new()
            .num_threads(t)
            .build()
            .expect("failed to build the intra pool");
        let wall_ms = median_ms(ITERS, || {
            intra_pass(&claims[..t * CHUNK], &vk, &big_pool, 11 + t as u64);
        });
        intra.push(Cell { wall_ms, proofs: t * CHUNK });
        eprintln!(" done");
    }

    // Amortization tail: 8 threads, 4x chunk.
    eprint!("threads = 8 at {BIG_CHUNK}/thread ...");
    let pools = single_thread_pools(8);
    let wall_ms = median_ms(ITERS, || {
        sharded_pass(&claims[..8 * BIG_CHUNK], &vk, &pools, BIG_CHUNK, 99);
    });
    let tail = Cell { wall_ms, proofs: 8 * BIG_CHUNK };
    eprintln!(" done");

    // ---- Report ----
    // Scaling efficiency: measured throughput over (1-thread throughput x T).
    let base = sharded[0].per_s();
    println!("\n4a. Throughput, {CHUNK} proofs per thread");
    println!("  threads │ ────────────── sharded ────────────── │ ──────── intra ────────");
    println!("          │  wall ms   us/proof   proofs/s    eff │  wall ms       proofs/s");
    println!("  ────────┼───────────────────────────────────────┼────────────────────────");
    for ((t, s), i) in thread_counts.iter().zip(&sharded).zip(&intra) {
        println!(
            "  {t:>7} │ {:>8.1} {:>10.2} {:>10.0} {:>5.2}x │ {:>8.1} {:>14.0}",
            s.wall_ms,
            s.us_per_proof(),
            s.per_s(),
            s.per_s() / (base * *t as f64),
            i.wall_ms,
            i.per_s(),
        );
    }
    println!(
        "\n4b. Amortization tail: 8 threads x {BIG_CHUNK} proofs = {:.1} ms, {:.2} us/proof, {:.0} proofs/s",
        tail.wall_ms,
        tail.us_per_proof(),
        tail.per_s()
    );

    let at8 = sharded
        .iter()
        .zip(&thread_counts)
        .find(|(_, &t)| t == 8)
        .map(|(c, _)| c.per_s().max(tail.per_s()))
        .unwrap_or(0.0);
    println!(
        "\nGoal: {:.0}k proofs/s on 8 threads — {} (best 8-thread figure: {:.0}k/s)",
        GOAL_PER_S / 1000.0,
        if at8 >= GOAL_PER_S { "MET" } else { "NOT MET" },
        at8 / 1000.0
    );
    println!();
}
