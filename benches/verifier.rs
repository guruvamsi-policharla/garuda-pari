//! Experiment 1b — verifier cost against the number of committed-input
//! blocks (BLS12-381).
//!
//! The circuit is held completely fixed: committed-input blocks are pure
//! *declarations* over witnesses the squaring chain already allocates, so
//! constraint count, domain size, instance length, and witness count are
//! identical across the whole sweep. Only the CRS changes — one extra
//! `delta_j` trapdoor, `Sigma_ci_j`, and `Gamma_ci_j` per block — so the
//! verify-time differences isolate exactly what we want.
//!
//! Verification is a `(3 + #blocks)`-pairing product plus a Fiat-Shamir
//! challenge. Both grow with the block count, and the table separates them:
//!
//!   - `fs us` replicates the challenge derivation (`compute_chall`) exactly.
//!     The verifying key is absorbed once when the key is built, so this only
//!     clones that state and absorbs the per-proof material: public input,
//!     one `c_ci` per block, and `T`. It is therefore O(#blocks) in the
//!     commitments alone, not in the key.
//!   - `algebra us` = `verify us` - `fs us` is the pairing/MSM cost, which is
//!     what the `(3 + #blocks)` pairing count predicts.
//!
//! `proof B` counts the proof's elements, `(2 + #blocks) G1 + 1 F`. `wire B`
//! is what `CanonicalSerialize` emits: 8 bytes more, a `u64` length prefix on
//! the `c_ci` vector that is redundant because the verifying key already fixes
//! the block count.
//!
//! Threads: single-threaded by default. Set `ZKPARI_BENCH_THREADS=0` for all
//! cores, or `=N` for N.
//!
//! Run with: cargo bench --bench verifier

mod common;

use ark_std::rand::{rngs::StdRng, SeedableRng};
use common::*;
use zkpari::{Proof, VerifyingKey, ZkPari};

const BLOCK_COUNTS: &[usize] = &[0, 1, 2, 4, 8, 16, 32, 64];

/// Circuit size held fixed across the sweep.
const LOG2_CONSTRAINTS: u32 = 14;

/// Re-derive the Fiat-Shamir challenge exactly as `verify` does, so we can
/// price the transcript separately from the pairing algebra. Mirrors
/// `zkpari::utils::compute_chall`, which is crate-private: clone the
/// transcript the verifying key already seeded with itself, then absorb only
/// the per-proof material.
fn fs_challenge(vk: &VerifyingKey<E>, public_input: &[Fr], proof: &Proof<E>) -> Fr {
    let mut t = vk.transcript().clone();
    let _ = t.append_serializable_element(b"input", &public_input.to_vec());
    for c in &proof.c_ci {
        let _ = t.append_serializable_element(b"comm_ci", c);
    }
    let _ = t.append_serializable_element(b"comm", &proof.t_g);
    t.get_and_append_challenge(b"r").unwrap()
}

struct Row {
    blocks: usize,
    verify_us: f64,
    fs_us: f64,
    prove_ms: f64,
    proof_bytes: usize,
    proof_wire_bytes: usize,
}

fn main() {
    in_bench_pool(run);
}

fn run() {
    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║  1b. ZK-Pari verifier cost vs committed-input blocks — BLS12-381     ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Threads: {}.", thread_label());
    println!("Circuit held fixed at 2^{LOG2_CONSTRAINTS} SR1CS constraints; blocks are declarations");
    println!("over witnesses that already exist, so only the CRS changes.");
    println!("Verification = (3 + #blocks) pairings + one Fiat-Shamir challenge.");
    println!();

    let mut rows = Vec::new();

    for &blocks in BLOCK_COUNTS {
        eprint!("  {blocks:>2} block(s) ...");
        let circuit = SquareChain::for_log2_constraints(LOG2_CONSTRAINTS, blocks, 3);
        let public_input = circuit.public_input();
        let mut rng = StdRng::seed_from_u64(20_260_824 + blocks as u64);

        let (pk, vk) = ZkPari::<E>::keygen(circuit, &mut rng);
        let mut proof = None;
        let prove_ms = median_ms(3, || {
            proof = Some(ZkPari::<E>::prove(circuit, &pk, &mut rng).expect("proving failed"));
        });
        let proof = proof.unwrap();
        assert!(
            ZkPari::<E>::verify(&proof, &vk, &public_input),
            "sanity verification failed at {blocks} blocks"
        );
        assert_eq!(
            proof.c_ci.len(),
            blocks,
            "proof should carry one commitment per block"
        );

        let verify_us = 1000.0
            * time_ms(150, 2000, || {
                std::hint::black_box(ZkPari::<E>::verify(&proof, &vk, &public_input));
            });
        let fs_us = 1000.0
            * time_ms(150, 2000, || {
                std::hint::black_box(fs_challenge(&vk, &public_input, &proof));
            });
        eprintln!(" done");

        rows.push(Row {
            blocks,
            verify_us,
            fs_us,
            prove_ms,
            proof_bytes: proof_element_bytes(&proof),
            proof_wire_bytes: compressed_size(&proof),
        });
    }

    println!();
    println!("  blocks │ pairings │ verify us │   fs us │ algebra us │ proof B │ wire B │ prove ms");
    println!("  ───────┼──────────┼───────────┼─────────┼────────────┼─────────┼────────┼─────────");
    for r in &rows {
        println!(
            "  {:>6} │ {:>8} │ {:>9.1} │ {:>7.1} │ {:>10.1} │ {:>7} │ {:>6} │ {:>8.2}",
            r.blocks,
            3 + r.blocks,
            r.verify_us,
            r.fs_us,
            r.verify_us - r.fs_us,
            r.proof_bytes,
            r.proof_wire_bytes,
            r.prove_ms,
        );
    }

    // Marginal cost per block, against the 0-block baseline.
    let base = &rows[0];
    println!();
    println!("  Marginal cost of each committed-input block (vs 0 blocks)");
    println!("  blocks │ verify us │ d verify/block │ d algebra/block │ d fs/block");
    println!("  ───────┼───────────┼────────────────┼─────────────────┼───────────");
    for r in rows.iter().skip(1) {
        let n = r.blocks as f64;
        println!(
            "  {:>6} │ {:>9.1} │ {:>14.2} │ {:>15.2} │ {:>10.2}",
            r.blocks,
            r.verify_us,
            (r.verify_us - base.verify_us) / n,
            ((r.verify_us - r.fs_us) - (base.verify_us - base.fs_us)) / n,
            (r.fs_us - base.fs_us) / n,
        );
    }
    println!();
    println!("  Fiat-Shamir is now a rounding error: the verifying key is absorbed");
    println!("  once at construction, so `fs us` only covers the per-proof material");
    println!("  (public input, one c_ci per block, T) — a few us even at 64 blocks.");
    println!("  Verification is now dominated by pairing algebra, which is what the");
    println!("  (3 + #blocks) pairing count predicts. `algebra` is a *derived*");
    println!("  difference of two separately timed loops, so it compounds both");
    println!("  measurements' noise; read the trend, not the individual cells.");
    println!();
}
