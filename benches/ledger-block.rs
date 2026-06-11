//! Phase-by-phase cost of private-transfer block processing.
//!
//! Drives the standalone [`zkpari::ledger`] pipeline — the chain's block
//! verification hot path — over BLS12-381 at several block sizes and reports
//! wall-clock per phase:
//!
//! - decode:  wire bytes -> transactions (5 validated uncompressed point
//!            reads per transfer: on-curve + subgroup, no sqrt)
//! - collect: theta transcripts + derived-tail claim assembly
//! - verify:  one RLC batch verification (MSMs + a 5-pairing product)
//! - apply:   commitment-chain checks + homomorphic updates
//!
//! Run with:
//!
//! ```sh
//! cargo bench --bench ledger-block            # release profile
//! ```

use ark_bls12_381::Bls12_381;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use std::time::Instant;
use zkpari::ledger::{decode_block, encode_block, Fixture, LedgerParams};

type E = Bls12_381;

const SIZES: &[usize] = &[64, 256, 512];
const ITERATIONS: usize = 5;

fn main() {
    let mut rng = StdRng::seed_from_u64(7);

    eprintln!("setup: keygen for the transfer relation...");
    let started = Instant::now();
    let params = LedgerParams::<E>::setup(&mut rng);
    eprintln!("setup done in {:?}\n", started.elapsed());

    println!(
        "{:>6}  {:>11} {:>11} {:>11} {:>11}  {:>11}  {:>8}  {:>9}",
        "txs", "decode_us", "collect_us", "verify_us", "apply_us", "total_us", "us/tx", "tx/s"
    );

    for &size in SIZES {
        // Median over a few iterations; each iteration processes the same
        // pre-built block against a fresh copy of the pre-block ledger.
        let mut fixture = Fixture::new(&params, size, 1_000);
        let pristine = fixture.ledger.clone();
        let block = fixture.transfer_block(3, true, &mut rng);
        let bytes = encode_block(&block);

        let mut decode_us = Vec::with_capacity(ITERATIONS);
        let mut collect_us = Vec::with_capacity(ITERATIONS);
        let mut verify_us = Vec::with_capacity(ITERATIONS);
        let mut apply_us = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let mut ledger = pristine.clone();

            let started = Instant::now();
            let decoded = decode_block::<E>(&bytes).expect("valid block bytes");
            decode_us.push(started.elapsed().as_micros());

            let timings = ledger
                .process_block_timed(&params, &decoded, &mut rng)
                .expect("valid block");
            collect_us.push(timings.collect_us);
            verify_us.push(timings.verify_us);
            apply_us.push(timings.apply_us);
        }

        let decode = median(&mut decode_us);
        let collect = median(&mut collect_us);
        let verify = median(&mut verify_us);
        let apply = median(&mut apply_us);
        let total = decode + collect + verify + apply;
        println!(
            "{:>6}  {:>11} {:>11} {:>11} {:>11}  {:>11}  {:>8.1}  {:>9.0}",
            size,
            decode,
            collect,
            verify,
            apply,
            total,
            total as f64 / size as f64,
            size as f64 / (total as f64 / 1e6),
        );
    }
}

fn median(samples: &mut [u128]) -> u128 {
    samples.sort_unstable();
    samples[samples.len() / 2]
}
