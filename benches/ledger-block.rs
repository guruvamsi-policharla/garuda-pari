//! Phase-by-phase cost of private-transfer block processing.
//!
//! Drives the standalone [`zkpari::ledger`] pipeline — the chain's block
//! verification hot path — over BN254 at several block sizes and reports
//! wall-clock per phase:
//!
//! - decode: wire bytes -> transactions (6 validated uncompressed point
//!   reads per transfer: on-curve + subgroup, no sqrt)
//! - collect: two range-proof claims per transfer
//! - verify: one RLC batch verification (MSMs + a 4-pairing product)
//! - apply: commitment-chain checks + homomorphic updates
//!
//! Run with:
//!
//! ```sh
//! cargo bench --bench ledger-block            # release profile
//! ```

use ark_bn254::Bn254;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use std::time::Instant;
use zkpari::ledger::{decode_block, encode_block, Fixture, LedgerParams};

type E = Bn254;

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
        let mut challenge_us = Vec::with_capacity(ITERATIONS);
        let mut partitions = Vec::with_capacity(ITERATIONS);
        let mut lagrange_us = Vec::with_capacity(ITERATIONS);
        let mut instance_us = Vec::with_capacity(ITERATIONS);
        let mut sample_rhos_us = Vec::with_capacity(ITERATIONS);
        let mut small_msm_us = Vec::with_capacity(ITERATIONS);
        let mut c_msm_us = Vec::with_capacity(ITERATIONS);
        let mut t_msm_us = Vec::with_capacity(ITERATIONS);
        let mut u_msm_us = Vec::with_capacity(ITERATIONS);
        let mut full_msm_us = Vec::with_capacity(ITERATIONS);
        let mut scalar_accum_us = Vec::with_capacity(ITERATIONS);
        let mut last_left_us = Vec::with_capacity(ITERATIONS);
        let mut pairing_us = Vec::with_capacity(ITERATIONS);
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
            challenge_us.push(timings.verify_breakdown.challenge_us);
            partitions.push(timings.verify_breakdown.partitions as u128);
            lagrange_us.push(timings.verify_breakdown.lagrange_us);
            instance_us.push(timings.verify_breakdown.instance_us);
            sample_rhos_us.push(timings.verify_breakdown.sample_rhos_us);
            small_msm_us.push(timings.verify_breakdown.small_msm_us);
            c_msm_us.push(timings.verify_breakdown.c_msm_us);
            t_msm_us.push(timings.verify_breakdown.t_msm_us);
            u_msm_us.push(timings.verify_breakdown.u_msm_us);
            full_msm_us.push(timings.verify_breakdown.full_msm_us);
            scalar_accum_us.push(timings.verify_breakdown.scalar_accum_us);
            last_left_us.push(timings.verify_breakdown.last_left_us);
            pairing_us.push(timings.verify_breakdown.pairing_us);
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
        println!(
            "        verify: partitions={:>2} challenge={:>7} lagrange={:>7} instance={:>7} rhos={:>6} \
             msm128={:>7} (c={:>6} t={:>6} u={:>6}) msm_full={:>7} \
             scalars={:>6} last={:>6} pairing={:>7}",
            median(&mut partitions),
            median(&mut challenge_us),
            median(&mut lagrange_us),
            median(&mut instance_us),
            median(&mut sample_rhos_us),
            median(&mut small_msm_us),
            median(&mut c_msm_us),
            median(&mut t_msm_us),
            median(&mut u_msm_us),
            median(&mut full_msm_us),
            median(&mut scalar_accum_us),
            median(&mut last_left_us),
            median(&mut pairing_us),
        );
    }
}

fn median(samples: &mut [u128]) -> u128 {
    samples.sort_unstable();
    samples[samples.len() / 2]
}
