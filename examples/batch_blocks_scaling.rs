//! Batch-verification scaling in the number of committed-input blocks.
//!
//! A dummy circuit — plain multiplications — parameterised by how many
//! committed-input blocks it declares, each block holding exactly one element.
//! We then sweep (number of blocks) x (number of proofs batched) and time
//! `ZkPari::batch_verify` against verifying the same proofs one by one.
//!
//! What the sweep is expected to show, from `src/batch_verify.rs`:
//!   - Each extra block adds one 128-bit MSM over the N proofs (`C~_j`) and
//!     one more pairing to the final multi-pairing, so cost grows roughly
//!     linearly in the block count.
//!   - Batch cost per proof falls sharply with N, because the single
//!     (3 + #blocks)-pairing check is amortised over the whole batch.
//!   - Batch-verification cost is independent of *circuit size*, so the
//!     circuit here is deliberately tiny.
//!
//! Wall-clock is dominated by *proving* the pool, not by the measurements:
//! `BLOCK_COUNTS.len() * max(PROOF_COUNTS)` proofs at a few ms each.
//!
//! Run with: cargo run --release --example batch_blocks_scaling

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError, Variable};
use ark_relations::lc;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use std::io::Write;
use std::time::Instant;
use zkpari::{Proof, ZkPari, ZkPariCircuit};

type E = Bls12_381;
type Fr = <E as Pairing>::ScalarField;

const BLOCK_COUNTS: &[usize] = &[1, 2];
const PROOF_COUNTS: &[usize] = &[1 << 10, 1 << 12, 1 << 14, 1 << 16];

/// Minimum wall-clock to spend on each measurement, and a cap on repetitions.
const MIN_SAMPLE_MS: u128 = 150;
const MAX_REPS: usize = 500;

// ---------------------------------------------------------------------------
// Dummy circuit: `num_blocks` multiplications, one committed input each
// ---------------------------------------------------------------------------

/// `num_blocks` independent multiplications `x_j * y_j = p_j`, each declaring
/// its left factor `x_j` as a committed-input block of exactly one element,
/// plus one multiplication `a * b = c` whose product `c` is the sole public
/// input.
///
/// The public part is deliberately independent of `num_blocks`, so the
/// instance length stays at 2 (`[1, c]`) across the whole sweep. The
/// verifier's Lagrange work is therefore constant and does not confound the
/// block scaling we are trying to measure.
///
/// Constraints are written as R1CS and converted by `Sr1csAdapter`, which
/// renumbers the witness space — so this also exercises the committed-input
/// remapping on the conversion path.
#[derive(Clone, Copy)]
struct MulBlocks {
    num_blocks: usize,
    /// Selects the witness values, so distinct seeds give distinct proofs.
    seed: u64,
}

impl MulBlocks {
    /// The public input the verifier is given: `[c]`, matching the `a * b = c`
    /// constraint in `synthesize` below.
    fn public_input(seed: u64) -> Vec<Fr> {
        vec![Fr::from(seed + 7) * Fr::from(3u64)]
    }
}

impl ZkPariCircuit<Fr> for MulBlocks {
    fn synthesize(self, cs: ConstraintSystemRef<Fr>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        let seed = self.seed;

        // Public multiplication: a * b = c, with c the only public input.
        let (av, bv) = (Fr::from(seed + 7), Fr::from(3u64));
        let a = cs.new_witness_variable(|| Ok(av))?;
        let b = cs.new_witness_variable(|| Ok(bv))?;
        let c = cs.new_input_variable(|| Ok(av * bv))?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;

        // One committed-input block per multiplication x_j * y_j = p_j.
        (0..self.num_blocks)
            .map(|j| {
                let (xv, yv) = (Fr::from(seed + j as u64 + 1), Fr::from(2 * (j as u64 + 1)));
                let x = cs.new_witness_variable(|| Ok(xv))?;
                let y = cs.new_witness_variable(|| Ok(yv))?;
                let p = cs.new_witness_variable(|| Ok(xv * yv))?;
                cs.enforce_r1cs_constraint(|| lc!() + x, || lc!() + y, || lc!() + p)?;
                // Block j commits to exactly one element: the left factor.
                Ok(vec![x])
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Measurement
// ---------------------------------------------------------------------------

/// Run `f` repeatedly for at least `MIN_SAMPLE_MS`, returning the mean
/// milliseconds per call. Panics if any call reports failure.
fn time_ms(mut f: impl FnMut() -> bool) -> f64 {
    assert!(f(), "verification failed during warm-up");
    let start = Instant::now();
    let mut reps = 0usize;
    loop {
        assert!(f(), "verification failed during timing");
        reps += 1;
        if start.elapsed().as_millis() >= MIN_SAMPLE_MS || reps >= MAX_REPS {
            break;
        }
    }
    start.elapsed().as_secs_f64() * 1000.0 / reps as f64
}

struct Row {
    blocks: usize,
    num_constraints: usize,
    /// Mean ms for one single-proof `verify`.
    single_ms: f64,
    /// Mean ms for `batch_verify`, indexed like `PROOF_COUNTS`.
    batch_ms: Vec<f64>,
}

/// Build the CRS and a pool of `max_proofs` distinct proofs, then measure.
fn measure(blocks: usize, max_proofs: usize) -> Row {
    print!("  building {blocks:>2} block(s): keygen ...");
    std::io::stdout().flush().ok();

    let mut rng = StdRng::seed_from_u64(20_260_824 + blocks as u64);
    let started = Instant::now();
    let (pk, vk) = ZkPari::<E>::keygen(
        MulBlocks {
            num_blocks: blocks,
            seed: 1,
        },
        &mut rng,
    );
    print!(
        " {:.0} ms, proving {max_proofs} ...",
        started.elapsed().as_secs_f64() * 1000.0
    );
    std::io::stdout().flush().ok();

    let started = Instant::now();
    let pool: Vec<(Proof<E>, Vec<Fr>)> = (0..max_proofs)
        .map(|i| {
            let seed = i as u64 + 1;
            let circuit = MulBlocks {
                num_blocks: blocks,
                seed,
            };
            let proof = ZkPari::<E>::prove(circuit, &pk, &mut rng).expect("proving failed");
            (proof, MulBlocks::public_input(seed))
        })
        .collect();
    let prove_ms = started.elapsed().as_secs_f64() * 1000.0;
    println!(
        " {prove_ms:.0} ms ({:.2} ms/proof)",
        prove_ms / max_proofs as f64
    );

    // Sanity: every proof must verify on its own, and the batch must accept.
    for (proof, input) in &pool {
        assert!(
            ZkPari::<E>::verify(proof, &vk, input),
            "individual verification failed for {blocks} blocks"
        );
    }
    assert!(
        ZkPari::<E>::batch_verify(&pool, &vk, &mut rng),
        "batch verification failed for {blocks} blocks"
    );

    let (p0, x0) = &pool[0];
    let single_ms = time_ms(|| ZkPari::<E>::verify(p0, &vk, x0));
    let batch_ms = PROOF_COUNTS
        .iter()
        .map(|&n| time_ms(|| ZkPari::<E>::batch_verify(&pool[..n], &vk, &mut rng)))
        .collect();
    Row {
        blocks,
        num_constraints: vk.succinct_index.num_constraints,
        single_ms,
        batch_ms,
    }
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

/// Print a `blocks x PROOF_COUNTS` table. `cell` renders one entry from the
/// row, its batch time in ms, and the batch size.
fn print_grid(title: &str, rows: &[Row], cell: impl Fn(&Row, f64, usize) -> String) {
    println!("\n{title}");
    print!("  blocks │");
    for n in PROOF_COUNTS {
        print!(" {:>10}", format!("N={n}"));
    }
    print!("\n  ───────┼");
    for _ in PROOF_COUNTS {
        print!("───────────");
    }
    println!();
    for r in rows {
        print!("  {:>6} │", r.blocks);
        for (&ms, &n) in r.batch_ms.iter().zip(PROOF_COUNTS) {
            print!(" {:>10}", cell(r, ms, n));
        }
        println!();
    }
}

fn print_report(rows: &[Row], max_proofs: usize) {
    println!("\nCircuit shape");
    println!("  blocks │ SR1CS constraints │ proof size │ pairings │ 1 verify");
    println!("  ───────┼───────────────────┼────────────┼──────────┼──────────");
    for r in rows {
        println!(
            "  {:>6} │ {:>17} │ {:>7} B  │ {:>8} │ {:>6.3} ms",
            r.blocks,
            r.num_constraints,
            // (2 + blocks) G1 compressed + 1 Fr
            (2 + r.blocks) * 48 + 32,
            3 + r.blocks,
            r.single_ms,
        );
    }

    print_grid(
        "Batch verification — total wall clock (ms)",
        rows,
        |_, ms, _| format!("{ms:.3}"),
    );
    print_grid(
        "Batch verification — amortised cost per proof (us)",
        rows,
        |_, ms, n| format!("{:.1}", ms * 1000.0 / n as f64),
    );
    print_grid(
        "Speedup over verifying one by one (N x single / batch)",
        rows,
        |r, ms, n| format!("{:.1}x", r.single_ms * n as f64 / ms),
    );

    // Marginal cost: a linear model total = fixed + slope * blocks predicts a
    // constant "per extra block" column; drift there means the model is wrong.
    println!("\nMarginal cost of each extra committed-input block (at N={max_proofs})");
    println!("  blocks │  total ms │ vs 1 block │ per extra block │ per block/proof");
    println!("  ───────┼───────────┼────────────┼─────────────────┼────────────────");
    let base = rows[0].batch_ms.last().copied().unwrap_or(1.0);
    for r in rows {
        let total = r.batch_ms.last().copied().unwrap_or(0.0);
        let (per_extra, per_proof) = if r.blocks == 1 {
            ("—".to_string(), "—".to_string())
        } else {
            let extra = (total - base) / (r.blocks - 1) as f64;
            (
                format!("{extra:.3} ms"),
                format!("{:.2} us", extra * 1000.0 / max_proofs as f64),
            )
        };
        println!(
            "  {:>6} │ {:>9.3} │ {:>9.2}x │ {per_extra:>15} │ {per_proof:>15}",
            r.blocks,
            total,
            total / base,
        );
    }

}

fn main() {
    let max_proofs = *PROOF_COUNTS.last().unwrap();

    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║   ZK-Pari batch verification: committed-input blocks x batch size    ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Circuit: `num_blocks` multiplications x_j * y_j = p_j, each declaring");
    println!("         x_j as a 1-element committed-input block, plus a * b = c with");
    println!("         c the single public input (instance length fixed at 2).");
    println!("Proof:   (2 + #blocks) G1 + 1 F. Verify: (3 + #blocks) pairings.");
    println!("Batching {max_proofs} proofs max; each measurement repeats for >= {MIN_SAMPLE_MS} ms.");
    println!();

    let rows: Vec<Row> = BLOCK_COUNTS
        .iter()
        .map(|&blocks| measure(blocks, max_proofs))
        .collect();

    print_report(&rows, max_proofs);
}
