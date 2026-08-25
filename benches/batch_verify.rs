//! Experiment 2 — batch verification vs individual verification (BLS12-381).
//!
//! 2a: a (committed-input blocks) x (proofs per batch) grid of amortised cost
//!     per proof, each cell annotated with its speedup over verifying one at a
//!     time. Total wall clock (per-proof * N) is not printed separately.
//! 2b: a phase breakdown at the largest batch, showing where the time goes.
//!
//! Batch verification replaces N independent `(3 + #blocks)`-pairing checks
//! with a single one, by taking a random linear combination with 128-bit
//! coefficients. The fixed cost of that one pairing product amortises away as
//! N grows, leaving per-proof cost dominated by the MSMs — which is why the
//! speedup keeps climbing with N but shrinks as blocks are added (each block
//! contributes another per-proof MSM term that batching cannot remove).
//!
//! **Proof pool.** Timing N = 65536 proofs per block count would be dominated
//! by *proving*, not verifying, so the pool is built with `ZkPari::simulate`,
//! which the library documents for exactly this (verifier benchmarking and
//! load generation). This is sound for free: the scheme is statistically
//! honest-verifier zero knowledge, so simulated and real proofs are drawn from
//! distributions at statistical distance at most `1/(q - m)`, and verification
//! performs the same value-independent sequence of MSMs and pairings over
//! either. A genuine proof is still generated and verified at every block
//! count, so the keys under test are exercised by real proving.
//!
//! Batch-verification cost is independent of circuit size, so the circuit is
//! held small and fixed.
//!
//! Threads: single-threaded by default. Set `ZKPARI_BENCH_THREADS=0` for all
//! cores, or `=N` for N.
//!
//! Run with: cargo bench --bench batch_verify

mod common;

use ark_std::rand::{rngs::StdRng, SeedableRng};
use common::*;
use std::io::Write;
use ark_ec::pairing::Pairing;
use ark_ec::VariableBaseMSM;
use ark_ff::{Field, PrimeField, Zero};
use zkpari::utils::msm_bigint_wnaf;
use zkpari::{CommittedInputOpening, Proof, ProvingKey, Trapdoor, VerifyingKey, ZkPari};

/// Per-phase costs of one batch verification, in microseconds.
///
/// The library itself carries no instrumentation — `batch_verify` is plain
/// production code — so this bench re-executes the same phases against the
/// public API and times each. [`phase_breakdown`] asserts its total against a
/// real `batch_verify` call, which catches the reconstruction drifting away
/// from what the library actually does.
#[derive(Default, Clone, Copy)]
struct Phases {
    challenge: f64,
    lagrange: f64,
    instance: f64,
    c_msm: f64,
    t_msm: f64,
    u_msm: f64,
    v_msm: f64,
    pairing: f64,
}

impl Phases {
    fn total(&self) -> f64 {
        self.challenge
            + self.lagrange
            + self.instance
            + self.c_msm
            + self.t_msm
            + self.u_msm
            + self.v_msm
            + self.pairing
    }
}

/// Time each phase of batch verification, mirroring `ZkPari::batch_verify`.
fn phase_breakdown(pool: &[Claim], vk: &VerifyingKey<E>, blocks: usize, batch_ms: f64) -> Phases {
    use ark_std::rand::RngCore;
    fn ms(f: impl FnMut()) -> f64 {
        time_ms(120, 20, f)
    }

    let n = pool.len();
    let mut rng = StdRng::seed_from_u64(7);

    // Values later phases consume, computed once outside the timing loops.
    let challenges: Vec<Fr> = pool.iter().map(|(p, x)| fs_challenge(vk, x, p)).collect();
    // 128-bit, exactly as `batch_verify` samples them. Using full-width
    // scalars here would inflate every MSM phase by ~2x, since ark-ec's MSM
    // skips the all-zero high windows that 128-bit values leave empty.
    let rhos: Vec<Fr> = (0..n)
        .map(|_| {
            let mut b = [0u8; 16];
            rng.fill_bytes(&mut b);
            Fr::from_le_bytes_mod_order(&b)
        })
        .collect();
    let t_bases: Vec<_> = pool.iter().map(|(p, _)| p.t_g).collect();
    let u_bases: Vec<_> = pool.iter().map(|(p, _)| p.u_g).collect();
    let instance_size = vk.succinct_index.instance_len;
    let start_ind = vk.succinct_index.num_constraints - instance_size;
    let lagrange_args = (&vk.domain, &challenges, start_ind, instance_size);
    let coeffs = ZkPari::<E>::batch_eval_last_lagrange_coeffs::<Fr>(
        lagrange_args.0,
        lagrange_args.1,
        lagrange_args.2,
        lagrange_args.3,
    );

    // The final multi-pairing has (3 + blocks) terms; the G1 side's exact
    // values do not affect its cost, only the term count.
    let mut g1: Vec<_> = vec![t_bases[0]; blocks + 2];
    g1.push(
        msm_bigint_wnaf::<G1>(
            &[u_bases[0], vk.alpha_g, vk.beta_g],
            &[Fr::ONE.into(), Fr::ONE.into(), Fr::ONE.into()],
        )
        .into(),
    );
    let mut g2 = vk.delta_h_prep.clone();
    g2.extend([
        vk.delta_w_h_prep.clone(),
        vk.tau_h_prep.clone(),
        vk.h_prep.clone(),
    ]);

    let phases = Phases {
        challenge: ms(|| {
            let c: Vec<Fr> = pool.iter().map(|(p, x)| fs_challenge(vk, x, p)).collect();
            let _ = std::hint::black_box(c);
        }),
        lagrange: ms(|| {
            let _ = std::hint::black_box(ZkPari::<E>::batch_eval_last_lagrange_coeffs::<Fr>(
                lagrange_args.0,
                lagrange_args.1,
                lagrange_args.2,
                lagrange_args.3,
            ));
        }),
        instance: ms(|| {
            let mut v_rs = Vec::with_capacity(n);
            for ((proof, x), lc) in pool.iter().zip(&coeffs) {
                let x_a = lc
                    .iter()
                    .zip(core::iter::once(Fr::ONE).chain(x.iter().copied()))
                    .fold(Fr::zero(), |acc, (l, v)| acc + *l * v);
                v_rs.push((x_a + proof.v_a).square());
            }
            let _ = std::hint::black_box(v_rs);
        }),
        c_msm: ms(|| {
            for j in 0..blocks {
                let bases: Vec<_> = pool.iter().map(|(p, _)| p.c_ci[j]).collect();
                let _ = std::hint::black_box(msm(&bases, &rhos));
            }
        }),
        t_msm: ms(|| {
            let _ = std::hint::black_box(msm(&t_bases, &rhos));
        }),
        u_msm: ms(|| {
            let _ = std::hint::black_box(msm(&u_bases, &rhos));
        }),
        v_msm: ms(|| {
            let rho_r: Vec<Fr> = rhos.iter().zip(&challenges).map(|(a, b)| *a * *b).collect();
            let _ = std::hint::black_box(msm(&u_bases, &rho_r));
        }),
        pairing: ms(|| {
            let _ = std::hint::black_box(E::multi_pairing(g1.clone(), g2.clone()));
        }),
    };

    // Guard against this reconstruction drifting from `batch_verify`.
    let ratio = phases.total() / batch_ms;
    assert!(
        (0.8..1.25).contains(&ratio),
        "phase breakdown sums to {:.1} ms but batch_verify took {batch_ms:.1} ms \
         (ratio {ratio:.2}) — the reconstruction no longer mirrors the library",
        phases.total()
    );
    phases
}

/// Fiat-Shamir challenge, exactly as verification derives it: clone the
/// transcript the key seeded with itself, then absorb the per-proof material.
fn fs_challenge(vk: &VerifyingKey<E>, x: &[Fr], p: &Proof<E>) -> Fr {
    let mut t = vk.transcript().clone();
    let _ = t.append_serializable_element(b"input", &x.to_vec());
    for c in &p.c_ci {
        let _ = t.append_serializable_element(b"comm_ci", c);
    }
    let _ = t.append_serializable_element(b"comm", &p.t_g);
    t.get_and_append_challenge(b"r").unwrap()
}

const BLOCK_COUNTS: &[usize] = &[0, 1, 2, 4, 8, 16, 32, 64];
const PROOF_COUNTS: &[usize] = &[1, 256, 4096, 65536];

/// Circuit size is irrelevant to batch verification; keep it small so the
/// real-proof cross-check stays cheap.
const LOG2_CONSTRAINTS: u32 = 12;

type Claim = (Proof<E>, Vec<Fr>);
type G1 = <E as Pairing>::G1;

/// `msm_unchecked` over G1, spelled once.
fn msm(bases: &[<E as Pairing>::G1Affine], scalars: &[Fr]) -> G1 {
    <G1 as VariableBaseMSM>::msm_unchecked(bases, scalars)
}

/// One simulated claim: fresh Pedersen commitments and a fresh public input,
/// so every proof in the pool has its own Fiat-Shamir challenge.
fn simulated_claim(
    pk: &ProvingKey<E>,
    vk: &VerifyingKey<E>,
    td: &Trapdoor<E>,
    blocks: usize,
    rng: &mut StdRng,
) -> Claim {
    // Each claim is independent, so the pool can be built in parallel even
    // when the measurements themselves are pinned to one thread.
    use ark_std::UniformRand;
    let c_ci: Vec<_> = (0..blocks)
        .map(|j| pk.pedersen_commit(j, &[Fr::rand(rng)], &CommittedInputOpening::rand(rng)))
        .collect();
    let x = vec![Fr::rand(rng)];
    let proof = ZkPari::<E>::simulate(td, vk, &c_ci, &x, rng);
    (proof, x)
}

struct Row {
    blocks: usize,
    single_us: f64,
    /// Mean ms for `batch_verify`, indexed like `PROOF_COUNTS`.
    batch_ms: Vec<f64>,
    phases: Phases,
}

fn measure(blocks: usize, max_proofs: usize) -> Row {
    eprint!("  {blocks:>2} block(s): keygen ...");
    std::io::stdout().flush().ok();
    let mut rng = StdRng::seed_from_u64(20_260_824 + blocks as u64);
    let circuit = SquareChain::for_log2_constraints(LOG2_CONSTRAINTS, blocks, 3);
    let (pk, vk, td) = ZkPari::<E>::keygen_with_trapdoor(circuit, &mut rng);

    // Sanity: a genuine proof of this circuit verifies under these keys.
    let real = ZkPari::<E>::prove(circuit, &pk, &mut rng).expect("proving failed");
    assert!(
        ZkPari::<E>::verify(&real, &vk, &circuit.public_input()),
        "real proof failed to verify at {blocks} blocks"
    );

    eprint!(" simulating {max_proofs} ...");
    std::io::stdout().flush().ok();
    let pool: Vec<Claim> = (0..max_proofs)
        .map(|_| simulated_claim(&pk, &vk, &td, blocks, &mut rng))
        .collect();
    assert!(
        ZkPari::<E>::batch_verify(&pool, &vk, &mut rng),
        "simulated pool failed to batch-verify at {blocks} blocks"
    );

    eprint!(" timing ...");
    std::io::stdout().flush().ok();
    let (p0, x0) = &pool[0];
    let single_us = 1000.0 * time_ms(150, 2000, || {
        std::hint::black_box(ZkPari::<E>::verify(p0, &vk, x0));
    });
    let batch_ms: Vec<f64> = PROOF_COUNTS
        .iter()
        .map(|&n| {
            time_ms(150, 200, || {
                assert!(ZkPari::<E>::batch_verify(&pool[..n], &vk, &mut rng));
            })
        })
        .collect();

    let full_batch_ms = *batch_ms.last().unwrap();
    let phases = phase_breakdown(&pool, &vk, blocks, full_batch_ms);
    eprintln!(" done");

    Row { blocks, single_us, batch_ms, phases }
}

/// Print a `blocks x PROOF_COUNTS` table; `cell` renders one entry.
fn print_grid(title: &str, rows: &[Row], cell: impl Fn(&Row, f64, usize) -> String) {
    println!("\n{title}");
    print!("  blocks │");
    for n in PROOF_COUNTS {
        print!(" {:>16}", format!("N={n}"));
    }
    print!("\n  ───────┼");
    for _ in PROOF_COUNTS {
        print!("─────────────────");
    }
    println!();
    for r in rows {
        print!("  {:>6} │", r.blocks);
        for (&ms, &n) in r.batch_ms.iter().zip(PROOF_COUNTS) {
            print!(" {:>16}", cell(r, ms, n));
        }
        println!();
    }
}

fn main() {
    in_bench_pool(run);
}

fn run() {
    let max_proofs = *PROOF_COUNTS.last().unwrap();

    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║  2. ZK-Pari batch vs individual verification — BLS12-381             ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Threads: {}.", thread_label());
    println!("Circuit fixed at 2^{LOG2_CONSTRAINTS} SR1CS constraints (batch cost does not depend on it).");
    println!("Pool built with the HVZK simulator: statistically indistinguishable");
    println!("from real proofs, so verification cost is identical by construction.");
    println!();

    let rows: Vec<Row> = BLOCK_COUNTS
        .iter()
        .map(|&b| measure(b, max_proofs))
        .collect();

    // The baseline the speedup column in the grid below divides by. Total wall
    // clock is recoverable as per-proof * N, so it is not printed separately.
    println!("\nPer-proof cost of individual verification");
    println!("  blocks │ pairings │ verify us");
    println!("  ───────┼──────────┼──────────");
    for r in &rows {
        println!("  {:>6} │ {:>8} │ {:>9.1}", r.blocks, 3 + r.blocks, r.single_us);
    }

    print_grid(
        "2a. Amortised batch cost per proof: us (speedup vs individual)",
        &rows,
        |r, ms, n| {
            let per_proof = ms * 1000.0 / n as f64;
            format!("{per_proof:.2} ({:.1}x)", r.single_us / per_proof)
        },
    );
    println!("\n2b. Where the time goes at N={max_proofs} (ms)");
    println!("  Phases are re-executed against the public API — the library carries no");
    println!("  instrumentation — and their total is checked against `batch_verify`.");
    println!("  blocks │ challenge │ lagrange │ instance │   C~ MSM │   T~ MSM │   U~ MSM │   V~ MSM │ pairing │    sum │ measured");
    println!("  ───────┼───────────┼──────────┼──────────┼──────────┼──────────┼──────────┼──────────┼─────────┼────────┼─────────");
    for Row { blocks, phases: p, batch_ms, .. } in &rows {
        println!(
            "  {blocks:>6} │ {:>9.1} │ {:>8.1} │ {:>8.1} │ {:>8.1} │ {:>8.1} │ {:>8.1} │ {:>8.1} │ {:>7.2} │ {:>6.1} │ {:>8.1}",
            p.challenge, p.lagrange, p.instance, p.c_msm, p.t_msm, p.u_msm, p.v_msm,
            p.pairing, p.total(), batch_ms.last().unwrap(),
        );
    }
    println!();
    println!("  C~ MSM is the only column that scales with the block count: one");
    println!("  MSM over all N proofs per committed-input block. T~/U~ are the same");
    println!("  MSM over T and U; V~ is the same again but with full-width scalars");
    println!("  (rho_k * r^(k) rather than the 128-bit rho_k). The final pairing");
    println!("  product is a fixed per-batch cost, which is what amortises away.");
    println!();
}
