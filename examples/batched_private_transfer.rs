//! Batched private transfers (one-to-many) with a single constant-size proof,
//! following Section 2 of the ZK-Pari note.
//!
//! A sender pays B recipients in one transaction. The transaction publishes
//! one transfer commitment per recipient (the recipients need them to update
//! their balances), but instead of B+1 separate range proofs it contains ONE
//! ZK-Pari proof of 3 G1 + 1 F — independent of B:
//!
//!   - Block 1 (size B+1) commits the claimed amounts v^_1..v^_B and the
//!     remaining balance v^_rem; its commitment C_ci_1 is transmitted.
//!   - Block 2 (size 1) commits the aggregate v_theta. Its commitment is
//!     com_theta = sum_i theta^{i-1} com_i + theta^B com_rem, which the
//!     verifier recomputes from the ledger commitments — never transmitted.
//!   - The circuit range-checks all B+1 values and enforces
//!     sum_i theta^{i-1} v^_i + theta^B v^_rem = v_theta, where theta is a
//!     Fiat-Shamir challenge bound to (com_alice, com_1..com_B, C_ci_1).
//!     By Schwartz-Zippel this guarantees (w.h.p.) the range-checked claimed
//!     values equal the values inside the ledger commitments.
//!
//! Run with: cargo run --release --example batched_private_transfer -p zkpari

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_relations::gr1cs::predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL;
use ark_relations::gr1cs::predicate::PredicateConstraintSystem;
use ark_relations::gr1cs::{
    ConstraintSystemRef, R1CS_PREDICATE_LABEL, SynthesisError, Variable,
};
use ark_relations::lc;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::SeedableRng;
use ark_std::Zero;
use zkpari::{CommittedInputOpening, Proof, VerifyingKey, ZkPari, ZkPariCircuit};
use zkpari::utils::transcript::IOPTranscript;
use std::time::Instant;

type E = Bls12_381;
type Fr = <Bls12_381 as Pairing>::ScalarField;
type G1 = <Bls12_381 as Pairing>::G1Affine;

// ---------------------------------------------------------------------------
// Batched range circuit (native SR1CS)
//
// Committed inputs, in allocation order:
//   block 1: v^_1, ..., v^_B, v^_rem   (B+1 values, all 64-bit range-checked)
//   block 2: v_theta                   (the theta-aggregate)
// Ordinary public input: theta.
//
// Each Horner step acc <- acc * theta + v^_i implements the product with two
// squares: (acc + theta)^2 = s_plus, (acc - theta)^2 = s_minus, so that
// acc * theta = (s_plus - s_minus)/4.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct BatchedRangeCircuit<F: Field> {
    theta: Option<F>,
    amounts: Option<Vec<u64>>,
    remaining: Option<u64>,
    batch_size: usize,
}

impl<F: Field> ZkPariCircuit<F> for BatchedRangeCircuit<F> {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let b = self.batch_size;
        let theta = self.theta;

        // Committed values: the B claimed amounts followed by the remaining balance
        let raw_values: Option<Vec<u64>> = match (self.amounts.as_ref(), self.remaining) {
            (Some(amounts), Some(remaining)) => {
                assert_eq!(amounts.len(), b);
                Some(amounts.iter().copied().chain([remaining]).collect())
            }
            _ => None,
        };
        let values: Option<Vec<F>> = raw_values
            .as_ref()
            .map(|raw| raw.iter().map(|v| F::from(*v)).collect());

        // Block 1 (committed inputs, allocated first): v^_1, ..., v^_B, v^_rem
        let mut value_vars = Vec::with_capacity(b + 1);
        for i in 0..=b {
            let vals = values.clone();
            let v = cs.new_witness_variable(move || {
                vals.ok_or(SynthesisError::AssignmentMissing).map(|v| v[i])
            })?;
            value_vars.push(v);
        }

        // Block 2 (single committed input): v_theta = sum_i theta^i * values[i]
        let v_theta_value: Option<F> = match (values.as_ref(), theta) {
            (Some(vals), Some(th)) => {
                let mut acc = vals[b];
                for v in vals[..b].iter().rev() {
                    acc = acc * th + v;
                }
                Some(acc)
            }
            _ => None,
        };
        let v_theta_var =
            cs.new_witness_variable(|| v_theta_value.ok_or(SynthesisError::AssignmentMissing))?;

        // theta is an ordinary public input (chosen after the ledger
        // commitments and the block-1 commitment are fixed)
        let theta_var = cs.new_input_variable(|| theta.ok_or(SynthesisError::AssignmentMissing))?;

        // 64-bit range check for every committed value
        for (i, &v) in value_vars.iter().enumerate() {
            let mut bit_vars = Vec::with_capacity(64);
            for bit in 0..64u32 {
                let raw = raw_values.clone();
                let bv = cs.new_witness_variable(move || {
                    let raw = raw.ok_or(SynthesisError::AssignmentMissing)?;
                    Ok(if (raw[i] >> bit) & 1 == 1 {
                        F::ONE
                    } else {
                        F::ZERO
                    })
                })?;
                bit_vars.push(bv);
            }
            let mut recon_minus_v = lc!() - v;
            let mut coeff = F::ONE;
            for &bv in &bit_vars {
                recon_minus_v = recon_minus_v + (coeff, bv);
                coeff.double_in_place();
            }
            let zero_lc = lc!() + v - v;
            cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;
            for &bv in &bit_vars {
                cs.enforce_sr1cs_constraint(|| lc!() + bv, || lc!() + bv)?;
            }
        }

        // Horner aggregation: acc = v^_rem; acc = acc * theta + v^_i for i = B..1
        let quarter = F::from(4u64).inverse().unwrap();
        let mut acc_lc = lc!() + value_vars[b];
        let mut acc_val: Option<F> = values.as_ref().map(|vals| vals[b]);
        for i in (0..b).rev() {
            let (av, th) = (acc_val, theta);
            let s_plus = cs.new_witness_variable(move || {
                let a = av.ok_or(SynthesisError::AssignmentMissing)?;
                let t = th.ok_or(SynthesisError::AssignmentMissing)?;
                Ok((a + t).square())
            })?;
            let s_minus = cs.new_witness_variable(move || {
                let a = av.ok_or(SynthesisError::AssignmentMissing)?;
                let t = th.ok_or(SynthesisError::AssignmentMissing)?;
                Ok((a - t).square())
            })?;
            let lhs_plus = acc_lc.clone() + theta_var;
            let lhs_minus = acc_lc.clone() - theta_var;
            cs.enforce_sr1cs_constraint(|| lhs_plus, || lc!() + s_plus)?;
            cs.enforce_sr1cs_constraint(|| lhs_minus, || lc!() + s_minus)?;
            acc_lc = lc!() + (quarter, s_plus) + (-quarter, s_minus) + value_vars[i];
            acc_val = match (acc_val, theta, values.as_ref()) {
                (Some(a), Some(t), Some(vals)) => Some(a * t + vals[i]),
                _ => None,
            };
        }

        // (acc - v_theta)^2 = 0
        let final_lhs = acc_lc - v_theta_var;
        let zero_lc = lc!() + value_vars[0] - value_vars[0];
        cs.enforce_sr1cs_constraint(|| final_lhs, || zero_lc)?;

        // Block 1: the claimed values; block 2: the theta-aggregate
        Ok(vec![value_vars, vec![v_theta_var]])
    }
}

// ---------------------------------------------------------------------------
// Transaction: what actually goes on chain
// ---------------------------------------------------------------------------

/// The on-chain payload of a one-to-many transfer. Note what is *absent*:
/// no per-recipient range proofs, and no `com_theta` (the verifier
/// recomputes it from the ledger commitments).
struct BatchedTransferTx {
    /// Per-recipient transfer commitments com_1..com_B (ledger data: the
    /// recipients' balances are updated by adding these).
    transfer_commitments: Vec<G1>,
    /// Commitment to the claimed amounts (block 1).
    c_ci_1: G1,
    /// The ZK-Pari proof body.
    t_g: G1,
    u_g: G1,
    v_a: Fr,
}

/// Fiat-Shamir challenge theta, bound to everything that must be fixed
/// before it is drawn: the sender's balance commitment, the per-recipient
/// transfer commitments, and the claimed-amounts commitment.
fn derive_theta(com_sender: &G1, transfer_commitments: &[G1], c_ci_1: &G1) -> Fr {
    let mut transcript = IOPTranscript::<Fr>::new(b"zk-pari batched transfer");
    let _ = transcript.append_serializable_element(b"com_sender", com_sender);
    for com in transfer_commitments {
        let _ = transcript.append_serializable_element(b"com_i", com);
    }
    let _ = transcript.append_serializable_element(b"c_ci_1", c_ci_1);
    transcript
        .get_and_append_challenge("theta".as_bytes())
        .unwrap()
}

/// Validator: recompute theta and com_theta from public data, reassemble the
/// proof, and verify. Returns the recomputed remaining-balance commitment on
/// success (the sender's new balance commitment).
fn validate(
    tx: &BatchedTransferTx,
    com_sender: &G1,
    vk: &VerifyingKey<E>,
) -> Option<G1> {
    let b = tx.transfer_commitments.len();
    let theta = derive_theta(com_sender, &tx.transfer_commitments, &tx.c_ci_1);

    // com_rem = com_sender - sum_i com_i  (balance conservation by construction)
    let com_sum = tx
        .transfer_commitments
        .iter()
        .fold(<E as Pairing>::G1::zero(), |acc, c| acc + c);
    let com_rem: G1 = (com_sender.into_group() - com_sum).into_affine();

    // com_theta = sum_i theta^{i-1} com_i + theta^B com_rem  (never transmitted)
    // One Pippenger MSM over B+1 points instead of B+1 independent scalar
    // multiplications: this is the only superconstant verifier work.
    let mut bases: Vec<G1> = tx.transfer_commitments.clone();
    bases.push(com_rem);
    let mut theta_powers = Vec::with_capacity(bases.len());
    let mut theta_pow = Fr::ONE;
    for _ in 0..bases.len() {
        theta_powers.push(theta_pow);
        theta_pow *= theta;
    }
    let com_theta: G1 =
        <E as Pairing>::G1::msm_unchecked(&bases, &theta_powers).into_affine();

    // Reassemble the full proof and verify; theta is the only public input
    let proof = Proof::<E> {
        c_ci: vec![tx.c_ci_1, com_theta],
        t_g: tx.t_g,
        u_g: tx.u_g,
        v_a: tx.v_a,
    };
    let _ = b;
    ZkPari::<E>::verify(&proof, vk, &[theta]).then_some(com_rem)
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(2026_06_10);

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║   Batched Private Transfers: one proof for B range proofs     ║");
    println!("║        (two committed-input blocks + theta aggregation)       ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    const B: usize = 8;
    let amounts: Vec<u64> = vec![100, 250, 50, 425, 75, 300, 600, 200];
    let alice_balance: u64 = 10_000;
    let total: u64 = amounts.iter().sum();
    let remaining: u64 = alice_balance - total;

    // ── 1. Trusted Setup ────────────────────────────────────────────────
    println!("1. Trusted Setup (batch size B = {B})");
    println!("   Block 1: B+1 = {} claimed values, Block 2: 1 aggregate\n", B + 1);
    let setup_start = Instant::now();
    let setup_circuit = BatchedRangeCircuit::<Fr> {
        theta: None,
        amounts: None,
        remaining: None,
        batch_size: B,
    };
    let (pk, vk) = ZkPari::<E>::keygen(setup_circuit, &mut rng);
    println!(
        "   Done in {:.1} ms; payment basis (G_pay, G~_pay) = (Sigma_ci_2[0], Gamma_ci_2)\n",
        setup_start.elapsed().as_secs_f64() * 1000.0
    );

    // ── 2. Ledger state ──────────────────────────────────────────────────
    println!("2. Ledger State");
    let r_alice = CommittedInputOpening::<Fr>::rand(&mut rng);
    let com_alice = pk.pedersen_commit(1, &[Fr::from(alice_balance)], &r_alice);
    println!(
        "   Alice's balance commitment: {}...  (opens to {alice_balance}, secret)\n",
        &format!("{}", com_alice)[..20]
    );

    // ── 3. Sender builds the one-to-many transaction ─────────────────────
    println!("3. Alice pays {B} recipients amounts {amounts:?} (total {total})");
    let prove_start = Instant::now();

    // 3a. Per-recipient transfer commitments in the payment basis
    let r_i: Vec<CommittedInputOpening<Fr>> = (0..B)
        .map(|_| CommittedInputOpening::rand(&mut rng))
        .collect();
    let com_i: Vec<G1> = amounts
        .iter()
        .zip(&r_i)
        .map(|(v, r)| pk.pedersen_commit(1, &[Fr::from(*v)], r))
        .collect();

    // 3b. Remaining balance commitment (homomorphically determined)
    let r_rem = r_i.iter().fold(r_alice.clone(), |acc, r| &acc - r);

    // 3c. Commit to the claimed values (block 1), then draw theta
    let rho_1 = CommittedInputOpening::<Fr>::rand(&mut rng);
    let claimed: Vec<Fr> = amounts
        .iter()
        .map(|v| Fr::from(*v))
        .chain([Fr::from(remaining)])
        .collect();
    let c_ci_1 = pk.pedersen_commit(0, &claimed, &rho_1);
    let theta = derive_theta(&com_alice, &com_i, &c_ci_1);

    // 3d. Opening of the aggregate: rho_2 = sum theta^{i-1} r_i + theta^B r_rem
    let mut theta_pow = Fr::ONE;
    let mut rho_2 = Fr::zero();
    for r in r_i.iter().chain([&r_rem]) {
        rho_2 += r.rho * theta_pow;
        theta_pow *= theta;
    }
    let rho_2 = CommittedInputOpening { rho: rho_2 };

    // 3e. One proof for B+1 range checks + the aggregation constraint
    let circuit = BatchedRangeCircuit::<Fr> {
        theta: Some(theta),
        amounts: Some(amounts.clone()),
        remaining: Some(remaining),
        batch_size: B,
    };
    let proof = ZkPari::<E>::prove_with_openings(circuit, &pk, &[rho_1, rho_2], &mut rng)
        .expect("batched range proof failed");
    let prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

    let tx = BatchedTransferTx {
        transfer_commitments: com_i.clone(),
        c_ci_1: proof.c_ci[0],
        t_g: proof.t_g,
        u_g: proof.u_g,
        v_a: proof.v_a,
    };
    println!("   Transaction built in {prove_ms:.1} ms\n");

    // ── 4. Sizes ──────────────────────────────────────────────────────────
    let g1_size = tx.c_ci_1.serialized_size(ark_serialize::Compress::Yes);
    let fr_size = tx.v_a.serialized_size(ark_serialize::Compress::Yes);
    let proof_bytes = 3 * g1_size + fr_size;
    let naive_bytes = (B + 1) * (2 * g1_size + fr_size) + g1_size;
    println!("4. On-chain size (excluding the B ledger commitments themselves)");
    println!("   This construction : C_ci_1 + (T, U, v_a)            = 3 G1 + 1 F = {proof_bytes} bytes");
    println!(
        "   Naive             : B+1 = {} proofs of (T, U, v_a) + C_ci = {naive_bytes} bytes",
        B + 1
    );
    println!(
        "   com_theta is recomputed by the verifier and never transmitted;\n   \
         the proof size is independent of B.\n"
    );

    // ── 5. Validator ──────────────────────────────────────────────────────
    println!("5. Validator Checks");
    let verify_start = Instant::now();
    let com_rem = validate(&tx, &com_alice, &vk).expect("transaction must verify");
    let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;
    println!("   Recomputed theta and com_theta from the ledger commitments");
    println!("   One pairing equation covers all {} range checks: PASS", B + 1);
    println!("   Verification done in {verify_ms:.1} ms\n");

    // A tampered transaction (inflated transfer commitment) must be rejected
    let mut bad_tx = BatchedTransferTx {
        transfer_commitments: com_i.clone(),
        c_ci_1: tx.c_ci_1,
        t_g: tx.t_g,
        u_g: tx.u_g,
        v_a: tx.v_a,
    };
    bad_tx.transfer_commitments[3] = pk.pedersen_commit(
        1,
        &[Fr::from(u64::MAX)],
        &CommittedInputOpening::rand(&mut rng),
    );
    assert!(validate(&bad_tx, &com_alice, &vk).is_none());
    println!("   Tampered transfer commitment: REJECTED\n");

    // ── 6. Ledger update ──────────────────────────────────────────────────
    println!("6. Ledger Update");
    // Sanity: Alice's new commitment opens to the remaining balance
    assert_eq!(
        com_rem,
        pk.pedersen_commit(1, &[Fr::from(remaining)], &r_rem)
    );
    println!("   Alice  : com <- com_alice - sum(com_i)   (opens to {remaining})");
    println!("   Each recipient i: com <- com + com_i     (learns (v_i, r_i) off-chain)\n");

    // ── 7. Proof size is independent of B ─────────────────────────────────
    println!("7. Scaling: one transaction, growing batch size");
    println!("   (proof stays 3 G1 + 1 F; naive grows as (B+1)(2 G1 + 1 F))\n");
    for b in [2usize, 8, 32, 128] {
        let amounts: Vec<u64> = (1..=b as u64).map(|i| 10 * i).collect();
        let balance: u64 = 1_000_000;
        let remaining = balance - amounts.iter().sum::<u64>();

        let keygen_start = Instant::now();
        let (pk_b, vk_b) = ZkPari::<E>::keygen(
            BatchedRangeCircuit::<Fr> {
                theta: None,
                amounts: None,
                remaining: None,
                batch_size: b,
            },
            &mut rng,
        );
        let keygen_ms = keygen_start.elapsed().as_secs_f64() * 1000.0;

        let r_sender = CommittedInputOpening::<Fr>::rand(&mut rng);
        let com_sender = pk_b.pedersen_commit(1, &[Fr::from(balance)], &r_sender);
        let r_i: Vec<CommittedInputOpening<Fr>> = (0..b)
            .map(|_| CommittedInputOpening::rand(&mut rng))
            .collect();
        let com_i: Vec<G1> = amounts
            .iter()
            .zip(&r_i)
            .map(|(v, r)| pk_b.pedersen_commit(1, &[Fr::from(*v)], r))
            .collect();
        let r_rem = r_i.iter().fold(r_sender.clone(), |acc, r| &acc - r);

        let prove_start = Instant::now();
        let rho_1 = CommittedInputOpening::<Fr>::rand(&mut rng);
        let claimed: Vec<Fr> = amounts
            .iter()
            .map(|v| Fr::from(*v))
            .chain([Fr::from(remaining)])
            .collect();
        let c_ci_1 = pk_b.pedersen_commit(0, &claimed, &rho_1);
        let theta = derive_theta(&com_sender, &com_i, &c_ci_1);
        let mut theta_pow = Fr::ONE;
        let mut rho_2 = Fr::zero();
        for r in r_i.iter().chain([&r_rem]) {
            rho_2 += r.rho * theta_pow;
            theta_pow *= theta;
        }
        let proof = ZkPari::<E>::prove_with_openings(
            BatchedRangeCircuit::<Fr> {
                theta: Some(theta),
                amounts: Some(amounts.clone()),
                remaining: Some(remaining),
                batch_size: b,
            },
            &pk_b,
            &[rho_1, CommittedInputOpening { rho: rho_2 }],
            &mut rng,
        )
        .unwrap();
        let prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

        let tx = BatchedTransferTx {
            transfer_commitments: com_i,
            c_ci_1: proof.c_ci[0],
            t_g: proof.t_g,
            u_g: proof.u_g,
            v_a: proof.v_a,
        };
        let verify_start = Instant::now();
        assert!(validate(&tx, &com_sender, &vk_b).is_some());
        let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;

        let proof_bytes = 3 * g1_size + fr_size;
        let naive_bytes = (b + 1) * (2 * g1_size + fr_size) + g1_size;
        println!(
            "   B = {b:>3} │ proof {proof_bytes:>4} B (naive {naive_bytes:>6} B, {:>5.1}x) │ keygen {keygen_ms:>8.1} ms │ prove {prove_ms:>8.1} ms │ verify {verify_ms:>6.1} ms",
            naive_bytes as f64 / proof_bytes as f64,
        );
    }
    println!();

    // ── 8. Summary ─────────────────────────────────────────────────────────
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  One 176-byte proof showed, for all B recipients at once:     ║");
    println!("║    - every transfer amount is non-negative (range checked)    ║");
    println!("║    - the sender's remaining balance is non-negative           ║");
    println!("║    - claimed amounts equal the committed ledger amounts       ║");
    println!("║      (theta-aggregation, never revealing any amount)          ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
}
