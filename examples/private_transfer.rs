//! Private transfers with hidden amounts using ZK-Pari (vanishing-polynomial
//! mask construction with committed inputs).
//!
//! Demonstrates a Zether-like private payment system where:
//!   - Account balances are stored as Pedersen commitments
//!   - The committed-input commitment C_ci of a ZK-Pari proof IS the ledger
//!     commitment: the transfer value is a committed input, hidden by the
//!     B-side vanishing direction rho_ci * v_K(X)
//!   - Transfers are validated by range proofs + homomorphic commitment checks
//!   - A full proof is 3 G1 + 1 F; since C_ci is ledger state here, the
//!     incremental proof material is 2 G1 + 1 F per range proof
//!
//! Run with: cargo run --release --example private_transfer -p zkpari

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_relations::gr1cs::predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL;
use ark_relations::gr1cs::predicate::PredicateConstraintSystem;
use ark_relations::gr1cs::{
    ConstraintSystemRef, R1CS_PREDICATE_LABEL, SynthesisError, Variable,
};
use ark_relations::lc;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::SeedableRng;
use zkpari::{CommittedInputOpening, ZkPari, ZkPariCircuit};
use std::time::Instant;

// ---------------------------------------------------------------------------
// Range proof circuit (native SR1CS)
//
// Proves the witness variable v is in [0, 2^64), and declares v as the
// single committed input: the proof's c_ci[0] is then a Pedersen commitment
// to v under the CRS basis (Sigma_ci[0], Gamma_ci).
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct RangeProofCircuit {
    value: Option<u64>,
}

impl<F: Field> ZkPariCircuit<F> for RangeProofCircuit {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let value = self.value;

        // The committed input (declared in the return value below)
        let v = cs.new_witness_variable(|| {
            let val = value.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(F::from(val))
        })?;

        let mut bit_vars = Vec::with_capacity(64);
        for i in 0..64u32 {
            let b = cs.new_witness_variable(|| {
                let val = value.ok_or(SynthesisError::AssignmentMissing)?;
                Ok(if (val >> i) & 1 == 1 { F::ONE } else { F::ZERO })
            })?;
            bit_vars.push(b);
        }

        // (sum(b_i * 2^i) - v)^2 = 0, with `v - v` as the zero RHS to avoid
        // the empty-LC -> symbolic_lc(0) aliasing bug.
        let mut recon_minus_v = lc!() - v;
        let mut coeff = F::ONE;
        for &b in &bit_vars {
            recon_minus_v = recon_minus_v + (coeff, b);
            coeff.double_in_place();
        }
        let zero_lc = lc!() + v - v;
        cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;

        // b_i^2 = b_i
        for &b in &bit_vars {
            cs.enforce_sr1cs_constraint(|| lc!() + b, || lc!() + b)?;
        }

        // Declare v as the single committed-input block
        Ok(vec![vec![v]])
    }
}

// ---------------------------------------------------------------------------
// Ledger: stores account balances as G1 points (Pedersen commitments)
// ---------------------------------------------------------------------------

struct Account<E: Pairing> {
    #[allow(dead_code)]
    name: String,
    balance: u64,
    commitment: E::G1Affine,
    opening: CommittedInputOpening<E::ScalarField>,
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    type E = Bls12_381;
    type Fr = <E as Pairing>::ScalarField;

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(2026_06_10);

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║       Private Transfers with Hidden Amounts (ZK-Pari)         ║");
    println!("║          vanishing-polynomial masks + committed inputs        ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ── 1. Trusted Setup ────────────────────────────────────────────────
    println!("1. Trusted Setup");
    println!("   Generating CRS for 64-bit range proof circuit (1 committed input)...");

    let setup_start = Instant::now();
    let dummy_circuit = RangeProofCircuit { value: Some(0) };
    let (pk, vk) = ZkPari::<E>::keygen(dummy_circuit, &mut rng);
    println!(
        "   Done in {:.1} ms\n",
        setup_start.elapsed().as_secs_f64() * 1000.0
    );

    println!("   Pedersen commitment generators fixed by the CRS:");
    println!("     G_pay  = Sigma_ci[0] = ((alpha a(tau) + beta b(tau))/delta_1) G");
    println!("     G~_pay = Gamma_ci    = (beta v_K(tau)/delta_1) G");
    println!();

    // ── 2. Account Creation (Deposits) ──────────────────────────────────
    println!("2. Account Creation");

    let alice_balance: u64 = 1000;
    let bob_balance: u64 = 500;

    let alice_opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let alice_com = pk.pedersen_commit(0, &[Fr::from(alice_balance)], &alice_opening);

    let bob_opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let bob_com = pk.pedersen_commit(0, &[Fr::from(bob_balance)], &bob_opening);

    let mut alice = Account::<E> {
        name: "Alice".into(),
        balance: alice_balance,
        commitment: alice_com,
        opening: alice_opening,
    };

    let mut bob = Account::<E> {
        name: "Bob".into(),
        balance: bob_balance,
        commitment: bob_com,
        opening: bob_opening,
    };

    println!(
        "   Alice deposits {} tokens  =>  com_Alice = {}...",
        alice.balance,
        &format!("{}", alice.commitment)[..20]
    );
    println!(
        "   Bob   deposits {} tokens  =>  com_Bob   = {}...\n",
        bob.balance,
        &format!("{}", bob.commitment)[..20]
    );

    // ── 3. Private Transfer: Alice → Bob ─────────────────────────────────
    let transfer_amount: u64 = 300;
    let remaining_balance: u64 = alice.balance - transfer_amount;

    println!("3. Private Transfer: Alice sends {transfer_amount} tokens to Bob");
    println!("   (Validators see ONLY commitments and proofs, never amounts)\n");

    // 3a. Sender creates commitment to the transfer amount
    let delta_opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let com_delta = pk.pedersen_commit(0, &[Fr::from(transfer_amount)], &delta_opening);

    // 3b. Derive the remaining-balance commitment via group subtraction
    let remaining_opening = &alice.opening - &delta_opening;
    let com_remaining: <E as Pairing>::G1Affine =
        (alice.commitment.into_group() - com_delta.into_group()).into_affine();

    // Sanity: the derived commitment equals a fresh commit with the derived opening
    let com_remaining_check =
        pk.pedersen_commit(0, &[Fr::from(remaining_balance)], &remaining_opening);
    assert_eq!(
        com_remaining, com_remaining_check,
        "Pedersen commitment homomorphism broken"
    );
    println!("   [ok] Commitment homomorphism: com_Alice = com_delta + com_remaining");

    // 3c. Prove the transfer amount is in [0, 2^64); C_ci is forced to com_delta
    println!("   Proving transfer amount in range [0, 2^64)...");
    let prove_start = Instant::now();
    let proof_delta = ZkPari::<E>::prove_with_openings(
        RangeProofCircuit {
            value: Some(transfer_amount),
        },
        &pk,
        core::slice::from_ref(&delta_opening),
        &mut rng,
    )
    .expect("range proof for transfer amount failed");
    let delta_prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

    // 3d. Prove the remaining balance is in [0, 2^64); C_ci is forced to com_remaining
    println!("   Proving remaining balance in range [0, 2^64)...");
    let prove_start = Instant::now();
    let proof_remaining = ZkPari::<E>::prove_with_openings(
        RangeProofCircuit {
            value: Some(remaining_balance),
        },
        &pk,
        core::slice::from_ref(&remaining_opening),
        &mut rng,
    )
    .expect("range proof for remaining balance failed");
    let remaining_prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;
    println!("   Proving done: {delta_prove_ms:.1} ms + {remaining_prove_ms:.1} ms");

    let proof_size = proof_delta.c_ci[0].serialized_size(ark_serialize::Compress::Yes)
        + proof_delta.t_g.serialized_size(ark_serialize::Compress::Yes)
        + proof_delta.u_g.serialized_size(ark_serialize::Compress::Yes)
        + proof_delta.v_a.serialized_size(ark_serialize::Compress::Yes);
    println!(
        "   Proof size: {proof_size} bytes (C_ci, T, U, v_a) = 3 G1 + 1 F;\n   \
         C_ci is ledger state, so the incremental proof is 2 G1 + 1 F\n"
    );

    // ── 4. Validator Checks ──────────────────────────────────────────────
    println!("4. Validator Checks (public, no secret knowledge needed)");

    // 4a. Verify both range proofs
    let verify_start = Instant::now();
    let delta_ok = ZkPari::<E>::verify(&proof_delta, &vk, &[]);
    let remaining_ok = ZkPari::<E>::verify(&proof_remaining, &vk, &[]);
    let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;

    println!(
        "   Range proof (transfer amount)  : {}",
        if delta_ok { "PASS" } else { "FAIL" }
    );
    println!(
        "   Range proof (remaining balance): {}",
        if remaining_ok { "PASS" } else { "FAIL" }
    );
    assert!(delta_ok && remaining_ok);

    // 4b. Commitment consistency: each proof's C_ci must match the
    //     commitment decomposition published with the transaction
    assert_eq!(
        proof_delta.c_ci[0], com_delta,
        "proof_delta.c_ci must equal com_delta"
    );
    assert_eq!(
        proof_remaining.c_ci[0], com_remaining,
        "proof_remaining.c_ci must equal com_remaining"
    );
    println!("   proof_delta.c_ci == com_delta        : PASS");
    println!("   proof_remaining.c_ci == com_remaining: PASS");

    // 4c. Balance conservation: com_delta + com_remaining == sender's old commitment
    let sum: <E as Pairing>::G1Affine =
        (proof_delta.c_ci[0].into_group() + proof_remaining.c_ci[0].into_group()).into_affine();
    assert_eq!(sum, alice.commitment, "balance conservation check failed");
    println!("   com_delta + com_remaining == com_Alice: PASS");
    println!("   Verification done: {verify_ms:.1} ms\n");

    // ── 5. Update Ledger ─────────────────────────────────────────────────
    println!("5. Update Ledger");

    let old_alice_com = alice.commitment;
    let old_bob_com = bob.commitment;

    alice.balance = remaining_balance;
    alice.commitment = proof_remaining.c_ci[0];
    alice.opening = remaining_opening;

    // Bob learns (amount, delta opening) out of band; the paper's eVRF-based
    // randomness recovery makes this non-interactive.
    bob.balance += transfer_amount;
    bob.commitment =
        (bob.commitment.into_group() + proof_delta.c_ci[0].into_group()).into_affine();
    bob.opening = &bob.opening + &delta_opening;

    // Both updated commitments must be consistent with the new balances
    let alice_com_check = pk.pedersen_commit(0, &[Fr::from(alice.balance)], &alice.opening);
    let bob_com_check = pk.pedersen_commit(0, &[Fr::from(bob.balance)], &bob.opening);
    assert_eq!(alice.commitment, alice_com_check);
    assert_eq!(bob.commitment, bob_com_check);

    println!(
        "   Alice: {} tokens  (com changed: {})",
        alice.balance,
        old_alice_com != alice.commitment
    );
    println!(
        "   Bob  : {} tokens  (com changed: {})\n",
        bob.balance,
        old_bob_com != bob.commitment
    );

    let alice_pre_transfer_com = old_alice_com;

    // ── 6. Batch Verification of Full Transfers at Scale ───────────────
    //
    // Each transfer requires:
    //   a) Two range proof verifications (delta + remaining)
    //   b) C_ci consistency: proof_delta.c_ci == com_delta,
    //      proof_remaining.c_ci == com_remaining
    //   c) Balance conservation: proof_delta.c_ci + proof_remaining.c_ci
    //      == sender_commitment
    println!("6. Batch Verification of Full Transfers at Scale");
    println!("   (each transfer = 2 range proofs + commitment checks)\n");

    for num_transfers in [512usize, 2048, 8192] {
        let transfers: Vec<_> = (0..num_transfers)
            .map(|_| {
                (
                    alice_pre_transfer_com,
                    proof_delta.clone(),
                    proof_remaining.clone(),
                )
            })
            .collect();

        // --- Individual: verify each transfer one by one ---
        let indiv_start = Instant::now();
        for (sender_com, p_delta, p_rem) in &transfers {
            assert!(ZkPari::<E>::verify(p_delta, &vk, &[]));
            assert!(ZkPari::<E>::verify(p_rem, &vk, &[]));
            let sum = (p_delta.c_ci[0].into_group() + p_rem.c_ci[0].into_group()).into_affine();
            assert_eq!(sum, *sender_com);
        }
        let indiv_ms = indiv_start.elapsed().as_secs_f64() * 1000.0;

        // --- Batch: batch-verify all range proofs, then check commitments ---
        let batch_start = Instant::now();

        let proofs_and_inputs: Vec<_> = transfers
            .iter()
            .flat_map(|(_, p_delta, p_rem)| {
                vec![(p_delta.clone(), vec![]), (p_rem.clone(), vec![])]
            })
            .collect();
        assert!(ZkPari::<E>::batch_verify(&proofs_and_inputs, &vk, &mut rng));

        for (sender_com, p_delta, p_rem) in &transfers {
            let sum = (p_delta.c_ci[0].into_group() + p_rem.c_ci[0].into_group()).into_affine();
            assert_eq!(sum, *sender_com);
        }

        let batch_ms = batch_start.elapsed().as_secs_f64() * 1000.0;

        println!(
            "   {num_transfers:>5} transfers │ indiv {indiv_ms:>9.1} ms ({:.3} ms/tx) │ batch {batch_ms:>9.1} ms ({:.3} ms/tx) │ {:.1}x",
            indiv_ms / num_transfers as f64,
            batch_ms / num_transfers as f64,
            indiv_ms / batch_ms,
        );
    }
    println!();

    // ── 7. Summary ───────────────────────────────────────────────────────
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Transfer complete. Validators verified:                      ║");
    println!("║    - Both amounts are non-negative (range proofs)             ║");
    println!("║    - Amounts are consistent with the sender's balance         ║");
    println!("║    - No amounts were revealed at any point                    ║");
    println!("║    - Batch verification gives significant speedup             ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
}
