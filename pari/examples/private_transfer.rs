//! Private transfers with hidden amounts using ZK-Pari.
//!
//! Demonstrates a Zether-like private payment system where:
//!   - Account balances are stored as Pedersen commitments
//!   - The Pari proof's T1 IS the Pedersen commitment (via witness_split=1)
//!   - Transfers are validated by range proofs + homomorphic commitment checks
//!
//! Run with: cargo run --example private_transfer -p pari

use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_relations::gr1cs::predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL;
use ark_relations::gr1cs::predicate::PredicateConstraintSystem;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, R1CS_PREDICATE_LABEL, SynthesisError,
};
use ark_relations::lc;
use ark_std::rand::SeedableRng;
use pari::data_structures::PedersenOpening;
use pari::Pari;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Range proof circuit (native SR1CS, identical to pari/src/test.rs)
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct RangeProofCircuit {
    value: Option<u64>,
}

impl<F: Field> ConstraintSynthesizer<F> for RangeProofCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let value = self.value;

        let v = cs.new_witness_variable(|| {
            let val = value.ok_or(SynthesisError::AssignmentMissing)?;
            let mut f = F::ZERO;
            let mut power = F::ONE;
            for i in 0..64u32 {
                if (val >> i) & 1 == 1 {
                    f += power;
                }
                power.double_in_place();
            }
            Ok(f)
        })?;

        let mut bit_vars = Vec::with_capacity(64);
        for i in 0..64u32 {
            let b = cs.new_witness_variable(|| {
                let val = value.ok_or(SynthesisError::AssignmentMissing)?;
                Ok(if (val >> i) & 1 == 1 { F::ONE } else { F::ZERO })
            })?;
            bit_vars.push(b);
        }

        let mut recon_minus_v = lc!() - v;
        let mut coeff = F::ONE;
        for &b in &bit_vars {
            recon_minus_v = recon_minus_v + (coeff, b);
            coeff.double_in_place();
        }
        let zero_lc = lc!() + v - v;
        cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;

        for &b in &bit_vars {
            cs.enforce_sr1cs_constraint(|| lc!() + b, || lc!() + b)?;
        }

        Ok(())
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
    opening: PedersenOpening<E::ScalarField>,
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    type E = Bn254;
    type Fr = <E as Pairing>::ScalarField;

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(2026_04_06);

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║       Private Transfers with Hidden Amounts (ZK-Pari)       ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ── 1. Trusted Setup ────────────────────────────────────────────────
    println!("1. Trusted Setup");
    println!("   Generating CRS for 64-bit range proof circuit (witness_split=1)...");

    let setup_start = Instant::now();
    let dummy_circuit = RangeProofCircuit { value: Some(0) };
    let (pk, vk) = Pari::<E>::keygen(dummy_circuit, 1, &mut rng);
    println!("   Done in {:.1} ms\n", setup_start.elapsed().as_secs_f64() * 1000.0);

    println!("   Pedersen commitment generators derived from CRS:");
    println!("     G_val  = Sigma1[0]            (value generator)");
    println!("     G_h    = (gamma/delta1)*G     (blinding generator)");
    println!();

    // ── 2. Account Creation (Deposits) ──────────────────────────────────
    println!("2. Account Creation");

    let alice_balance: u64 = 1000;
    let bob_balance: u64 = 500;

    let alice_opening = PedersenOpening::<Fr>::rand(&mut rng);
    let alice_com = pk.pedersen_commit(Fr::from(alice_balance), &alice_opening);

    let bob_opening = PedersenOpening::<Fr>::rand(&mut rng);
    let bob_com = pk.pedersen_commit(Fr::from(bob_balance), &bob_opening);

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

    println!("   Alice deposits {} tokens  =>  com_Alice = {:?}...", alice.balance, &format!("{:?}", alice.commitment)[..20]);
    println!("   Bob   deposits {} tokens  =>  com_Bob   = {:?}...\n", bob.balance, &format!("{:?}", bob.commitment)[..20]);

    // ── 3. Private Transfer: Alice → Bob ─────────────────────────────────
    let transfer_amount: u64 = 300;
    let remaining_balance: u64 = alice.balance - transfer_amount;

    println!("3. Private Transfer: Alice sends {} tokens to Bob", transfer_amount);
    println!("   (Validators see ONLY commitments and proofs, never amounts)\n");

    // 3a. Sender creates commitment to transfer amount
    let delta_opening = PedersenOpening::<Fr>::rand(&mut rng);
    let com_delta = pk.pedersen_commit(Fr::from(transfer_amount), &delta_opening);

    // 3b. Derive commitment to remaining balance via group subtraction
    let remaining_opening = &alice.opening - &delta_opening;
    let com_remaining: <E as Pairing>::G1Affine =
        (alice.commitment.into_group() - com_delta.into_group()).into_affine();

    // Sanity: the derived commitment should equal a fresh commit with the derived opening
    let com_remaining_check = pk.pedersen_commit(Fr::from(remaining_balance), &remaining_opening);
    assert_eq!(
        com_remaining, com_remaining_check,
        "Pedersen commitment homomorphism broken"
    );
    println!("   [ok] Commitment homomorphism verified: com_Alice = com_delta + com_remaining");

    // 3c. Prove transfer amount is in [0, 2^64)
    println!("   Proving transfer amount in range [0, 2^64)...");
    let prove_start = Instant::now();
    let proof_delta = Pari::<E>::prove_with_pedersen_opening(
        RangeProofCircuit { value: Some(transfer_amount) },
        &pk,
        &delta_opening,
        &mut rng,
    )
    .expect("range proof for transfer amount failed");
    let delta_prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

    // 3d. Prove remaining balance is in [0, 2^64)
    println!("   Proving remaining balance in range [0, 2^64)...");
    let prove_start = Instant::now();
    let proof_remaining = Pari::<E>::prove_with_pedersen_opening(
        RangeProofCircuit { value: Some(remaining_balance) },
        &pk,
        &remaining_opening,
        &mut rng,
    )
    .expect("range proof for remaining balance failed");
    let remaining_prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;
    println!("   Proving done: {:.1} ms + {:.1} ms\n", delta_prove_ms, remaining_prove_ms);

    // ── 4. Validator Checks ──────────────────────────────────────────────
    println!("4. Validator Checks (public, no secret knowledge needed)");

    // 4a. Verify both range proofs
    let verify_start = Instant::now();
    let delta_ok = Pari::<E>::verify(&proof_delta, &vk, &[]);
    let remaining_ok = Pari::<E>::verify(&proof_remaining, &vk, &[]);
    let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;

    println!("   Range proof (transfer amount) : {}", if delta_ok { "PASS" } else { "FAIL" });
    println!("   Range proof (remaining balance): {}", if remaining_ok { "PASS" } else { "FAIL" });
    assert!(delta_ok && remaining_ok);

    // 4b. Commitment consistency: proof.t_1 values must match the commitment decomposition
    assert_eq!(
        proof_delta.t_1, com_delta,
        "proof_delta.t_1 must equal com_delta"
    );
    assert_eq!(
        proof_remaining.t_1, com_remaining,
        "proof_remaining.t_1 must equal com_remaining"
    );
    println!("   proof_delta.t_1 == com_delta    : PASS");
    println!("   proof_remaining.t_1 == com_rem  : PASS");

    // 4c. Balance conservation: com_delta + com_remaining must equal the sender's old commitment
    let sum: <E as Pairing>::G1Affine =
        (proof_delta.t_1.into_group() + proof_remaining.t_1.into_group()).into_affine();
    assert_eq!(sum, alice.commitment, "balance conservation check failed");
    println!("   com_delta + com_remaining == com_Alice: PASS");
    println!("   Verification done: {:.1} ms\n", verify_ms);

    // ── 5. Update Ledger ─────────────────────────────────────────────────
    println!("5. Update Ledger");

    let old_alice_com = alice.commitment;
    let old_bob_com = bob.commitment;

    alice.balance = remaining_balance;
    alice.commitment = proof_remaining.t_1;
    alice.opening = remaining_opening;

    bob.balance += transfer_amount;
    bob.commitment = (bob.commitment.into_group() + proof_delta.t_1.into_group()).into_affine();
    bob.opening = PedersenOpening {
        zeta_1: bob.opening.zeta_1 + delta_opening.zeta_1,
    };

    // Verify updated commitments are consistent with the new balances
    let alice_com_check = pk.pedersen_commit(Fr::from(alice.balance), &alice.opening);
    let bob_com_check = pk.pedersen_commit(Fr::from(bob.balance), &bob.opening);
    assert_eq!(alice.commitment, alice_com_check);
    assert_eq!(bob.commitment, bob_com_check);

    println!("   Alice: {} tokens  (com changed: {})", alice.balance, old_alice_com != alice.commitment);
    println!("   Bob  : {} tokens  (com changed: {})\n", bob.balance, old_bob_com != bob.commitment);

    // ── 6. Summary ───────────────────────────────────────────────────────
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Transfer complete. Validators verified:                     ║");
    println!("║    - Both amounts are non-negative (range proofs)            ║");
    println!("║    - Amounts are consistent with the sender's balance        ║");
    println!("║    - No amounts were revealed at any point                   ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
}
