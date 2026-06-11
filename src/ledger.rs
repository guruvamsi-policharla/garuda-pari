//! Standalone Zether-style private-transfer ledger: a chain's block
//! processing hot path extracted as a library for profiling and optimization.
//!
//! This module mirrors the constantinople chain's private-transfer pipeline
//! (`crates/primitives/src/privacy.rs` plus the executor's `execute_body`
//! phases) without any of the chain harness around it: networking, consensus,
//! signatures, nonces, and the merkleized database are all out of scope. What
//! remains is exactly the cryptographic work a validator performs per block
//! of private transactions:
//!
//! 1. **decode** — deserialize transactions, validating every G1 point
//!    (canonical encoding, on-curve, prime-order subgroup). Points travel
//!    uncompressed so decoding pays no square root.
//! 2. **collect** — derive each proof's Fiat-Shamir aggregation challenge
//!    `theta` and assemble the batch-verification claims. The block-2
//!    commitment `com_theta = (1 - theta) * amount + theta * input` is a
//!    *derived tail*: it is never materialized, entering the batched check as
//!    MSM terms (see [`ZkPari::batch_verify_derived_tail`]).
//! 3. **verify** — one random-linear-combination batch verification of every
//!    proof in the block: a handful of size-`n` MSMs and a single 5-pairing
//!    product.
//! 4. **apply** — check each sender's declared commitment against ledger
//!    state, then update commitments homomorphically: transfers subtract the
//!    amount commitment from the sender's `private` and add it to the
//!    recipient's `pending`; funds and burns add/subtract a publicly
//!    computable `commit(value)`.
//!
//! Processing is all-or-nothing, like block verification on the chain: any
//! invalid transaction rejects the whole block and leaves the ledger
//! untouched.
//!
//! Known deltas from constantinople (cost attribution, not cost amount):
//! - Constantinople validates the two payload commitments at transaction
//!   decode and the three proof points at claim collection; here all five
//!   validate at decode. Same total work, different phase.
//! - Constantinople re-serializes a 48-byte compressed cache after every
//!   commitment update (its state codec); [`apply`](Ledger::process_block)
//!   here stops at the affine point.
//! - Public `u64` balances are not modeled: the chain additionally rejects
//!   funds exceeding the sender's public balance and burns overflowing it
//!   (two integer comparisons — no crypto cost).
//!
//! [`decode_block`] is the validating entry point: every point it returns is
//! subgroup-checked. Callers constructing [`Transaction`]s directly are
//! responsible for only using validated group elements (fixture-built blocks
//! are).
//!
//! # Fixtures
//!
//! [`Fixture`] builds valid blocks (honestly proven or trapdoor-simulated)
//! against a live ledger so the pipeline can be driven at any scale; see
//! `benches/ledger-block.rs` for a phase-by-phase cost breakdown.

use crate::data_structures::{CommittedInputOpening, Proof, ProvingKey, Trapdoor, VerifyingKey};
use crate::utils::transcript::IOPTranscript;
use crate::{ZkPari, ZkPariCircuit};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, Zero};
use ark_relations::gr1cs::{
    predicate::{polynomial_constraint::SR1CS_PREDICATE_LABEL, PredicateConstraintSystem},
    ConstraintSystemRef, SynthesisError, Variable, R1CS_PREDICATE_LABEL,
};
use ark_relations::lc;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::HashMap;
use ark_std::ops::Neg;
use ark_std::rand::RngCore;
use ark_std::vec::Vec;
use std::time::Instant;

/// One recipient per transfer: the batched circuit's `B`.
const BATCH_SIZE: usize = 1;

/// CRS block index of the payment basis ledger commitments live in (block 2
/// of the batched circuit: `[claimed values]`, then `[aggregate]`).
const LEDGER_BLOCK: usize = 1;

/// Fiat-Shamir domain for the aggregation challenge `theta`. Byte-identical
/// to constantinople's so transcripts can be cross-checked between the two.
const THETA_DOMAIN: &[u8] = b"constantinople-private-transfer-theta";

// ---------------------------------------------------------------------------
// Batched range circuit (B = 1), identical to constantinople's: range-checks
// the claimed amount and the remaining balance (block 1) and enforces the
// Horner aggregation `amount + theta * remaining = v_theta` against the
// block-2 committed aggregate, with `theta` a public input.
// ---------------------------------------------------------------------------

/// The one-recipient batched range circuit; public so callers can keygen
/// against the exact relation this module proves.
#[derive(Clone)]
pub struct BatchedRangeCircuit<F: Field> {
    pub theta: Option<F>,
    pub amount: Option<u64>,
    pub remaining: Option<u64>,
}

impl<F: Field> ZkPariCircuit<F> for BatchedRangeCircuit<F> {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let theta = self.theta;
        let raw_values: Option<[u64; BATCH_SIZE + 1]> = match (self.amount, self.remaining) {
            (Some(amount), Some(remaining)) => Some([amount, remaining]),
            _ => None,
        };
        let values: Option<Vec<F>> = raw_values
            .as_ref()
            .map(|raw| raw.iter().map(|v| F::from(*v)).collect());

        // Block 1 (committed inputs): amount, remaining.
        let mut value_vars = Vec::with_capacity(BATCH_SIZE + 1);
        for i in 0..=BATCH_SIZE {
            let vals = values.clone();
            let v = cs.new_witness_variable(move || {
                vals.ok_or(SynthesisError::AssignmentMissing).map(|v| v[i])
            })?;
            value_vars.push(v);
        }

        // Block 2 (single committed input): v_theta = amount + theta * remaining.
        let v_theta_value: Option<F> = match (values.as_ref(), theta) {
            (Some(vals), Some(th)) => Some(vals[0] + th * vals[1]),
            _ => None,
        };
        let v_theta_var =
            cs.new_witness_variable(|| v_theta_value.ok_or(SynthesisError::AssignmentMissing))?;

        // theta is an ordinary public input.
        let theta_var = cs.new_input_variable(|| theta.ok_or(SynthesisError::AssignmentMissing))?;

        // 64-bit range check for every committed value.
        for (i, &v) in value_vars.iter().enumerate() {
            let mut bit_vars = Vec::with_capacity(64);
            for bit in 0..64u32 {
                let raw = raw_values;
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
            for &b in &bit_vars {
                recon_minus_v = recon_minus_v + (coeff, b);
                coeff.double_in_place();
            }
            let zero_lc = lc!() + v - v;
            cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;
            for &b in &bit_vars {
                cs.enforce_sr1cs_constraint(|| lc!() + b, || lc!() + b)?;
            }
        }

        // Horner aggregation (identical to the chain's circuit, B = 1):
        // acc = remaining; acc = acc * theta + amount. Each product
        // acc * theta is enforced with two squares:
        //   (acc + theta)^2 = s_plus,  (acc - theta)^2 = s_minus,
        //   acc * theta = (s_plus - s_minus)/4
        let quarter = F::from(4u64).inverse().expect("4 is invertible");
        let mut acc_lc = lc!() + value_vars[BATCH_SIZE];
        let mut acc_val: Option<F> = values.as_ref().map(|vals| vals[BATCH_SIZE]);
        for i in (0..BATCH_SIZE).rev() {
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

        Ok(vec![value_vars, vec![v_theta_var]])
    }
}

// ---------------------------------------------------------------------------
// Parameters, commitments, theta
// ---------------------------------------------------------------------------

/// Proving/verifying keys (and the setup trapdoor, retained for cheap
/// simulated fixtures) for the one-recipient transfer relation.
pub struct LedgerParams<E: Pairing> {
    pub pk: ProvingKey<E>,
    pub vk: VerifyingKey<E>,
    pub trapdoor: Trapdoor<E>,
}

impl<E: Pairing> LedgerParams<E> {
    /// Runs the (demo-grade, trapdoor-retaining) setup for the transfer
    /// relation.
    pub fn setup(rng: &mut impl RngCore) -> Self {
        let circuit = BatchedRangeCircuit {
            theta: Some(E::ScalarField::from(7u64)),
            amount: Some(0),
            remaining: Some(0),
        };
        let (pk, vk, trapdoor) = ZkPari::<E>::keygen_with_trapdoor(circuit, rng);
        Self { pk, vk, trapdoor }
    }

    /// Pedersen commitment to `value` in the payment basis with the given
    /// blinding.
    pub fn commit_with(
        &self,
        value: u64,
        opening: &CommittedInputOpening<E::ScalarField>,
    ) -> E::G1Affine {
        self.pk
            .pedersen_commit(LEDGER_BLOCK, &[E::ScalarField::from(value)], opening)
    }

    /// Publicly computable commitment to `value` (zero blinding): what funds
    /// and burns move between the public and private sides.
    pub fn commit(&self, value: u64) -> E::G1Affine {
        self.commit_with(value, &CommittedInputOpening::zero())
    }

    /// The zero commitment (identity point): a never-touched account state.
    pub fn zero_commitment(&self) -> E::G1Affine {
        E::G1Affine::zero()
    }
}

/// Fiat-Shamir aggregation challenge bound to everything an adversary could
/// vary before it is drawn: the sender's declared commitment, the amount
/// commitment, and the block-1 commitment to the claimed values.
///
/// This binding is load-bearing for the derived-tail batch verification:
/// `theta` enters the proof-system challenge as the public input, and
/// `com_theta` is a deterministic function of `(theta, input, amount)`, so the
/// derived commitment is fixed before the challenge is revealed.
pub fn derive_theta<E: Pairing>(
    input: &E::G1Affine,
    amount: &E::G1Affine,
    c_ci_1: &E::G1Affine,
) -> E::ScalarField {
    let mut transcript = IOPTranscript::<E::ScalarField>::new(THETA_DOMAIN);
    let _ = transcript.append_serializable_element(b"com_sender", input);
    let _ = transcript.append_serializable_element(b"com_amount", amount);
    let _ = transcript.append_serializable_element(b"c_ci_1", c_ci_1);
    transcript
        .get_and_append_challenge(b"theta")
        .expect("transcript challenge")
}

// ---------------------------------------------------------------------------
// Transactions
// ---------------------------------------------------------------------------

/// Account identifier. The chain uses 32-byte account keys; a u64 keeps the
/// hash-map cost profile while staying simple.
pub type AccountId = u64;

/// The transmitted proof material: `3 G1 + 1 F`, points uncompressed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferProof<E: Pairing> {
    pub c_ci_1: E::G1Affine,
    pub t_g: E::G1Affine,
    pub u_g: E::G1Affine,
    pub v_a: E::ScalarField,
}

/// One private-side transaction, as the chain's executor sees it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transaction<E: Pairing> {
    /// Moves `value` from the (untracked) public balance into the sender's
    /// private commitment. Publicly computable; needs no proof.
    Fund {
        sender: AccountId,
        value: u64,
        /// The sender's declared current private commitment (chain check).
        sender_commitment: E::G1Affine,
    },
    /// Confidential transfer: the amount commitment moves from the sender's
    /// `private` to the recipient's `pending`.
    Transfer {
        sender: AccountId,
        recipient: AccountId,
        sender_commitment: E::G1Affine,
        amount_commitment: E::G1Affine,
        proof: TransferProof<E>,
    },
    /// Moves `value` back to the public side; reuses the transfer proof to
    /// range-check the remaining balance (the "amount" is `commit(value)`).
    Burn {
        sender: AccountId,
        value: u64,
        sender_commitment: E::G1Affine,
        proof: TransferProof<E>,
    },
}

const TAG_FUND: u8 = 0;
const TAG_TRANSFER: u8 = 1;
const TAG_BURN: u8 = 2;

/// Why a block was rejected.
#[derive(Debug, Clone, PartialEq, Eq, displaydoc::Display)]
pub enum LedgerError {
    /// malformed block bytes
    Malformed,
    /// invalid group element encoding (non-canonical, off-curve, or outside the prime-order subgroup)
    InvalidPoint,
    /// degenerate aggregation challenge
    DegenerateTheta,
    /// batched proof verification failed
    InvalidProof,
    /// account {0} declared a commitment that does not match ledger state
    CommitmentMismatch(AccountId),
}

fn write_point<E: Pairing>(out: &mut Vec<u8>, point: &E::G1Affine) {
    point
        .serialize_uncompressed(&mut *out)
        .expect("serialization into a Vec cannot fail");
}

/// Validated read: canonical encoding, on-curve, and prime-order subgroup.
/// This validation is load-bearing — these points later enter unchecked MSMs
/// and the pairing.
fn read_point<E: Pairing>(bytes: &mut &[u8]) -> Result<E::G1Affine, LedgerError> {
    E::G1Affine::deserialize_uncompressed(bytes).map_err(|_| LedgerError::InvalidPoint)
}

fn write_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn read_u64(bytes: &mut &[u8]) -> Result<u64, LedgerError> {
    if bytes.len() < 8 {
        return Err(LedgerError::Malformed);
    }
    let (head, rest) = bytes.split_at(8);
    *bytes = rest;
    Ok(u64::from_le_bytes(head.try_into().expect("8 bytes")))
}

impl<E: Pairing> TransferProof<E> {
    fn write(&self, out: &mut Vec<u8>) {
        write_point::<E>(out, &self.c_ci_1);
        write_point::<E>(out, &self.t_g);
        write_point::<E>(out, &self.u_g);
        self.v_a
            .serialize_compressed(&mut *out)
            .expect("serialization into a Vec cannot fail");
    }

    fn read(bytes: &mut &[u8]) -> Result<Self, LedgerError> {
        Ok(Self {
            c_ci_1: read_point::<E>(bytes)?,
            t_g: read_point::<E>(bytes)?,
            u_g: read_point::<E>(bytes)?,
            v_a: E::ScalarField::deserialize_compressed(&mut *bytes)
                .map_err(|_| LedgerError::Malformed)?,
        })
    }
}

/// Serializes a block of transactions (length-prefixed).
pub fn encode_block<E: Pairing>(transactions: &[Transaction<E>]) -> Vec<u8> {
    let mut out = Vec::new();
    write_u64(&mut out, transactions.len() as u64);
    for transaction in transactions {
        match transaction {
            Transaction::Fund {
                sender,
                value,
                sender_commitment,
            } => {
                out.push(TAG_FUND);
                write_u64(&mut out, *sender);
                write_u64(&mut out, *value);
                write_point::<E>(&mut out, sender_commitment);
            }
            Transaction::Transfer {
                sender,
                recipient,
                sender_commitment,
                amount_commitment,
                proof,
            } => {
                out.push(TAG_TRANSFER);
                write_u64(&mut out, *sender);
                write_u64(&mut out, *recipient);
                write_point::<E>(&mut out, sender_commitment);
                write_point::<E>(&mut out, amount_commitment);
                proof.write(&mut out);
            }
            Transaction::Burn {
                sender,
                value,
                sender_commitment,
                proof,
            } => {
                out.push(TAG_BURN);
                write_u64(&mut out, *sender);
                write_u64(&mut out, *value);
                write_point::<E>(&mut out, sender_commitment);
                proof.write(&mut out);
            }
        }
    }
    out
}

/// Deserializes a block, validating every group element (the **decode**
/// phase: per transfer, five subgroup-checked uncompressed point reads).
pub fn decode_block<E: Pairing>(mut bytes: &[u8]) -> Result<Vec<Transaction<E>>, LedgerError> {
    let count = read_u64(&mut bytes)? as usize;
    // Each transaction is at least a fund (tag + two u64s + one point); cap
    // the allocation against malformed length prefixes.
    let min_transaction = 17 + E::G1Affine::zero().uncompressed_size();
    if count > bytes.len() / min_transaction + 1 {
        return Err(LedgerError::Malformed);
    }
    let mut transactions = Vec::with_capacity(count);
    for _ in 0..count {
        let (tag, rest) = bytes.split_first().ok_or(LedgerError::Malformed)?;
        bytes = rest;
        let transaction = match *tag {
            TAG_FUND => Transaction::Fund {
                sender: read_u64(&mut bytes)?,
                value: read_u64(&mut bytes)?,
                sender_commitment: read_point::<E>(&mut bytes)?,
            },
            TAG_TRANSFER => Transaction::Transfer {
                sender: read_u64(&mut bytes)?,
                recipient: read_u64(&mut bytes)?,
                sender_commitment: read_point::<E>(&mut bytes)?,
                amount_commitment: read_point::<E>(&mut bytes)?,
                proof: TransferProof::read(&mut bytes)?,
            },
            TAG_BURN => Transaction::Burn {
                sender: read_u64(&mut bytes)?,
                value: read_u64(&mut bytes)?,
                sender_commitment: read_point::<E>(&mut bytes)?,
                proof: TransferProof::read(&mut bytes)?,
            },
            _ => return Err(LedgerError::Malformed),
        };
        transactions.push(transaction);
    }
    if !bytes.is_empty() {
        return Err(LedgerError::Malformed);
    }
    Ok(transactions)
}

// ---------------------------------------------------------------------------
// Ledger state and block processing
// ---------------------------------------------------------------------------

/// Per-account commitment state. Incoming transfers accumulate in `pending`
/// (the Zether anti-griefing split); only an account's own transactions move
/// `private`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountState<E: Pairing> {
    pub private: E::G1Affine,
    pub pending: E::G1Affine,
}

impl<E: Pairing> Default for AccountState<E> {
    fn default() -> Self {
        Self {
            private: E::G1Affine::zero(),
            pending: E::G1Affine::zero(),
        }
    }
}

/// Wall-clock per phase of [`Ledger::process_block_timed`].
#[derive(Debug, Clone, Copy, Default)]
pub struct PhaseTimings {
    pub collect_us: u128,
    pub verify_us: u128,
    pub apply_us: u128,
}

/// The committed account states the chain would hold in its merkleized
/// database.
#[derive(Clone, Debug, Default)]
pub struct Ledger<E: Pairing> {
    pub accounts: HashMap<AccountId, AccountState<E>>,
}

/// `a + b` in affine, mirroring the chain's per-update cost exactly: full
/// projective+projective addition followed by normalization (one field
/// inversion per operation).
fn g1_add<E: Pairing>(a: &E::G1Affine, b: &E::G1Affine) -> E::G1Affine {
    (a.into_group() + b.into_group()).into_affine()
}

/// `a - b` in affine.
fn g1_sub<E: Pairing>(a: &E::G1Affine, b: &E::G1Affine) -> E::G1Affine {
    (a.into_group() - b.into_group()).into_affine()
}

impl<E: Pairing> Ledger<E> {
    pub fn new() -> Self {
        Self {
            accounts: HashMap::new(),
        }
    }

    /// Assembles the batch-verification claims for every proof-carrying
    /// transaction (the **collect** phase): per claim, one theta transcript
    /// plus the derived-tail MSM terms
    /// `com_theta = (1 - theta) * amount + theta * input`.
    ///
    /// Burns materialize their public amount commitment `commit(value)` here,
    /// mirroring the chain.
    #[allow(clippy::type_complexity)]
    pub fn collect_claims(
        params: &LedgerParams<E>,
        transactions: &[Transaction<E>],
    ) -> Result<
        (
            Vec<(Proof<E>, Vec<E::ScalarField>)>,
            Vec<Vec<(E::G1Affine, E::ScalarField)>>,
        ),
        LedgerError,
    > {
        let mut proofs = Vec::with_capacity(transactions.len());
        let mut derived = Vec::with_capacity(transactions.len());
        for transaction in transactions {
            let (input, amount, proof) = match transaction {
                Transaction::Fund { .. } => continue,
                Transaction::Transfer {
                    sender_commitment,
                    amount_commitment,
                    proof,
                    ..
                } => (sender_commitment, *amount_commitment, proof),
                Transaction::Burn {
                    sender_commitment,
                    value,
                    proof,
                    ..
                } => (sender_commitment, params.commit(*value), proof),
            };
            let theta = derive_theta::<E>(input, &amount, &proof.c_ci_1);
            // Defense-in-depth: degenerate challenges collapse the Horner
            // aggregation; a 192-bit hash never produces them honestly.
            if theta.is_zero() || theta.is_one() {
                return Err(LedgerError::DegenerateTheta);
            }
            proofs.push((
                Proof {
                    c_ci: vec![proof.c_ci_1],
                    t_g: proof.t_g,
                    u_g: proof.u_g,
                    v_a: proof.v_a,
                },
                vec![theta],
            ));
            derived.push(vec![
                (amount, E::ScalarField::one() - theta),
                (*input, theta),
            ]);
        }
        Ok((proofs, derived))
    }

    /// Checks declared sender commitments against ledger state and applies
    /// every update (the **apply** phase). All-or-nothing: on any mismatch
    /// the ledger is left untouched.
    pub fn apply(
        &mut self,
        params: &LedgerParams<E>,
        transactions: &[Transaction<E>],
    ) -> Result<(), LedgerError> {
        // Overlay mirrors the chain's speculative execution: state mutates in
        // a scratch map and commits only if the whole block is valid.
        let mut overlay: HashMap<AccountId, AccountState<E>> = HashMap::new();
        {
            let read = |overlay: &HashMap<AccountId, AccountState<E>>, id: &AccountId| {
                overlay
                    .get(id)
                    .or_else(|| self.accounts.get(id))
                    .cloned()
                    .unwrap_or_default()
            };
            for transaction in transactions {
                match transaction {
                    Transaction::Fund {
                        sender,
                        value,
                        sender_commitment,
                    } => {
                        let mut account = read(&overlay, sender);
                        if account.private != *sender_commitment {
                            return Err(LedgerError::CommitmentMismatch(*sender));
                        }
                        account.private = g1_add::<E>(&account.private, &params.commit(*value));
                        overlay.insert(*sender, account);
                    }
                    Transaction::Transfer {
                        sender,
                        recipient,
                        sender_commitment,
                        amount_commitment,
                        ..
                    } => {
                        let mut account = read(&overlay, sender);
                        if account.private != *sender_commitment {
                            return Err(LedgerError::CommitmentMismatch(*sender));
                        }
                        account.private = g1_sub::<E>(&account.private, amount_commitment);
                        overlay.insert(*sender, account);
                        let mut recipient_account = read(&overlay, recipient);
                        recipient_account.pending =
                            g1_add::<E>(&recipient_account.pending, amount_commitment);
                        overlay.insert(*recipient, recipient_account);
                    }
                    Transaction::Burn {
                        sender,
                        value,
                        sender_commitment,
                        ..
                    } => {
                        let mut account = read(&overlay, sender);
                        if account.private != *sender_commitment {
                            return Err(LedgerError::CommitmentMismatch(*sender));
                        }
                        account.private = g1_sub::<E>(&account.private, &params.commit(*value));
                        overlay.insert(*sender, account);
                    }
                }
            }
        }
        self.accounts.extend(overlay);
        Ok(())
    }

    /// Processes one block: collect claims, batch-verify every proof, then
    /// check commitment chains and apply the updates. Mirrors the chain's
    /// `execute_body` ordering. Returns an error (ledger untouched) if
    /// anything is invalid.
    pub fn process_block(
        &mut self,
        params: &LedgerParams<E>,
        transactions: &[Transaction<E>],
        rng: &mut impl RngCore,
    ) -> Result<(), LedgerError>
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        self.process_block_timed(params, transactions, rng)
            .map(|_| ())
    }

    /// [`Self::process_block`] with per-phase wall-clock timings, for
    /// profiling.
    pub fn process_block_timed(
        &mut self,
        params: &LedgerParams<E>,
        transactions: &[Transaction<E>],
        rng: &mut impl RngCore,
    ) -> Result<PhaseTimings, LedgerError>
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let mut timings = PhaseTimings::default();

        let started = Instant::now();
        let (proofs, derived) = Self::collect_claims(params, transactions)?;
        timings.collect_us = started.elapsed().as_micros();

        let started = Instant::now();
        if !proofs.is_empty()
            && !ZkPari::<E>::batch_verify_derived_tail(&proofs, &derived, &params.vk, rng)
        {
            return Err(LedgerError::InvalidProof);
        }
        timings.verify_us = started.elapsed().as_micros();

        let started = Instant::now();
        self.apply(params, transactions)?;
        timings.apply_us = started.elapsed().as_micros();

        Ok(timings)
    }
}

// ---------------------------------------------------------------------------
// Client-side balances and block fixtures
// ---------------------------------------------------------------------------

/// A client's secret view of its private balance: plaintext value plus the
/// Pedersen opening. Spending requires both.
#[derive(Clone, Debug)]
pub struct ClientBalance<E: Pairing> {
    value: u64,
    opening: CommittedInputOpening<E::ScalarField>,
}

impl<E: Pairing> ClientBalance<E> {
    pub fn empty() -> Self {
        Self {
            value: 0,
            opening: CommittedInputOpening::zero(),
        }
    }

    pub fn value(&self) -> u64 {
        self.value
    }

    pub fn commitment(&self, params: &LedgerParams<E>) -> E::G1Affine {
        params.commit_with(self.value, &self.opening)
    }

    /// Funding adds a zero-blinding public commitment: value moves, the
    /// opening is unchanged.
    pub fn fund(&mut self, value: u64) {
        self.value = self
            .value
            .checked_add(value)
            .expect("client balance must stay within the 64-bit range invariant");
    }

    /// Splits off `amount` with fresh blinding, leaving the remainder. The
    /// homomorphic relationship `input = amount_com + remaining_com` pins the
    /// remaining opening to `opening - r_amount`.
    #[allow(clippy::type_complexity)]
    fn split(
        &mut self,
        amount: u64,
        rng: &mut impl RngCore,
    ) -> Option<(
        CommittedInputOpening<E::ScalarField>,
        u64,
        CommittedInputOpening<E::ScalarField>,
    )> {
        if amount > self.value {
            return None;
        }
        let r_amount = CommittedInputOpening::<E::ScalarField>::rand(rng);
        let remaining = self.value - amount;
        let r_remaining = CommittedInputOpening {
            rho: self.opening.rho - r_amount.rho,
        };
        self.value = remaining;
        self.opening = r_remaining.clone();
        Some((r_amount, remaining, r_remaining))
    }
}

/// Builds the transmitted proof for a transfer/burn, honestly or via the
/// setup trapdoor (simulation: cheap fixtures for load generation; transcript
/// distribution matches honest proofs).
#[allow(clippy::too_many_arguments)]
fn build_proof<E: Pairing>(
    params: &LedgerParams<E>,
    input: &E::G1Affine,
    amount: u64,
    amount_com: &E::G1Affine,
    r_amount: &CommittedInputOpening<E::ScalarField>,
    remaining: u64,
    r_remaining: &CommittedInputOpening<E::ScalarField>,
    simulate: bool,
    rng: &mut impl RngCore,
) -> TransferProof<E> {
    let rho_1 = CommittedInputOpening::<E::ScalarField>::rand(rng);
    let c_ci_1 = params.pk.pedersen_commit(
        0,
        &[
            E::ScalarField::from(amount),
            E::ScalarField::from(remaining),
        ],
        &rho_1,
    );
    let theta = derive_theta::<E>(input, amount_com, &c_ci_1);

    let proof = if simulate {
        // com_theta = (1 - theta) * amount + theta * input, materialized only
        // here (the verifier folds it as MSM terms instead).
        let com_theta = (amount_com.into_group() * (E::ScalarField::one() - theta)
            + input.into_group() * theta)
            .into_affine();
        ZkPari::<E>::simulate_derived(
            &params.trapdoor,
            &params.vk,
            &[c_ci_1, com_theta],
            &[theta],
            1,
            rng,
        )
    } else {
        let rho_2 = CommittedInputOpening {
            rho: r_amount.rho + theta * r_remaining.rho,
        };
        ZkPari::<E>::prove_with_openings_derived(
            BatchedRangeCircuit {
                theta: Some(theta),
                amount: Some(amount),
                remaining: Some(remaining),
            },
            &params.pk,
            &[rho_1, rho_2],
            1,
            rng,
        )
        .expect("range proof synthesis cannot fail for in-range values")
    };

    TransferProof {
        c_ci_1: proof.c_ci[0],
        t_g: proof.t_g,
        u_g: proof.u_g,
        v_a: proof.v_a,
    }
}

/// A self-consistent world: a ledger plus the client-side secrets needed to
/// keep producing valid blocks against it.
pub struct Fixture<'a, E: Pairing> {
    pub params: &'a LedgerParams<E>,
    pub ledger: Ledger<E>,
    clients: Vec<ClientBalance<E>>,
}

impl<'a, E: Pairing> Fixture<'a, E> {
    /// `accounts` accounts, each pre-funded with `balance` (both the ledger
    /// commitments and the client openings reflect it).
    pub fn new(params: &'a LedgerParams<E>, accounts: usize, balance: u64) -> Self {
        let mut ledger = Ledger::new();
        let mut clients = Vec::with_capacity(accounts);
        for id in 0..accounts as u64 {
            let mut client = ClientBalance::empty();
            client.fund(balance);
            ledger.accounts.insert(
                id,
                AccountState {
                    private: client.commitment(params),
                    pending: E::G1Affine::zero(),
                },
            );
            clients.push(client);
        }
        Self {
            params,
            ledger,
            clients,
        }
    }

    /// Builds one valid block: every account transfers `amount` to its ring
    /// neighbor (`simulate` switches between honest proofs and trapdoor
    /// simulation). Client state advances; the ledger advances only when the
    /// caller processes the block, so each block must be processed (or the
    /// fixture discarded) before building the next.
    pub fn transfer_block(
        &mut self,
        amount: u64,
        simulate: bool,
        rng: &mut impl RngCore,
    ) -> Vec<Transaction<E>> {
        let n = self.clients.len();
        let mut transactions = Vec::with_capacity(n);
        for sender in 0..n {
            let input = self.clients[sender].commitment(self.params);
            let (r_amount, remaining, r_remaining) = self.clients[sender]
                .split(amount, rng)
                .expect("fixture accounts hold enough balance");
            let amount_com = self.params.commit_with(amount, &r_amount);
            let proof = build_proof(
                self.params,
                &input,
                amount,
                &amount_com,
                &r_amount,
                remaining,
                &r_remaining,
                simulate,
                rng,
            );
            transactions.push(Transaction::Transfer {
                sender: sender as u64,
                recipient: ((sender + 1) % n) as u64,
                sender_commitment: input,
                amount_commitment: amount_com,
                proof,
            });
        }
        transactions
    }

    /// Builds one valid burn from `sender`.
    pub fn burn(
        &mut self,
        sender: AccountId,
        value: u64,
        simulate: bool,
        rng: &mut impl RngCore,
    ) -> Transaction<E> {
        let client = &mut self.clients[sender as usize];
        let input = client.commitment(self.params);
        // A burn's "amount" is the public commit(value): zero blinding.
        let remaining = client
            .value
            .checked_sub(value)
            .expect("fixture burn must not exceed the client balance");
        let r_remaining = client.opening.clone();
        client.value = remaining;
        let amount_com = self.params.commit(value);
        let proof = build_proof(
            self.params,
            &input,
            value,
            &amount_com,
            &CommittedInputOpening::zero(),
            remaining,
            &r_remaining,
            simulate,
            rng,
        );
        Transaction::Burn {
            sender,
            value,
            sender_commitment: input,
            proof,
        }
    }

    /// Builds one fund for `sender`.
    pub fn fund(&mut self, sender: AccountId, value: u64) -> Transaction<E> {
        let client = &mut self.clients[sender as usize];
        let input = client.commitment(self.params);
        client.fund(value);
        Transaction::Fund {
            sender,
            value,
            sender_commitment: input,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Bn254;
    use ark_std::test_rng;

    type E = Bn254;

    use ark_std::sync::OnceLock;

    fn params() -> &'static LedgerParams<E> {
        static PARAMS: OnceLock<LedgerParams<E>> = OnceLock::new();
        PARAMS.get_or_init(|| LedgerParams::<E>::setup(&mut test_rng()))
    }

    fn fixture(accounts: usize) -> Fixture<'static, E> {
        Fixture::new(params(), accounts, 1_000)
    }

    #[test]
    fn simulated_block_roundtrips_and_updates_commitments() {
        let mut rng = test_rng();
        let mut fixture = fixture(4);

        let block = fixture.transfer_block(25, true, &mut rng);
        let bytes = encode_block(&block);
        let decoded = decode_block::<E>(&bytes).expect("decode");
        assert_eq!(decoded, block);

        fixture
            .ledger
            .process_block(fixture.params, &decoded, &mut rng)
            .expect("valid block");

        // Sender commitments advanced to the clients' new openings; pending
        // accumulated one amount commitment per recipient.
        for (id, client) in fixture.clients.iter().enumerate() {
            let account = &fixture.ledger.accounts[&(id as u64)];
            assert_eq!(account.private, client.commitment(fixture.params));
            assert_ne!(account.pending, <E as Pairing>::G1Affine::zero());
        }

        // A second chained block (different blinding) also processes.
        let second = fixture.transfer_block(10, true, &mut rng);
        fixture
            .ledger
            .process_block(fixture.params, &second, &mut rng)
            .expect("chained block");
    }

    #[test]
    fn honest_proofs_also_verify() {
        let mut rng = test_rng();
        let mut fixture = fixture(2);
        let block = fixture.transfer_block(7, false, &mut rng);
        fixture
            .ledger
            .process_block(fixture.params, &block, &mut rng)
            .expect("honest block");
    }

    #[test]
    fn funds_and_burns_apply() {
        let mut rng = test_rng();
        let mut fixture = fixture(2);

        let block = vec![fixture.fund(0, 50), fixture.burn(1, 100, true, &mut rng)];
        fixture
            .ledger
            .process_block(fixture.params, &block, &mut rng)
            .expect("fund + burn block");
        assert_eq!(
            fixture.ledger.accounts[&0].private,
            fixture.clients[0].commitment(fixture.params)
        );
        assert_eq!(
            fixture.ledger.accounts[&1].private,
            fixture.clients[1].commitment(fixture.params)
        );
    }

    #[test]
    fn tampered_amount_rejects_block_and_preserves_state() {
        let mut rng = test_rng();
        let mut fixture = fixture(3);
        let before = fixture.ledger.clone();

        let mut block = fixture.transfer_block(25, true, &mut rng);
        if let Transaction::Transfer {
            amount_commitment, ..
        } = &mut block[1]
        {
            *amount_commitment = g1_add::<E>(amount_commitment, &fixture.params.commit(1));
        }
        assert_eq!(
            fixture
                .ledger
                .process_block(fixture.params, &block, &mut rng),
            Err(LedgerError::InvalidProof)
        );
        assert_eq!(fixture.ledger.accounts, before.accounts);
    }

    #[test]
    fn stale_sender_commitment_is_a_chain_mismatch() {
        let mut rng = test_rng();
        let mut fixture = fixture(3);

        // A block whose proofs are valid for their declared inputs, applied
        // against a ledger whose account 0 has since moved: proofs verify,
        // the chain check rejects, the ledger is untouched.
        let block = fixture.transfer_block(25, true, &mut rng);
        let moved = g1_add::<E>(
            &fixture.ledger.accounts[&0].private,
            &fixture.params.commit(1),
        );
        fixture.ledger.accounts.get_mut(&0).expect("exists").private = moved;
        let before = fixture.ledger.clone();

        assert_eq!(
            fixture
                .ledger
                .process_block(fixture.params, &block, &mut rng),
            Err(LedgerError::CommitmentMismatch(0))
        );
        assert_eq!(fixture.ledger.accounts, before.accounts);
    }

    #[test]
    fn malformed_points_are_rejected_at_decode() {
        let mut rng = test_rng();
        let mut fixture = fixture(2);
        let block = fixture.transfer_block(5, true, &mut rng);
        let mut bytes = encode_block(&block);
        // Corrupt a byte inside the first transmitted point.
        bytes[8 + 8 + 1 + 8 + 8 + 3] ^= 0xFF;
        assert!(matches!(
            decode_block::<E>(&bytes),
            Err(LedgerError::InvalidPoint) | Err(LedgerError::Malformed)
        ));
    }
}
