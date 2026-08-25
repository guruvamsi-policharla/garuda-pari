//! The private-transfer circuits from the paper (R_send, R_recv) and their
//! Poseidon/Merkle building blocks.
//!
//! Account commitments are Poseidon values opened in-circuit as public
//! inputs, so these proofs carry **zero** committed-input blocks (2 G1 + 1 F
//! on the wire, 3 pairings to verify); wrap the circuits in
//! `zkpari::Uncommitted` for keygen/prove.
//!
//! The per-account nullifier/tag trees are *user-maintained* indexed Merkle
//! trees; the ledger stores only their 32-byte roots, and the insertion
//! proof `pi_mt` is verified **in-circuit** (`indexed.rs`) rather than
//! natively — the statement carries (root, root') and the ledger just
//! compares-and-swaps. Batch verification cost is independent of circuit
//! size, so this removes both the per-transaction native hashing and the
//! ~depth x 32 B insertion proof from the wire at zero marginal ledger
//! cost. What stays native: the ledger's root-history check on the revealed
//! receipt anchor (rootrho in the W most recent roots) and receiver
//! registration.

pub mod indexed;
pub mod merkle;
pub mod poseidon;
pub mod recv;
pub mod send;

use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};

use super::Fr;

/// Enforce `var` in [0, 2^64) by allocating its 64 bits (from the native
/// `value`) and constraining their recomposition to equal `var`.
/// 64 boolean constraints + 1 packing constraint.
pub fn enforce_range_64(
    cs: ConstraintSystemRef<Fr>,
    var: &FpVar<Fr>,
    value: u64,
) -> Result<(), SynthesisError> {
    let bits = (0..64)
        .map(|i| Boolean::new_witness(cs.clone(), || Ok((value >> i) & 1 == 1)))
        .collect::<Result<Vec<_>, _>>()?;
    Boolean::le_bits_to_fp(&bits)?.enforce_equal(var)
}

/// Enforce `var` in [0, 2^n), bits taken from the native `value`.
pub fn enforce_range_bits(
    cs: ConstraintSystemRef<Fr>,
    var: &FpVar<Fr>,
    value: Fr,
    n: usize,
) -> Result<(), SynthesisError> {
    let big = value.into_bigint();
    let bits = (0..n)
        .map(|i| Boolean::new_witness(cs.clone(), || Ok(big.get_bit(i))))
        .collect::<Result<Vec<_>, _>>()?;
    Boolean::le_bits_to_fp(&bits)?.enforce_equal(var)
}

/// Enforce `a < b`, given both are already range-constrained below 2^128
/// (`b` may be exactly 2^128): witnesses the bits of `b - a - 1` in
/// [0, 2^128), which exists iff a < b.
pub fn enforce_lt_128(
    cs: ConstraintSystemRef<Fr>,
    a: &FpVar<Fr>,
    a_val: Fr,
    b: &FpVar<Fr>,
    b_val: Fr,
) -> Result<(), SynthesisError> {
    let diff = b - a - FpVar::Constant(Fr::one());
    enforce_range_bits(cs, &diff, b_val - a_val - Fr::one(), 128)
}
