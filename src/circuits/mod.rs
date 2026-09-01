//! The private-payment circuits from the paper (R_send, R_recv, R_op) and
//! their hash/Merkle building blocks, instantiated over BLS12-381.
//!
//! Every hash goes through [`hasher`]: Pedersen over Jubjub for Merkle
//! nodes, indexed leaves, and commitments; SHA-256 for the single nullifier
//! CRPRF.
//!
//! Account commitments are hash values opened in-circuit as public inputs,
//! so a proof is the bare `2 G1 + 1 F` and verification is 3 pairings.
//!
//! R_send ([`send`]) is hash-light: three Pedersen commitment openings and
//! range checks, nothing else. All tree work lives in R_recv ([`recv`]): the
//! nullifier is derived in-circuit from the receipt's MMR position under the
//! receiver's committed key and inserted into the receiver's
//! *user-maintained* indexed nullifier tree ([`indexed`]). The tree root
//! lives *inside* the account commitment, so an account's entire public
//! state is one commitment; the insertion proof `pi_mt` is verified
//! **in-circuit** rather than natively, and the ledger just
//! compare-and-swaps the commitment. R_op ([`op`]) is the paper's
//! operation-hiding relation: a witness-selected OR of the send and receive
//! branches over the shared statement `(A, com, com', rho, root_rho)`, so an
//! observer cannot tell sends from receives.
//!
//! What stays native: the ledger's root-history check on the revealed
//! receipt anchor (root_rho in the W most recent roots) and registration
//! (R_reg is a Schnorr-style proof of the account signing key, outside the
//! SNARK).

pub mod hasher;
pub mod indexed;
pub mod merkle;
pub mod op;
pub mod recv;
pub mod send;

#[cfg(test)]
mod tests;

use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};

/// The scalar field the circuits are written over (BLS12-381; the Pedersen
/// hash lives on Jubjub, whose base field this is).
pub type Fr = ark_bls12_381::Fr;

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