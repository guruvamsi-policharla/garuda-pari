//! Poseidon instantiation shared by all private-transfer primitives.
//!
//! One sponge configuration (BLS12-381 Fr, width 5 = rate 4 + capacity 1,
//! alpha = 5, 8 full / 60 partial rounds) covers every hash in the scheme:
//!
//!   Com_acct(b, kappa; r)                = H(DOM_ACCT, b, kappa, r)
//!   CRPRF_kappa(pay, Sen, zeta)          = H(DOM_PAY,  kappa, Sen, zeta)
//!   CRPRF_kappa(pad, Sen, zeta)          = H(DOM_PAD,  kappa, Sen, zeta)
//!   Com_rec(v, Sen, Rec, nullifier; r'') = H(DOM_REC,  v, Sen, Rec, nullifier, r'')
//!   Merkle node                          = H(DOM_NODE, left, right)
//!
//! Poseidon commitments hide because the trailing argument is a uniformly
//! random field element; domain tags keep the five uses of the permutation
//! from colliding. Rate 4 means every absorb of at most 4 elements costs one
//! permutation, so only Com_rec (6 elements) pays for two.

use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_crypto_primitives::sponge::poseidon::{
    find_poseidon_ark_and_mds, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{CryptographicSponge, FieldBasedCryptographicSponge};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};

use super::super::Fr;

/// Domain-separation tags, absorbed as the first sponge element.
pub const DOM_ACCT: u64 = 1;
pub const DOM_PAY: u64 = 2;
pub const DOM_PAD: u64 = 3;
pub const DOM_REC: u64 = 4;
pub const DOM_NODE: u64 = 5;
/// Indexed-tree leaf: `H(DOM_ILEAF, value, next_value, next_index)`.
pub const DOM_ILEAF: u64 = 6;

const RATE: usize = 4;
const CAPACITY: usize = 1;
const FULL_ROUNDS: usize = 8;
const PARTIAL_ROUNDS: usize = 60;
const ALPHA: u64 = 5;

/// The single Poseidon configuration used everywhere (parameters from the
/// Grain LFSR, as in the Poseidon reference implementation).
pub fn poseidon_config() -> PoseidonConfig<Fr> {
    let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(
        255, // modulus bits of BLS12-381 Fr
        RATE,
        FULL_ROUNDS as u64,
        PARTIAL_ROUNDS as u64,
        0,
    );
    PoseidonConfig::new(FULL_ROUNDS, PARTIAL_ROUNDS, ALPHA, mds, ark, RATE, CAPACITY)
}

/// Native hash: absorb `dom` then `inputs`, squeeze one field element.
pub fn hash(cfg: &PoseidonConfig<Fr>, dom: u64, inputs: &[Fr]) -> Fr {
    let mut sponge = PoseidonSponge::new(cfg);
    sponge.absorb(&Fr::from(dom));
    sponge.absorb(&inputs.to_vec());
    sponge.squeeze_native_field_elements(1)[0]
}

/// In-circuit hash mirroring [`hash`]; the domain tag is a constant, so it
/// adds no witness variables.
pub fn hash_var(
    cs: ConstraintSystemRef<Fr>,
    cfg: &PoseidonConfig<Fr>,
    dom: u64,
    inputs: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    let mut sponge = PoseidonSpongeVar::new(cs, cfg);
    sponge.absorb(&FpVar::Constant(Fr::from(dom)))?;
    sponge.absorb(&inputs)?;
    Ok(sponge.squeeze_field_elements(1)?.remove(0))
}
