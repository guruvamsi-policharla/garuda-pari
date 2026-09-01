//! The Sapling-style hash instantiation shared by all private-transfer
//! primitives: Pedersen over Jubjub for everything structural (Merkle
//! nodes, indexed-tree leaves, commitments) and SHA-256 for the scheme's
//! single CRPRF call site (nullifier derivation in R_recv).
//!
//! Every hash in the scheme goes through [`hash`] / [`hash_var`], routed by
//! its domain tag:
//!
//!   Com_acct(b, kappa, root_null; r) = H(DOM_ACCT, b, kappa, root, r) Pedersen
//!   CRPRF_kappa(recv, pos)           = H(DOM_NULL, kappa, pos)        SHA-256
//!   Com_rec(v, Sen, Rec; r'')        = H(DOM_REC,  v, S, R, r'')      Pedersen
//!   Merkle node                    = H(DOM_NODE, left, right)   Pedersen
//!   Indexed-tree leaf              = H(DOM_ILEAF, value, nv, ni) Pedersen
//!
//! The paper's `recv` PRF label *is* the DOM_NULL domain byte; the key
//! kappa comes first in the preimage, then the receipt position.
//!
//! Both primitives share a byte serialization: a 1-byte domain tag followed
//! by the canonical 32-byte little-endian encoding of each field element
//! (the in-circuit `to_bytes_le` enforces the canonical decomposition, so
//! the encoding is unique).
//!
//! **Pedersen**: digest = x-coordinate of `sum_i bits_i * G_i` with one
//! 8-bit window of doubling powers per input byte, sliced to the exact
//! preimage length so padding is never paid for (~5.6 R1CS per bit via the
//! twisted-Edwards 2-bit-lookup gadget). x-coordinate truncation identifies
//! P and -P, which is still collision-resistant under the discrete log
//! assumption (the Sapling argument). Commitments hide because the trailing
//! randomness contributes a 256-bit subset sum; a deployment would make the
//! randomness windows a doubling chain of a *single* base so that term is
//! exactly r*H (Sapling's windowed Pedersen commitment) — identical circuit
//! cost — and would derive all generators as nothing-up-my-sleeve points
//! rather than from this benchmark's fixed seed.
//!
//! **SHA-256**: the 256-bit digest is truncated to its low 253 bits and
//! repacked as a field element — always `< r`, so native and in-circuit
//! outputs agree bit for bit. With fixed-length input and the key in front,
//! SHA-256(dom || kappa || pos) is a standard PRF instantiation. The call
//! is 2 compression functions; only R_recv pays it (once) — R_send has no
//! PRF call site at all.

use ark_crypto_primitives::crh::sha256::constraints::Sha256Gadget;
use ark_crypto_primitives::crh::sha256::{digest::Digest, Sha256};
use ark_ec::CurveGroup;
use ark_ed_on_bls12_381::{constraints::EdwardsVar, EdwardsProjective};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::convert::{ToBitsGadget, ToBytesGadget};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::uint8::UInt8;
use ark_relations::gr1cs::SynthesisError;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;

use super::super::Fr;

/// Domain-separation tags (small values on purpose: they serialize as a
/// single byte). NULL routes to SHA-256; everything else to Pedersen.
pub const DOM_ACCT: u64 = 1;
/// The nullifier CRPRF: the paper's `recv` label.
pub const DOM_NULL: u64 = 2;
pub const DOM_REC: u64 = 4;
pub const DOM_NODE: u64 = 5;
/// Indexed-tree leaf: `H(DOM_ILEAF, value, next_value, next_index)`.
pub const DOM_ILEAF: u64 = 6;

/// The largest Pedersen preimage: Com_acct / Com_rec's 1-byte tag + 4 field
/// elements (three data slots plus randomness).
const PEDERSEN_MAX_BYTES: usize = 1 + 4 * 32;

/// The CRPRF call site, which needs a genuine PRF rather than a CRH.
fn is_prf(dom: u64) -> bool {
    dom == DOM_NULL
}

/// The hash instantiation every primitive is parametrized by: the Pedersen
/// generator table (one 8-bit window of Jubjub doubling powers per input
/// byte, sized for the largest preimage and sliced per call).
#[derive(Clone)]
pub struct HashCfg {
    table: Vec<Vec<EdwardsProjective>>,
}

impl HashCfg {
    pub fn new() -> Self {
        let mut rng = StdRng::seed_from_u64(0x4a75_626a_7562); // "Jubjub"
        let table = (0..PEDERSEN_MAX_BYTES)
            .map(|_| {
                let mut base = EdwardsProjective::rand(&mut rng);
                let mut powers = Vec::with_capacity(8);
                for _ in 0..8 {
                    powers.push(base);
                    base.double_in_place();
                }
                powers
            })
            .collect();
        Self { table }
    }
}

impl Default for HashCfg {
    fn default() -> Self {
        Self::new()
    }
}

/// The byte serialization shared by both primitives: 1-byte domain tag,
/// then each element in canonical 32-byte LE form.
fn serialize_native(dom: u64, inputs: &[Fr]) -> Vec<u8> {
    let mut bytes = vec![dom as u8];
    for x in inputs {
        bytes.extend_from_slice(&x.into_bigint().to_bytes_le());
    }
    bytes
}

/// In-circuit mirror of [`serialize_native`]; `to_bytes_le` enforces the
/// canonical (unique) decomposition of each element.
fn serialize_var(dom: u64, inputs: &[FpVar<Fr>]) -> Result<Vec<UInt8<Fr>>, SynthesisError> {
    let mut bytes = vec![UInt8::constant(dom as u8)];
    for x in inputs {
        bytes.extend(x.to_bytes_le()?);
    }
    Ok(bytes)
}

/// Repack the low 253 bits of a SHA-256 digest as a field element (253 bits
/// is always `< r`, so no reduction happens and the circuit can mirror this
/// exactly).
fn field_from_digest(digest: &[u8]) -> Fr {
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(digest);
    bytes[31] &= 0x1f;
    Fr::from_le_bytes_mod_order(&bytes)
}

/// Native hash of `dom` and `inputs` (SHA-256 for the PRF domains,
/// Pedersen otherwise).
pub fn hash(cfg: &HashCfg, dom: u64, inputs: &[Fr]) -> Fr {
    let bytes = serialize_native(dom, inputs);
    if is_prf(dom) {
        field_from_digest(&Sha256::digest(&bytes))
    } else {
        assert!(
            bytes.len() <= cfg.table.len(),
            "preimage exceeds generator table"
        );
        let mut acc = EdwardsProjective::zero();
        for (byte, powers) in bytes.iter().zip(&cfg.table) {
            for (i, g) in powers.iter().enumerate() {
                if (byte >> i) & 1 == 1 {
                    acc += g;
                }
            }
        }
        acc.into_affine().x
    }
}

/// In-circuit hash mirroring [`hash`]; the domain tag is a constant, so it
/// adds no witness variables under either primitive.
pub fn hash_var(
    cfg: &HashCfg,
    dom: u64,
    inputs: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    let bytes = serialize_var(dom, inputs)?;
    if is_prf(dom) {
        let digest = Sha256Gadget::digest(&bytes)?.0;
        let mut bits = Vec::with_capacity(256);
        for byte in &digest {
            bits.extend(byte.to_bits_le()?);
        }
        Boolean::le_bits_to_fp(&bits[..253])
    } else {
        assert!(
            bytes.len() <= cfg.table.len(),
            "preimage exceeds generator table"
        );
        let windows = bytes
            .iter()
            .map(|b| b.to_bits_le())
            .collect::<Result<Vec<_>, _>>()?;
        let point = EdwardsVar::precomputed_base_multiscalar_mul_le(
            &cfg.table[..bytes.len()],
            windows.iter().map(|w| w.as_slice()),
        )?;
        Ok(point.x)
    }
}
