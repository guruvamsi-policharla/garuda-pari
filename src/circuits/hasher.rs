//! The collision-resistant hash shared by all private-payment primitives,
//! in two interchangeable instantiations: **Pedersen over Jubjub**
//! (Sapling-style) and **Poseidon** over the BLS12-381 scalar field. A
//! [`HashCfg`] fixes one of them for a whole deployment; the circuits are
//! written against [`hash`] / [`hash_var`] and never see the backend.
//!
//! Every hash in the scheme goes through those two functions, routed by a
//! domain tag:
//!
//!   Com_acct(b, root_null; r)         = H(DOM_ACCT, b, root, r)
//!   Com_rec(v, Sen, Rec; r'')         = H(DOM_REC,  v, S, R, r'')
//!   Com_rec(v, Sen, Rec, type; r'')   = H(DOM_REC,  v, S, R, t, r'')
//!   Merkle node                       = H(DOM_NODE, left, right)
//!
//! There is no PRF anywhere: the nullifier of a receipt *is* its position
//! in the receipt log (`null = pid`), and nullifiers are never published —
//! they live only inside the receiver's committed sparse Merkle tree and
//! inside zero-knowledge proofs, so pseudorandomness would buy nothing.
//! Soundness needs only that positions are unique, which the receipt-log
//! opening already binds. Consequently the account commitment carries no
//! PRF key: it has exactly two data slots (balance, nullifier-tree root)
//! plus randomness, and every hash in the scheme is a plain CRH.
//!
//! The receipt commitment has two arities: the unlinkable construction's
//! three data slots, and the operation-hiding construction's four (the
//! trailing *type* slot distinguishes real receipts, type 1, from the dummy
//! receipts a hidden receive publishes, type 0). A deployment uses exactly
//! one of the two constructions, so the arities never coexist under one
//! ledger.
//!
//! **Pedersen**: preimage = 1-byte domain tag followed by the canonical
//! 32-byte little-endian encoding of each field element (the in-circuit
//! `to_bytes_le` enforces the canonical decomposition, so the encoding is
//! unique). Digest = x-coordinate of `sum_i bits_i * G_i` with one 8-bit
//! window of doubling powers per input byte, sliced to the exact preimage
//! length so padding is never paid for (~5.6 R1CS per bit via the
//! twisted-Edwards 2-bit-lookup gadget). x-coordinate truncation identifies
//! P and -P, which is still collision-resistant under the discrete log
//! assumption (the Sapling argument). Commitments hide because the trailing
//! randomness contributes a 256-bit subset sum; a deployment would make the
//! randomness windows a doubling chain of a *single* base so that term is
//! exactly r*H (Sapling's windowed Pedersen commitment) — identical circuit
//! cost — and would derive all generators as nothing-up-my-sleeve points
//! rather than from this instantiation's fixed seed.
//!
//! **Poseidon**: width 3 (rate 2, capacity 1), alpha = 5, 8 full + 57
//! partial rounds — the Poseidon-128 parameter set for a 255-bit prime at
//! t = 3, so a Merkle node costs exactly one permutation (~240 R1CS: 3
//! constraints per S-box). Inputs are absorbed as field elements directly
//! (no byte decomposition), and the domain tag together with the input
//! arity is placed in the *capacity* slot as an initial value, which gives
//! domain separation without spending rate. Round constants and the MDS
//! matrix come from the reference Grain LFSR; a deployment would run the
//! reference implementation's matrix-security checks (`skip_matrices`)
//! before fixing them.

use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_crypto_primitives::sponge::poseidon::{
    find_poseidon_ark_and_mds, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{CryptographicSponge, FieldBasedCryptographicSponge};
use ark_ec::CurveGroup;
use ark_ed_on_bls12_381::{constraints::EdwardsVar, EdwardsProjective};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_r1cs_std::convert::{ToBitsGadget, ToBytesGadget};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::select::TwoBitLookupGadget;
use ark_r1cs_std::uint8::UInt8;
use ark_r1cs_std::GR1CSVar;
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;

use super::Fr;

/// Domain-separation tags (small values on purpose: they serialize as a
/// single byte under Pedersen and fit the capacity encoding under
/// Poseidon).
pub const DOM_ACCT: u64 = 1;
pub const DOM_REC: u64 = 4;
pub const DOM_NODE: u64 = 5;

/// The largest Pedersen preimage: the operation-hiding Com_rec's 1-byte tag
/// + 5 field elements (four data slots plus randomness).
const PEDERSEN_MAX_BYTES: usize = 1 + 5 * 32;

/// Poseidon parameters: width 3, alpha 5, 8 full + 57 partial rounds.
const POSEIDON_RATE: usize = 2;
const POSEIDON_ALPHA: u64 = 5;
const POSEIDON_FULL_ROUNDS: usize = 8;
const POSEIDON_PARTIAL_ROUNDS: usize = 57;

/// Which collision-resistant hash a deployment runs on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HashKind {
    Pedersen,
    Poseidon,
}

impl HashKind {
    pub fn label(self) -> &'static str {
        match self {
            HashKind::Pedersen => "pedersen",
            HashKind::Poseidon => "poseidon",
        }
    }
}

/// One 8-bit Pedersen window in the form the in-circuit gadget consumes:
/// for each pair of adjacent bits `(2j, 2j+1)`, the affine `x` and `y`
/// coordinates of `[O, G_2j, G_2j+1, G_2j + G_2j+1]`, indexed by the 2-bit
/// value. Precomputing these once per [`HashCfg`] keeps circuit synthesis
/// free of group arithmetic — in particular of `normalize_batch`, whose
/// rayon-parallel batch inversion spawns a task per point and made
/// synthesis *slower* on many cores when called per window.
pub type PedersenLookups = [([Fr; 4], [Fr; 4]); 4];

/// The hash instantiation every primitive is parametrized by.
#[derive(Clone)]
pub enum HashCfg {
    /// Pedersen generator table: one 8-bit window of Jubjub doubling powers
    /// per input byte, sized for the largest preimage and sliced per call.
    /// `lookups[i]` is `table[i]` re-expressed as the gadget's 2-bit tables.
    Pedersen {
        table: Vec<Vec<EdwardsProjective>>,
        lookups: Vec<PedersenLookups>,
    },
    /// Poseidon round constants and MDS matrix.
    Poseidon { params: PoseidonConfig<Fr> },
}

impl HashCfg {
    /// The Pedersen/Jubjub instantiation (the historical default).
    pub fn new() -> Self {
        Self::pedersen()
    }

    pub fn of(kind: HashKind) -> Self {
        match kind {
            HashKind::Pedersen => Self::pedersen(),
            HashKind::Poseidon => Self::poseidon(),
        }
    }

    pub fn pedersen() -> Self {
        let mut rng = StdRng::seed_from_u64(0x4a75_626a_7562); // "Jubjub"
        let table: Vec<Vec<EdwardsProjective>> = (0..PEDERSEN_MAX_BYTES)
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
        let lookups = table
            .iter()
            .map(|powers| pedersen_lookups(powers))
            .collect();
        Self::Pedersen { table, lookups }
    }

    pub fn poseidon() -> Self {
        let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(
            Fr::MODULUS_BIT_SIZE as u64,
            POSEIDON_RATE,
            POSEIDON_FULL_ROUNDS as u64,
            POSEIDON_PARTIAL_ROUNDS as u64,
            0,
        );
        let params = PoseidonConfig::new(
            POSEIDON_FULL_ROUNDS,
            POSEIDON_PARTIAL_ROUNDS,
            POSEIDON_ALPHA,
            mds,
            ark,
            POSEIDON_RATE,
            1,
        );
        Self::Poseidon { params }
    }

    pub fn kind(&self) -> HashKind {
        match self {
            HashCfg::Pedersen { .. } => HashKind::Pedersen,
            HashCfg::Poseidon { .. } => HashKind::Poseidon,
        }
    }
}

impl Default for HashCfg {
    fn default() -> Self {
        Self::new()
    }
}

// ── Pedersen ────────────────────────────────────────────────────────────

/// The Pedersen byte serialization: 1-byte domain tag, then each element in
/// canonical 32-byte LE form.
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

fn pedersen_hash(table: &[Vec<EdwardsProjective>], dom: u64, inputs: &[Fr]) -> Fr {
    let bytes = serialize_native(dom, inputs);
    assert!(
        bytes.len() <= table.len(),
        "preimage exceeds generator table"
    );
    let mut acc = EdwardsProjective::zero();
    for (byte, powers) in bytes.iter().zip(table) {
        for (i, g) in powers.iter().enumerate() {
            if (byte >> i) & 1 == 1 {
                acc += g;
            }
        }
    }
    acc.into_affine().x
}

/// The 2-bit lookup tables for one 8-bit window of doubling powers: for
/// each bit pair, the affine coordinates of `[O, G_a, G_b, G_a + G_b]`.
fn pedersen_lookups(powers: &[EdwardsProjective]) -> PedersenLookups {
    debug_assert_eq!(powers.len(), 8);
    let zero = EdwardsProjective::zero().into_affine();
    let mut out = [([Fr::zero(); 4], [Fr::zero(); 4]); 4];
    for (j, pair) in powers.chunks(2).enumerate() {
        let (g_a, g_b) = (pair[0], pair[1]);
        let pts = [
            zero,
            g_a.into_affine(),
            g_b.into_affine(),
            (g_a + g_b).into_affine(),
        ];
        out[j] = (pts.map(|p| p.x), pts.map(|p| p.y));
    }
    out
}

/// In-circuit mirror of [`pedersen_hash`]: `sum_i bits_i * G_i` via the
/// twisted-Edwards 2-bit-lookup gadget, then the x-coordinate.
///
/// This is `EdwardsVar::precomputed_base_multiscalar_mul_le` unrolled over
/// precomputed affine tables: the same gadget calls in the same order (two
/// `two_bit_lookup`s and one point addition per bit pair), hence the same
/// constraints and the same digest, minus the per-window `normalize_batch`
/// the library version performs at synthesis time.
fn pedersen_hash_var(
    lookups: &[PedersenLookups],
    dom: u64,
    inputs: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    let bytes = serialize_var(dom, inputs)?;
    assert!(
        bytes.len() <= lookups.len(),
        "preimage exceeds generator table"
    );
    let mut acc = EdwardsVar::zero();
    for (byte, window) in bytes.iter().zip(lookups) {
        let bits = byte.to_bits_le()?;
        for (pair, (xs, ys)) in bits.chunks(2).zip(window) {
            let x = FpVar::two_bit_lookup(pair, xs)?;
            let y = FpVar::two_bit_lookup(pair, ys)?;
            acc += EdwardsVar::new(x, y);
        }
    }
    Ok(acc.x)
}

// ── Poseidon ────────────────────────────────────────────────────────────

/// The capacity initial value: domain tag in the low byte, input arity
/// above it. Fixing the arity here means no two preimages of different
/// lengths can collide across the sponge's absorb boundary.
fn poseidon_iv(dom: u64, arity: usize) -> Fr {
    debug_assert!(dom < 256);
    Fr::from(dom + ((arity as u64) << 8))
}

fn poseidon_hash(params: &PoseidonConfig<Fr>, dom: u64, inputs: &[Fr]) -> Fr {
    let mut sponge = PoseidonSponge::new(params);
    sponge.state[0] = poseidon_iv(dom, inputs.len());
    sponge.absorb(&inputs);
    sponge.squeeze_native_field_elements(1)[0]
}

fn poseidon_hash_var(
    params: &PoseidonConfig<Fr>,
    dom: u64,
    inputs: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    let cs = inputs
        .iter()
        .fold(ConstraintSystemRef::None, |cs, x| cs.or(x.cs()));
    let mut sponge = PoseidonSpongeVar::new(cs, params);
    sponge.state[0] = FpVar::Constant(poseidon_iv(dom, inputs.len()));
    sponge.absorb(&inputs)?;
    Ok(sponge.squeeze_field_elements(1)?.swap_remove(0))
}

// ── Dispatch ────────────────────────────────────────────────────────────

/// Native hash of `dom` and `inputs` under the configured backend.
pub fn hash(cfg: &HashCfg, dom: u64, inputs: &[Fr]) -> Fr {
    match cfg {
        HashCfg::Pedersen { table, .. } => pedersen_hash(table, dom, inputs),
        HashCfg::Poseidon { params } => poseidon_hash(params, dom, inputs),
    }
}

/// In-circuit hash mirroring [`hash`]; the domain tag is a constant, so it
/// adds no witness variables under either backend.
pub fn hash_var(
    cfg: &HashCfg,
    dom: u64,
    inputs: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    match cfg {
        HashCfg::Pedersen { lookups, .. } => pedersen_hash_var(lookups, dom, inputs),
        HashCfg::Poseidon { params } => poseidon_hash_var(params, dom, inputs),
    }
}
