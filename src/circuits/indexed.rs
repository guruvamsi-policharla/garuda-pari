//! Indexed Merkle tree (Aztec-style) for the per-account nullifier trees,
//! with the *insertion proof verified in-circuit*.
//!
//! Leaves form a linked list sorted by value: leaf = (value, next_value,
//! next_index), hashed as `H(DOM_ILEAF, value, next_value, next_index)`;
//! `next_value = 0` marks the list maximum, and the genesis leaf (0, 0, 0)
//! makes the empty tree well-formed. Inserting `key` proves
//! *non-membership* by exhibiting the low leaf with
//! `low.value < key < low.next_value` (or `low.next_value = 0`), then
//! re-links: the low leaf's successor becomes `key`, and the new leaf takes
//! over the low leaf's old successor.
//!
//! The in-circuit check `enforce_indexed_insert` is the paper's
//! `mt.AccVerifyInsert(root, key, pi_mt) = root'` moved inside the SNARK:
//! the ledger then only compares `root` against its stored 32-byte root and
//! swaps in `root'` — no per-transaction hashing, and no `pi_mt` on the
//! wire. Cost: four hash-chains of `depth` node hashes (old low
//! leaf up to `root`, updated low leaf up to the intermediate root, the
//! empty slot up to the same intermediate root, the new leaf up to `root'`)
//! plus three leaf hashes and two 128-bit comparisons.
//!
//! Tree keys are the low 128 bits of the (hash-output) nullifier —
//! full field elements cannot be compared soundly in-circuit without their
//! own decomposition, and 128 bits keeps collisions negligible while making
//! the ordering checks cheap.

use ark_ff::{BigInt, PrimeField, Zero};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::convert::ToBitsGadget;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::select::CondSelectGadget;
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};

use super::hasher::{hash, hash_var, HashCfg, DOM_ILEAF, DOM_NODE};
use super::merkle::{alloc_path, compute_root_var, MerklePath};
use super::Fr;
use super::{enforce_lt_128, enforce_range_bits};

/// Truncate a field element to the low 128 bits — the indexed-tree key of a
/// nullifier.
pub fn truncate_to_key(x: Fr) -> Fr {
    let limbs = x.into_bigint().0;
    Fr::from_bigint(BigInt::new([limbs[0], limbs[1], 0, 0])).unwrap()
}

/// 2^128 as a field element (the comparison bound when the low leaf is the
/// list maximum).
fn two_pow_128() -> Fr {
    Fr::from_bigint(BigInt::new([0, 0, 1, 0])).unwrap()
}

#[derive(Clone, Copy, Debug)]
pub struct IndexedLeaf {
    pub value: Fr,
    pub next_value: Fr,
    pub next_index: u64,
}

/// Everything the prover needs to witness one insertion.
#[derive(Clone, Debug)]
pub struct IndexedInsertion {
    pub old_root: Fr,
    pub new_root: Fr,
    /// The low leaf *before* the update.
    pub low_leaf: IndexedLeaf,
    /// Path of the low leaf; also valid (same siblings) for the updated
    /// low leaf under the intermediate root.
    pub low_path: MerklePath,
    /// Slot of the new leaf (empty before the insert).
    pub new_index: u64,
    /// Path of the new slot under the *intermediate* root.
    pub new_path: MerklePath,
}

impl IndexedInsertion {
    /// Transient stand-in for two-phase circuit construction; replaced by
    /// `attach_*_insertion` before the circuit is ever synthesized.
    pub fn placeholder() -> Self {
        Self {
            old_root: Fr::zero(),
            new_root: Fr::zero(),
            low_leaf: IndexedLeaf {
                value: Fr::zero(),
                next_value: Fr::zero(),
                next_index: 0,
            },
            low_path: MerklePath {
                siblings: vec![],
                index_bits: vec![],
            },
            new_index: 0,
            new_path: MerklePath {
                siblings: vec![],
                index_bits: vec![],
            },
        }
    }
}

/// Fixed-depth indexed Merkle tree, rebuilt eagerly on each insert (fine for
/// test/benchmark-sized trees; empty slots to the right are all-zero
/// subtrees).
pub struct IndexedMerkleTree {
    cfg: HashCfg,
    pub depth: usize,
    leaves: Vec<IndexedLeaf>,
    /// `levels[0]` = leaf hashes, ..., `levels[depth]` = root.
    levels: Vec<Vec<Fr>>,
    /// `zeros[j]` = root of the all-zero subtree of height `j`.
    zeros: Vec<Fr>,
}

impl IndexedMerkleTree {
    pub fn new(cfg: &HashCfg, depth: usize) -> Self {
        let mut zeros = Vec::with_capacity(depth + 1);
        zeros.push(Fr::zero());
        for j in 0..depth {
            let z = zeros[j];
            zeros.push(hash(cfg, DOM_NODE, &[z, z]));
        }
        let mut tree = Self {
            cfg: cfg.clone(),
            depth,
            leaves: vec![IndexedLeaf {
                value: Fr::zero(),
                next_value: Fr::zero(),
                next_index: 0,
            }],
            levels: vec![Vec::new(); depth + 1],
            zeros,
        };
        tree.rebuild();
        tree
    }

    fn leaf_hash(&self, leaf: &IndexedLeaf) -> Fr {
        hash(
            &self.cfg,
            DOM_ILEAF,
            &[leaf.value, leaf.next_value, Fr::from(leaf.next_index)],
        )
    }

    fn rebuild(&mut self) {
        self.levels[0] = self.leaves.iter().map(|l| self.leaf_hash(l)).collect();
        for j in 0..self.depth {
            self.levels[j + 1] = self.levels[j]
                .chunks(2)
                .map(|pair| {
                    let left = pair[0];
                    let right = if pair.len() == 2 {
                        pair[1]
                    } else {
                        self.zeros[j]
                    };
                    hash(&self.cfg, DOM_NODE, &[left, right])
                })
                .collect();
        }
    }

    pub fn root(&self) -> Fr {
        *self.levels[self.depth]
            .first()
            .unwrap_or(&self.zeros[self.depth])
    }

    /// Authentication path for `index`; the slot may be empty (used for the
    /// insertion slot), in which case the leaf hashes up from zero.
    fn path(&self, index: usize) -> MerklePath {
        let mut siblings = Vec::with_capacity(self.depth);
        let mut index_bits = Vec::with_capacity(self.depth);
        for j in 0..self.depth {
            let pos = index >> j;
            let sib = *self.levels[j].get(pos ^ 1).unwrap_or(&self.zeros[j]);
            siblings.push(sib);
            index_bits.push(pos & 1 == 1);
        }
        MerklePath {
            siblings,
            index_bits,
        }
    }

    /// Insert a key (must be a 128-bit value, nonzero, and not present) and
    /// return the witness data for the in-circuit insertion proof.
    pub fn insert(&mut self, key: Fr) -> IndexedInsertion {
        let key_big = key.into_bigint();
        assert!(
            key_big.0[2] == 0 && key_big.0[3] == 0 && !key.is_zero(),
            "keys are nonzero 128-bit values; use truncate_to_key"
        );

        // Find the low leaf: value < key < next_value (or next_value = 0).
        let mut low_index = None;
        for (i, leaf) in self.leaves.iter().enumerate() {
            assert!(leaf.value != key, "duplicate key");
            if leaf.value.into_bigint() < key_big
                && (leaf.next_value.is_zero() || key_big < leaf.next_value.into_bigint())
            {
                low_index = Some(i);
            }
        }
        let low_index = low_index.expect("sorted linked list must have a low leaf");

        let old_root = self.root();
        let low_leaf = self.leaves[low_index];
        // Updating leaf `low_index` and appending at `new_index` never touch
        // their own paths' siblings, so this path also verifies the updated
        // low leaf under the intermediate root.
        let low_path = self.path(low_index);

        let new_index = self.leaves.len();
        assert!(new_index < 1usize << self.depth.min(63), "tree is full");

        // Re-link: low leaf now points at the new leaf...
        self.leaves[low_index].next_value = key;
        self.leaves[low_index].next_index = new_index as u64;
        self.rebuild();
        let new_path = self.path(new_index); // under the intermediate root

        // ...and the new leaf takes over the low leaf's old successor.
        self.leaves.push(IndexedLeaf {
            value: key,
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
        });
        self.rebuild();

        IndexedInsertion {
            old_root,
            new_root: self.root(),
            low_leaf,
            low_path,
            new_index: new_index as u64,
            new_path,
        }
    }
}

/// Derive the in-circuit tree key from a full field element: canonical bit
/// decomposition, repacking the low 128 bits (matches [`truncate_to_key`]).
pub fn key_from_field_var(x: &FpVar<Fr>) -> Result<FpVar<Fr>, SynthesisError> {
    let bits = x.to_bits_le()?;
    Boolean::le_bits_to_fp(&bits[..128])
}

/// Enforce that inserting `key` (a 128-bit tree key with native value
/// `key_val`) transitions the indexed tree from `root_old` to `root_new` —
/// but only when `enforce` is true.
///
/// This is `mt.AccVerifyInsert(root_old, key, pi_mt) = root_new` in-circuit;
/// soundness of the non-membership argument follows from the sorted
/// linked-list invariant, which every accepted insertion preserves.
///
/// The three root equalities are gated on `enforce` (R_op's send branch
/// disables them); the leaf range checks and the non-membership orderings
/// stay unconditional, so a disabled branch must still witness *some* valid
/// insertion — inserting the derived key into an empty tree always works.
#[allow(clippy::too_many_arguments)]
pub fn enforce_indexed_insert(
    cs: ConstraintSystemRef<Fr>,
    cfg: &HashCfg,
    key: &FpVar<Fr>,
    key_val: Fr,
    root_old: &FpVar<Fr>,
    root_new: &FpVar<Fr>,
    ins: &IndexedInsertion,
    enforce: &Boolean<Fr>,
) -> Result<(), SynthesisError> {
    // The low leaf, range-checked so the orderings below are sound.
    let low_value = FpVar::new_witness(cs.clone(), || Ok(ins.low_leaf.value))?;
    let low_next = FpVar::new_witness(cs.clone(), || Ok(ins.low_leaf.next_value))?;
    let low_next_index = FpVar::new_witness(cs.clone(), || Ok(Fr::from(ins.low_leaf.next_index)))?;
    enforce_range_bits(cs.clone(), &low_value, ins.low_leaf.value, 128)?;
    enforce_range_bits(cs.clone(), &low_next, ins.low_leaf.next_value, 128)?;

    // 1. The low leaf is in the tree under root_old.
    let low_path = alloc_path(cs.clone(), &ins.low_path)?;
    let low_hash = hash_var(
        cfg,
        DOM_ILEAF,
        &[low_value.clone(), low_next.clone(), low_next_index.clone()],
    )?;
    compute_root_var(cfg, &low_hash, &low_path)?.conditional_enforce_equal(root_old, enforce)?;

    // 2. Non-membership: low.value < key < low.next_value, where a zero
    //    next_value means "list maximum" and compares as 2^128.
    enforce_lt_128(cs.clone(), &low_value, ins.low_leaf.value, key, key_val)?;
    let is_max = low_next.is_eq(&FpVar::zero())?;
    let bound = FpVar::conditionally_select(&is_max, &FpVar::Constant(two_pow_128()), &low_next)?;
    let bound_val = if ins.low_leaf.next_value.is_zero() {
        two_pow_128()
    } else {
        ins.low_leaf.next_value
    };
    enforce_lt_128(cs.clone(), key, key_val, &bound, bound_val)?;

    // 3. The new slot's position, bound to the value hashed into the
    //    updated low leaf.
    let new_path = alloc_path(cs, &ins.new_path)?;
    let new_index = Boolean::le_bits_to_fp(&new_path.bits)?;

    // 4. Updated low leaf (successor becomes the new leaf) -> intermediate
    //    root, over the *same* siblings as step 1.
    let low_updated_hash = hash_var(cfg, DOM_ILEAF, &[low_value, key.clone(), new_index])?;
    let mid_root = compute_root_var(cfg, &low_updated_hash, &low_path)?;

    // 5. The new slot is empty under the intermediate root...
    compute_root_var(cfg, &FpVar::zero(), &new_path)?
        .conditional_enforce_equal(&mid_root, enforce)?;

    // 6. ...and holds the new leaf under root_new.
    let new_leaf_hash = hash_var(cfg, DOM_ILEAF, &[key.clone(), low_next, low_next_index])?;
    compute_root_var(cfg, &new_leaf_hash, &new_path)?
        .conditional_enforce_equal(root_new, enforce)?;

    Ok(())
}
