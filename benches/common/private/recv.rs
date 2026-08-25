//! The paper's receive relation R_recv, as an R1CS gadget circuit.
//!
//! Statement (public inputs, in the paper's order):
//!   x_r = (Rec, com, rootnull, com', rootnull', nullifier, rootrho)
//! Witness:
//!   w_r = (b, kappa, r, r', v, Sen, r'', pi_mmr, pi_mt)
//! Constraints:
//!   com  = Com_acct(b, kappa; r)
//!   com' = Com_acct(b + v, kappa; r')
//!   rho  = Com_rec(v, Sen, Rec, nullifier; r'')
//!   mmr.Verify(rootrho, rho, pi_mmr) = 1
//!   mt.AccVerifyInsert(rootnull, nullifier, pi_mt) = rootnull'
//!   v > 0   and   b, v, b + v in [0, 2^64)
//!
//! The nullifier-tree insertion proof is verified *in-circuit* against the
//! indexed tree (see `indexed.rs`), whose low-leaf argument also proves the
//! nullifier was not already present — the double-receive check. The ledger
//! just compares `rootnull` with its stored root and swaps in `rootnull'`.
//! The one remaining native check: `rootrho` is a *revealed anchor* — the
//! receiver computes pi_mmr from the public receipt log against a recent
//! root, and the ledger checks `rootrho` against its retained root history
//! (the W most recent roots) natively.

use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

use super::super::Fr;
use super::enforce_range_64;
use super::indexed::{
    enforce_indexed_insert, key_from_field_var, truncate_to_key, IndexedInsertion,
    IndexedMerkleTree,
};
use super::merkle::{enforce_membership, MerklePath, MerkleTree};
use super::poseidon::{hash, hash_var, DOM_ACCT, DOM_REC};

#[derive(Clone)]
pub struct RecvCircuit {
    pub cfg: PoseidonConfig<Fr>,
    /// Acting receiver identifier (public).
    pub rec: Fr,
    /// Revealed nullifier of the consumed receipt (public).
    pub nullifier: Fr,
    /// Revealed anchor of the receipt tree (public; checked against the
    /// ledger's root history natively).
    pub root: Fr,
    /// Current balance.
    pub b: u64,
    /// Received amount.
    pub v: u64,
    /// Account PRF key.
    pub kappa: Fr,
    /// Opening randomness: old account, new account, receipt.
    pub r: Fr,
    pub r_new: Fr,
    pub r_receipt: Fr,
    /// Sender identifier inside the receipt.
    pub sen: Fr,
    /// Membership path of the receipt under `root`; its length is the
    /// receipt-tree depth and is fixed at keygen time.
    pub path: MerklePath,
    /// Witness for inserting the nullifier into the receiver's nullifier
    /// tree; fixes that tree's depth and carries (rootnull, rootnull').
    pub null_insert: IndexedInsertion,
}

impl RecvCircuit {
    /// A satisfiable instance of the given depths, for keygen and
    /// constraint counting.
    pub fn blank(cfg: &PoseidonConfig<Fr>, receipt_depth: usize, acct_depth: usize) -> Self {
        let mut receipt_tree = MerkleTree::new(cfg, receipt_depth);
        let mut null_tree = IndexedMerkleTree::new(cfg, acct_depth);
        let mut blank = Self {
            cfg: cfg.clone(),
            rec: Fr::from(0u64),
            nullifier: Fr::from(1u64),
            root: Fr::from(0u64),
            b: 0,
            v: 1,
            kappa: Fr::from(0u64),
            r: Fr::from(0u64),
            r_new: Fr::from(0u64),
            r_receipt: Fr::from(0u64),
            sen: Fr::from(0u64),
            path: MerklePath {
                siblings: vec![],
                index_bits: vec![],
            },
            null_insert: null_tree.insert(truncate_to_key(Fr::from(1u64))),
        };
        let index = receipt_tree.append(blank.receipt());
        blank.root = receipt_tree.root();
        blank.path = receipt_tree.path(index);
        blank
    }

    /// Insert the revealed nullifier into the receiver's nullifier tree
    /// (mutating the ledger-side state) and attach the insertion witness.
    pub fn attach_nullifier_insertion(&mut self, null_tree: &mut IndexedMerkleTree) {
        self.null_insert = null_tree.insert(truncate_to_key(self.nullifier));
    }

    pub fn com(&self) -> Fr {
        hash(&self.cfg, DOM_ACCT, &[Fr::from(self.b), self.kappa, self.r])
    }

    pub fn com_new(&self) -> Fr {
        let b_new = Fr::from(self.b) + Fr::from(self.v);
        hash(&self.cfg, DOM_ACCT, &[b_new, self.kappa, self.r_new])
    }

    /// The receipt rho this proof consumes (must sit under `root`).
    pub fn receipt(&self) -> Fr {
        hash(
            &self.cfg,
            DOM_REC,
            &[
                Fr::from(self.v),
                self.sen,
                self.rec,
                self.nullifier,
                self.r_receipt,
            ],
        )
    }

    /// The statement, in the order the circuit allocates its inputs.
    pub fn public_input(&self) -> Vec<Fr> {
        vec![
            self.rec,
            self.com(),
            self.null_insert.old_root,
            self.com_new(),
            self.null_insert.new_root,
            self.nullifier,
            self.root,
        ]
    }
}

impl ConstraintSynthesizer<Fr> for RecvCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Statement, allocated first, in the paper's order.
        let rec = FpVar::new_input(cs.clone(), || Ok(self.rec))?;
        let com = FpVar::new_input(cs.clone(), || Ok(self.com()))?;
        let rootnull = FpVar::new_input(cs.clone(), || Ok(self.null_insert.old_root))?;
        let com_new = FpVar::new_input(cs.clone(), || Ok(self.com_new()))?;
        let rootnull_new = FpVar::new_input(cs.clone(), || Ok(self.null_insert.new_root))?;
        let nullifier = FpVar::new_input(cs.clone(), || Ok(self.nullifier))?;
        let root = FpVar::new_input(cs.clone(), || Ok(self.root))?;

        // Witness.
        let b = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.b)))?;
        let v = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.v)))?;
        let kappa = FpVar::new_witness(cs.clone(), || Ok(self.kappa))?;
        let r = FpVar::new_witness(cs.clone(), || Ok(self.r))?;
        let r_new = FpVar::new_witness(cs.clone(), || Ok(self.r_new))?;
        let r_receipt = FpVar::new_witness(cs.clone(), || Ok(self.r_receipt))?;
        let sen = FpVar::new_witness(cs.clone(), || Ok(self.sen))?;

        // com = Com_acct(b, kappa; r)
        hash_var(cs.clone(), &self.cfg, DOM_ACCT, &[b.clone(), kappa.clone(), r])?
            .enforce_equal(&com)?;

        // com' = Com_acct(b + v, kappa; r') — same PRF key, credited balance.
        let b_new = &b + &v;
        hash_var(
            cs.clone(),
            &self.cfg,
            DOM_ACCT,
            &[b_new.clone(), kappa, r_new],
        )?
        .enforce_equal(&com_new)?;

        // rho = Com_rec(v, Sen, Rec, nullifier; r'')
        let receipt = hash_var(
            cs.clone(),
            &self.cfg,
            DOM_REC,
            &[v.clone(), sen, rec, nullifier.clone(), r_receipt],
        )?;

        // mmr.Verify(rootrho, rho, pi_mmr) = 1
        enforce_membership(cs.clone(), &self.cfg, &receipt, &root, &self.path)?;

        // mt.AccVerifyInsert(rootnull, nullifier, pi_mt) = rootnull': the
        // indexed nullifier-tree insertion, verified in-circuit; its low-leaf
        // argument proves the nullifier is new (no double-receive).
        let null_key = key_from_field_var(&nullifier)?;
        enforce_indexed_insert(
            cs.clone(),
            &self.cfg,
            &null_key,
            truncate_to_key(self.nullifier),
            &rootnull,
            &rootnull_new,
            &self.null_insert,
        )?;

        // v > 0 and b, v, b + v in B = [0, 2^64): the b + v range check
        // rules out overflow past the balance domain.
        enforce_range_64(cs.clone(), &b, self.b)?;
        enforce_range_64(cs.clone(), &v, self.v)?;
        enforce_range_64(cs, &b_new, self.b.wrapping_add(self.v))?;
        v.enforce_not_equal(&FpVar::zero())?;

        Ok(())
    }
}
