//! The paper's receive relation R_recv, as an R1CS gadget circuit.
//!
//! Statement (public inputs, in the paper's order):
//!   x_r = (R, com, com', root_rho)
//! Witness:
//!   w_r = (b, kappa, root_null, root_null', r, r', rho, pos, pi_mmr,
//!          null, pi_mt, v, S, r'')
//! Constraints:
//!   com  = Com_acct(b, kappa, root_null; r)
//!   com' = Com_acct(b + v, kappa, root_null'; r')
//!   rho  = Com_rec(v, S, R; r'')
//!   mmr.Verify(root_rho, rho, pos, pi_mmr) = 1
//!   null = CRPRF_kappa(recv, pos)
//!   mt.AccVerifyInsert(root_null, null, pi_mt) = root_null'
//!   v > 0   and   b, v, b + v in [0, 2^64)
//!
//! The nullifier and both tree roots are witnesses: they live inside the
//! account commitment, so the account's entire public state is one
//! commitment and neither the nullifier nor a tree root appears on the
//! wire. The nullifier is derived *in-circuit* from the receipt's MMR
//! position under the receiver's committed key (one SHA-256 call — the
//! scheme's only PRF site), then inserted into the receiver's indexed
//! nullifier tree, also in-circuit. Positions are unique, so distinct
//! receipts get distinct nullifiers and no send can block a pending
//! payment (the Faerie-Gold hedge), while the low-leaf argument of the
//! indexed insertion makes a double-receive unwitnessable.
//!
//! The membership path's left/right ordering is driven by the bits of the
//! witnessed `pos` (allocated once, packed into the PRF input), so the same
//! witness position is bound to both the MMR opening and the nullifier —
//! a proof for the right receipt at a wrong position cannot exist.
//!
//! The one remaining native check: `root_rho` is a *revealed anchor* — the
//! receiver computes pi_mmr from the public receipt log against a recent
//! root, and the ledger checks `root_rho` against its retained root history
//! (the W most recent roots) natively.

use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

use super::super::Fr;
use super::enforce_range_64;
use super::hasher::{hash, hash_var, HashCfg, DOM_ACCT, DOM_NULL, DOM_REC};
use super::indexed::{
    enforce_indexed_insert, key_from_field_var, truncate_to_key, IndexedInsertion,
    IndexedMerkleTree,
};
use super::merkle::{alloc_siblings, compute_root_with_bits, MerklePath, MerkleTree};

#[derive(Clone)]
pub struct RecvCircuit {
    pub cfg: HashCfg,
    /// Acting receiver identifier (public).
    pub rec: Fr,
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
    /// Position of the receipt in the MMR (witness; determines the
    /// nullifier and the path ordering).
    pub pos: u64,
    /// Membership path of the receipt under `root`; its length is the
    /// receipt-tree depth and is fixed at keygen time. Only the siblings
    /// are used — the ordering comes from the bits of `pos`.
    pub path: MerklePath,
    /// Witness for inserting the nullifier into the receiver's nullifier
    /// tree; fixes that tree's depth and carries (root_null, root_null').
    pub null_insert: IndexedInsertion,
}

impl RecvCircuit {
    /// A satisfiable instance of the given depths, for keygen and
    /// constraint counting.
    pub fn blank(cfg: &HashCfg, receipt_depth: usize, acct_depth: usize) -> Self {
        let mut receipt_tree = MerkleTree::new(cfg, receipt_depth);
        let mut null_tree = IndexedMerkleTree::new(cfg, acct_depth);
        let mut blank = Self {
            cfg: cfg.clone(),
            rec: Fr::from(0u64),
            root: Fr::from(0u64),
            b: 0,
            v: 1,
            kappa: Fr::from(0u64),
            r: Fr::from(0u64),
            r_new: Fr::from(0u64),
            r_receipt: Fr::from(0u64),
            sen: Fr::from(0u64),
            pos: 0,
            path: MerklePath {
                siblings: vec![],
                index_bits: vec![],
            },
            null_insert: IndexedInsertion::placeholder(),
        };
        blank.pos = receipt_tree.append(blank.receipt()) as u64;
        blank.root = receipt_tree.root();
        blank.path = receipt_tree.path(blank.pos as usize);
        blank.attach_nullifier_insertion(&mut null_tree);
        blank
    }

    /// The position-derived nullifier: CRPRF_kappa(recv, pos), the paper's
    /// SHA-256 call. Never published — only its tree insertion is.
    pub fn nullifier(&self) -> Fr {
        hash(&self.cfg, DOM_NULL, &[self.kappa, Fr::from(self.pos)])
    }

    /// Insert the derived nullifier into the receiver's nullifier tree
    /// (mutating the receiver-side state) and attach the insertion witness.
    /// Requires `kappa` and `pos` to be final.
    pub fn attach_nullifier_insertion(&mut self, null_tree: &mut IndexedMerkleTree) {
        self.null_insert = null_tree.insert(truncate_to_key(self.nullifier()));
    }

    pub fn com(&self) -> Fr {
        hash(
            &self.cfg,
            DOM_ACCT,
            &[
                Fr::from(self.b),
                self.kappa,
                self.null_insert.old_root,
                self.r,
            ],
        )
    }

    pub fn com_new(&self) -> Fr {
        let b_new = Fr::from(self.b) + Fr::from(self.v);
        hash(
            &self.cfg,
            DOM_ACCT,
            &[b_new, self.kappa, self.null_insert.new_root, self.r_new],
        )
    }

    /// The receipt rho this proof consumes (must sit under `root` at `pos`).
    pub fn receipt(&self) -> Fr {
        hash(
            &self.cfg,
            DOM_REC,
            &[Fr::from(self.v), self.sen, self.rec, self.r_receipt],
        )
    }

    /// The statement, in the order the circuit allocates its inputs.
    pub fn public_input(&self) -> Vec<Fr> {
        vec![self.rec, self.com(), self.com_new(), self.root]
    }
}

impl ConstraintSynthesizer<Fr> for RecvCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Statement, allocated first, in the paper's order:
        // (R, com, com', root_rho). The nullifier and both tree roots are
        // witnesses, bound inside the account commitments.
        let rec = FpVar::new_input(cs.clone(), || Ok(self.rec))?;
        let com = FpVar::new_input(cs.clone(), || Ok(self.com()))?;
        let com_new = FpVar::new_input(cs.clone(), || Ok(self.com_new()))?;
        let root = FpVar::new_input(cs.clone(), || Ok(self.root))?;

        // Witness: (b, kappa, root_null, root_null', r, r', ..., v, S, r'').
        let b = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.b)))?;
        let kappa = FpVar::new_witness(cs.clone(), || Ok(self.kappa))?;
        let root_null = FpVar::new_witness(cs.clone(), || Ok(self.null_insert.old_root))?;
        let root_null_new = FpVar::new_witness(cs.clone(), || Ok(self.null_insert.new_root))?;
        let r = FpVar::new_witness(cs.clone(), || Ok(self.r))?;
        let r_new = FpVar::new_witness(cs.clone(), || Ok(self.r_new))?;
        let r_receipt = FpVar::new_witness(cs.clone(), || Ok(self.r_receipt))?;
        let sen = FpVar::new_witness(cs.clone(), || Ok(self.sen))?;
        let v = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.v)))?;

        // The position: allocated as its bits (one per tree level, so
        // pos in [0, 2^depth) by construction) and packed into the field
        // element fed to the PRF. The same bits drive the path ordering.
        let pos_bits = (0..self.path.siblings.len())
            .map(|i| Boolean::new_witness(cs.clone(), || Ok((self.pos >> i) & 1 == 1)))
            .collect::<Result<Vec<_>, _>>()?;
        let pos = Boolean::le_bits_to_fp(&pos_bits)?;

        // com = Com_acct(b, kappa, root_null; r)
        hash_var(
            &self.cfg,
            DOM_ACCT,
            &[b.clone(), kappa.clone(), root_null.clone(), r],
        )?
        .enforce_equal(&com)?;

        // com' = Com_acct(b + v, kappa, root_null'; r') — same PRF key,
        // credited balance, updated nullifier-tree root.
        let b_new = &b + &v;
        hash_var(
            &self.cfg,
            DOM_ACCT,
            &[b_new.clone(), kappa.clone(), root_null_new.clone(), r_new],
        )?
        .enforce_equal(&com_new)?;

        // rho = Com_rec(v, S, R; r'')
        let receipt = hash_var(&self.cfg, DOM_REC, &[v.clone(), sen, rec, r_receipt])?;

        // mmr.Verify(root_rho, rho, pos, pi_mmr) = 1, ordered by pos bits.
        let siblings = alloc_siblings(cs.clone(), &self.path)?;
        compute_root_with_bits(&self.cfg, &receipt, &siblings, &pos_bits)?.enforce_equal(&root)?;

        // null = CRPRF_kappa(recv, pos): the SHA-256 call. Stays in
        // the witness — only its insertion below is visible, and even
        // that is bound inside com' rather than published.
        let nullifier = hash_var(&self.cfg, DOM_NULL, &[kappa, pos])?;

        // mt.AccVerifyInsert(root_null, null, pi_mt) = root_null': the
        // indexed nullifier-tree insertion, verified in-circuit; its low-leaf
        // argument proves the nullifier is new (no double-receive).
        let null_key = key_from_field_var(&nullifier)?;
        enforce_indexed_insert(
            cs.clone(),
            &self.cfg,
            &null_key,
            truncate_to_key(self.nullifier()),
            &root_null,
            &root_null_new,
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
