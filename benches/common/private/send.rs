//! The paper's send relation R_send, as an R1CS gadget circuit.
//!
//! Statement (public inputs, in the paper's order):
//!   x_s = (Sen, com, com', roottag, roottag', rho, tag)
//! Witness:
//!   w_s = (b, kappa, r, r', r'', v, Rec, zeta, pi_mt)
//! Constraints:
//!   com  = Com_acct(b, kappa; r)
//!   com' = Com_acct(b - v, kappa; r')
//!   nullifier = CRPRF_kappa(pay, Sen, zeta)     (stays inside the circuit)
//!   tag       = CRPRF_kappa(pad, Sen, zeta)
//!   rho  = Com_rec(v, Sen, Rec, nullifier; r'')
//!   mt.AccVerifyInsert(roottag, tag, pi_mt) = roottag'   (indexed tree)
//!   1 <= v <= b   and   b, v, b - v in [0, 2^64)
//!
//! (`tag` is the paper's padding nullifier, written nf-hat there.) The
//! tag-tree insertion proof is verified *in-circuit* (see `indexed.rs`), so
//! the ledger's only tag work is comparing `roottag` against its stored
//! root and swapping in `roottag'`. The paper's `Rec in Accounts` line is
//! not enforced here: the receiver need not be registered when the receipt
//! is created. There are no committed-input blocks because account
//! commitments are Poseidon values chained by the ledger.

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
use super::poseidon::{hash, hash_var, DOM_ACCT, DOM_PAD, DOM_PAY, DOM_REC};

#[derive(Clone)]
pub struct SendCircuit {
    pub cfg: PoseidonConfig<Fr>,
    /// Acting sender identifier (public).
    pub sen: Fr,
    /// Current balance.
    pub b: u64,
    /// Transfer amount.
    pub v: u64,
    /// Account PRF key.
    pub kappa: Fr,
    /// Opening randomness: old account, new account, receipt.
    pub r: Fr,
    pub r_new: Fr,
    pub r_receipt: Fr,
    /// Receiver identifier (hidden inside the receipt).
    pub rec: Fr,
    /// Per-payment PRF input.
    pub zeta: Fr,
    /// Witness for inserting the tag into the sender's tag tree; fixes the
    /// tree depth at keygen time and carries (roottag, roottag').
    pub tag_insert: IndexedInsertion,
}

impl SendCircuit {
    /// Insert this payment's tag into the sender's tag tree (mutating the
    /// ledger-side state) and attach the insertion witness.
    pub fn attach_tag_insertion(&mut self, tag_tree: &mut IndexedMerkleTree) {
        self.tag_insert = tag_tree.insert(truncate_to_key(self.tag()));
    }

    pub fn com(&self) -> Fr {
        hash(&self.cfg, DOM_ACCT, &[Fr::from(self.b), self.kappa, self.r])
    }

    pub fn com_new(&self) -> Fr {
        let b_new = Fr::from(self.b) - Fr::from(self.v);
        hash(&self.cfg, DOM_ACCT, &[b_new, self.kappa, self.r_new])
    }

    pub fn nullifier(&self) -> Fr {
        hash(&self.cfg, DOM_PAY, &[self.kappa, self.sen, self.zeta])
    }

    pub fn tag(&self) -> Fr {
        hash(&self.cfg, DOM_PAD, &[self.kappa, self.sen, self.zeta])
    }

    /// The receipt rho published on the ledger and later consumed by R_recv.
    pub fn receipt(&self) -> Fr {
        hash(
            &self.cfg,
            DOM_REC,
            &[
                Fr::from(self.v),
                self.sen,
                self.rec,
                self.nullifier(),
                self.r_receipt,
            ],
        )
    }

    /// The statement, in the order the circuit allocates its inputs.
    pub fn public_input(&self) -> Vec<Fr> {
        vec![
            self.sen,
            self.com(),
            self.com_new(),
            self.tag_insert.old_root,
            self.tag_insert.new_root,
            self.receipt(),
            self.tag(),
        ]
    }
}

impl ConstraintSynthesizer<Fr> for SendCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Statement, allocated first, in the paper's order.
        let sen = FpVar::new_input(cs.clone(), || Ok(self.sen))?;
        let com = FpVar::new_input(cs.clone(), || Ok(self.com()))?;
        let com_new = FpVar::new_input(cs.clone(), || Ok(self.com_new()))?;
        let roottag = FpVar::new_input(cs.clone(), || Ok(self.tag_insert.old_root))?;
        let roottag_new = FpVar::new_input(cs.clone(), || Ok(self.tag_insert.new_root))?;
        let receipt = FpVar::new_input(cs.clone(), || Ok(self.receipt()))?;
        let tag = FpVar::new_input(cs.clone(), || Ok(self.tag()))?;

        // Witness.
        let b = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.b)))?;
        let v = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.v)))?;
        let kappa = FpVar::new_witness(cs.clone(), || Ok(self.kappa))?;
        let r = FpVar::new_witness(cs.clone(), || Ok(self.r))?;
        let r_new = FpVar::new_witness(cs.clone(), || Ok(self.r_new))?;
        let r_receipt = FpVar::new_witness(cs.clone(), || Ok(self.r_receipt))?;
        let rec = FpVar::new_witness(cs.clone(), || Ok(self.rec))?;
        let zeta = FpVar::new_witness(cs.clone(), || Ok(self.zeta))?;

        // com = Com_acct(b, kappa; r)
        hash_var(cs.clone(), &self.cfg, DOM_ACCT, &[b.clone(), kappa.clone(), r])?
            .enforce_equal(&com)?;

        // com' = Com_acct(b - v, kappa; r')
        let b_new = &b - &v;
        hash_var(
            cs.clone(),
            &self.cfg,
            DOM_ACCT,
            &[b_new.clone(), kappa.clone(), r_new],
        )?
        .enforce_equal(&com_new)?;

        // nullifier = CRPRF_kappa(pay, Sen, zeta); stays private here — the
        // receiver reveals it when consuming the receipt.
        let nullifier = hash_var(
            cs.clone(),
            &self.cfg,
            DOM_PAY,
            &[kappa.clone(), sen.clone(), zeta.clone()],
        )?;

        // tag = CRPRF_kappa(pad, Sen, zeta), inserted into the sender's tag tree.
        hash_var(cs.clone(), &self.cfg, DOM_PAD, &[kappa, sen.clone(), zeta])?
            .enforce_equal(&tag)?;

        // rho = Com_rec(v, Sen, Rec, nullifier; r'')
        hash_var(
            cs.clone(),
            &self.cfg,
            DOM_REC,
            &[v.clone(), sen, rec, nullifier, r_receipt],
        )?
        .enforce_equal(&receipt)?;

        // mt.AccVerifyInsert(roottag, tag, pi_mt) = roottag': the indexed
        // tag-tree insertion, verified in-circuit.
        let tag_key = key_from_field_var(&tag)?;
        enforce_indexed_insert(
            cs.clone(),
            &self.cfg,
            &tag_key,
            truncate_to_key(self.tag()),
            &roottag,
            &roottag_new,
            &self.tag_insert,
        )?;

        // 1 <= v <= b and b, v, b - v in B = [0, 2^64): the three range
        // checks make the subtraction non-wrapping, and v != 0 gives v >= 1.
        enforce_range_64(cs.clone(), &b, self.b)?;
        enforce_range_64(cs.clone(), &v, self.v)?;
        enforce_range_64(cs, &b_new, self.b.wrapping_sub(self.v))?;
        v.enforce_not_equal(&FpVar::zero())?;

        Ok(())
    }
}
