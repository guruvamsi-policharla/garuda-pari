//! The paper's send relation R_send, as an R1CS gadget circuit.
//!
//! Statement (public inputs, in the paper's order):
//!   x_s = (S, com, com', rho)
//! Witness:
//!   w_s = (b, kappa, root_null, r, r', r'', v, R)
//! Constraints:
//!   com  = Com_acct(b, kappa, root_null; r)
//!   com' = Com_acct(b - v, kappa, root_null; r')
//!   rho  = Com_rec(v, S, R; r'')
//!   1 <= v <= b   and   b, v, b - v in [0, 2^64)
//!
//! There is no hashing beyond the three Pedersen commitment openings:
//! the PRF key and the owner's indexed-nullifier-tree root are bound
//! inside the account commitment and stay unchanged across a send.
//! Nullifier derivation is the receiver's job (from the receipt's MMR
//! position under the receiver's key, see `recv.rs`), so a send touches no
//! tree and no PRF, and the circuit has no depth parameter. The paper's
//! `R in Accounts` line is not enforced here: the receiver need not be
//! registered when the receipt is created. There are no committed-input
//! blocks because account commitments are hash values chained by the
//! ledger — one commitment is the account's entire public state.

use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

use super::super::Fr;
use super::enforce_range_64;
use super::hasher::{hash, hash_var, HashCfg, DOM_ACCT, DOM_REC};

#[derive(Clone)]
pub struct SendCircuit {
    pub cfg: HashCfg,
    /// Acting sender identifier (public).
    pub sen: Fr,
    /// Current balance.
    pub b: u64,
    /// Transfer amount.
    pub v: u64,
    /// Account PRF key.
    pub kappa: Fr,
    /// Root of the sender's indexed nullifier tree (unchanged across send).
    pub root_null: Fr,
    /// Opening randomness: old account, new account, receipt.
    pub r: Fr,
    pub r_new: Fr,
    pub r_receipt: Fr,
    /// Receiver identifier (hidden inside the receipt).
    pub rec: Fr,
}

impl SendCircuit {
    pub fn com(&self) -> Fr {
        hash(
            &self.cfg,
            DOM_ACCT,
            &[Fr::from(self.b), self.kappa, self.root_null, self.r],
        )
    }

    pub fn com_new(&self) -> Fr {
        let b_new = Fr::from(self.b) - Fr::from(self.v);
        hash(
            &self.cfg,
            DOM_ACCT,
            &[b_new, self.kappa, self.root_null, self.r_new],
        )
    }

    /// The receipt rho published on the ledger and later consumed by R_recv.
    pub fn receipt(&self) -> Fr {
        hash(
            &self.cfg,
            DOM_REC,
            &[Fr::from(self.v), self.sen, self.rec, self.r_receipt],
        )
    }

    /// The statement, in the order the circuit allocates its inputs.
    pub fn public_input(&self) -> Vec<Fr> {
        vec![self.sen, self.com(), self.com_new(), self.receipt()]
    }
}

impl ConstraintSynthesizer<Fr> for SendCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Statement, allocated first, in the paper's order.
        let sen = FpVar::new_input(cs.clone(), || Ok(self.sen))?;
        let com = FpVar::new_input(cs.clone(), || Ok(self.com()))?;
        let com_new = FpVar::new_input(cs.clone(), || Ok(self.com_new()))?;
        let receipt = FpVar::new_input(cs.clone(), || Ok(self.receipt()))?;

        // Witness: (b, kappa, root_null, r, r', r'', v, R).
        let b = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.b)))?;
        let kappa = FpVar::new_witness(cs.clone(), || Ok(self.kappa))?;
        let root_null = FpVar::new_witness(cs.clone(), || Ok(self.root_null))?;
        let r = FpVar::new_witness(cs.clone(), || Ok(self.r))?;
        let r_new = FpVar::new_witness(cs.clone(), || Ok(self.r_new))?;
        let r_receipt = FpVar::new_witness(cs.clone(), || Ok(self.r_receipt))?;
        let v = FpVar::new_witness(cs.clone(), || Ok(Fr::from(self.v)))?;
        let rec = FpVar::new_witness(cs.clone(), || Ok(self.rec))?;

        // com = Com_acct(b, kappa, root_null; r)
        hash_var(
            &self.cfg,
            DOM_ACCT,
            &[b.clone(), kappa.clone(), root_null.clone(), r],
        )?
        .enforce_equal(&com)?;

        // com' = Com_acct(b - v, kappa, root_null; r') — same key and root.
        let b_new = &b - &v;
        hash_var(
            &self.cfg,
            DOM_ACCT,
            &[b_new.clone(), kappa, root_null, r_new],
        )?
        .enforce_equal(&com_new)?;

        // rho = Com_rec(v, S, R; r'')
        hash_var(&self.cfg, DOM_REC, &[v.clone(), sen, rec, r_receipt])?.enforce_equal(&receipt)?;

        // 1 <= v <= b and b, v, b - v in B = [0, 2^64): the three range
        // checks make the subtraction non-wrapping, and v != 0 gives v >= 1.
        enforce_range_64(cs.clone(), &b, self.b)?;
        enforce_range_64(cs.clone(), &v, self.v)?;
        enforce_range_64(cs, &b_new, self.b.wrapping_sub(self.v))?;
        v.enforce_not_equal(&FpVar::zero())?;

        Ok(())
    }
}
