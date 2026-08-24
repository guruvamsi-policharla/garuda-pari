//! ZK-Pari: Pari with vanishing-polynomial masks, a zero-knowledge SNARK for
//! Square R1CS with committed inputs.
//!
//! This implements the masked, committed-input variant of
//! [Pari](https://eprint.iacr.org/2024/1245.pdf):
//!
//! - The assignment is split into ordinary public inputs, *committed inputs*
//!   (witness variables declared by the circuit, see [`ZkPariCircuit`]), and
//!   private witnesses.
//! - The committed inputs are grouped into independently committed *blocks*:
//!   block `j` has its own trapdoor `delta_j` and its commitment `C_ci_j` is
//!   a Pedersen vector commitment under the basis `(Sigma_ci_j, Gamma_ci_j)`,
//!   hidden by a vanishing-polynomial direction `rho_ci_j * v_K(X)` on the
//!   B-side.
//! - Two further vanishing directions `h(X) * v_K(X)` with `h(X) = eta_1 +
//!   eta_2 * X` mask the A-side, giving the honest-verifier simulator
//!   independent randomness at the verifier challenge and at the SRS trapdoor.
//! - A single Glock-style opening proof accounts for both the ordinary Pari
//!   commitment and the exposed committed-input commitments, so a proof is
//!   `(2 + #blocks) G1 + 1 F` elements. Applications may use slimmer wire
//!   formats when a commitment is recomputable, but must reconstruct the full
//!   `Proof` before verification.
//!
//! The scheme is statistically honest-verifier zero-knowledge with simulation
//! distance at most `1 / (|F| - |K|)`.
//!
//! Verification checks the (3 + #blocks)-pairing equation
//!
//! ```text
//! prod_j e(C_ci_j, delta_j H) * e(T, delta_w H)
//!     = e(U, tau H - r H) * e(v_a alpha G + v_R beta G, H)
//! ```
//!
//! with `v_R = (v_a + x_A(r))^2 - x_B(r)` computed by the verifier
//! (`x_B = 0` after SR1CS instance outlining).
//!
//! # Committed inputs
//!
//! Circuits declare their committed inputs by implementing [`ZkPariCircuit`]:
//! synthesis returns the blocks as lists of witness [`Variable`]s, allocated
//! anywhere in the circuit. Key generation derives the commitment keys from
//! the declared variables, so there is no positional convention to maintain.
//! Plain arkworks [`ConstraintSynthesizer`](ark_relations::gr1cs::ConstraintSynthesizer)
//! circuits can be wrapped in [`Uncommitted`] for proofs without committed
//! inputs.
//!
//! # Batched private transfers
//!
//! The batched-transfer example uses two committed-input blocks: the claimed
//! amounts live in block 1 (size `B+1`), while block 2 holds a single
//! random-linear-combination aggregate `v_theta`. The circuit enforces
//! `sum_i theta^{i-1} v_i = v_theta` for a Fiat-Shamir challenge `theta`
//! bound to the ledger commitments and block-1 commitment, which guarantees
//! (w.h.p.) that the range-checked claimed amounts equal the committed ledger
//! amounts. See `examples/batched_private_transfer.rs`.

use ark_ec::pairing::Pairing;

pub use ark_relations::gr1cs::{ConstraintSystemRef, Variable};
use ark_std::marker::PhantomData;

mod batch_verify;
mod circuit;
pub mod data_structures;
mod generator;
mod prover;
mod simulator;
pub mod utils;
mod verifier;

#[cfg(test)]
mod test;

pub use batch_verify::BatchVerifyTimings;
pub use circuit::{Uncommitted, ZkPariCircuit};
pub use data_structures::{
    CommittedInputOpening, Proof, ProvingKey, SuccinctIndex, Trapdoor, VerifyingKey,
};

/// The ZK-Pari SNARK.
pub struct ZkPari<E: Pairing> {
    _p: PhantomData<E>,
}

impl<E: Pairing> ZkPari<E> {
    /// Transcript domain separator.
    pub const SNARK_NAME: &'static [u8] = b"ZK-Pari";
}
