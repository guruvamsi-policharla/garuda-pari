use ark_ff::Field;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable};
use ark_std::collections::BTreeSet;

/// A circuit for ZK-Pari: synthesizes constraints and *declares* its
/// committed-input blocks.
///
/// Block `j` is an ordered list of witness [`Variable`]s; the proof exposes
/// one Pedersen vector commitment `C_ci_j` per block (under the CRS basis
/// `(Sigma_ci_j, Gamma_ci_j)`, with the values in declaration order).
///
/// Declared variables may be allocated anywhere in the circuit, in any
/// order — including values produced mid-circuit by gadgets. The only
/// requirements, checked at key generation, are that every declared variable
/// is a witness variable, is declared at most once, and appears in at least
/// one constraint (otherwise its CRS basis element would be the identity and
/// the commitment would ignore it).
///
/// Synthesis must be deterministic: key generation and proving re-synthesize
/// the circuit and rely on identical variable assignment (this is the same
/// assumption the rest of the SNARK already makes about the constraint
/// matrices).
pub trait ZkPariCircuit<F: Field> {
    /// Synthesize the constraints and return the committed-input blocks.
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError>;
}

/// Adapter for plain arkworks circuits with no committed inputs.
///
/// Wrap any [`ConstraintSynthesizer`] to use it with ZK-Pari:
/// `ZkPari::<E>::keygen(Uncommitted(circuit), rng)`.
#[derive(Clone)]
pub struct Uncommitted<C>(pub C);

impl<F: Field, C: ConstraintSynthesizer<F>> ZkPariCircuit<F> for Uncommitted<C> {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        self.0.generate_constraints(cs)?;
        Ok(Vec::new())
    }
}

/// Convert declared blocks of [`Variable`]s into blocks of witness indices,
/// enforcing that every declared variable is a witness and that no variable
/// is declared twice.
pub(crate) fn blocks_to_witness_indices(blocks: &[Vec<Variable>]) -> Vec<Vec<usize>> {
    let mut seen = BTreeSet::new();
    blocks
        .iter()
        .map(|block| {
            block
                .iter()
                .map(|v| {
                    assert!(
                        v.is_witness(),
                        "committed inputs must be witness variables (instance variables are \
                         already public)"
                    );
                    let index = v
                        .get_variable_index(0)
                        .expect("witness variables always carry an index");
                    assert!(
                        seen.insert(index),
                        "witness variable {index} is declared as a committed input more than once"
                    );
                    index
                })
                .collect()
        })
        .collect()
}
