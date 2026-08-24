use ark_ff::Field;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, Matrix, SynthesisError, Variable,
};
use ark_std::collections::{BTreeMap, BTreeSet};

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

/// Witness-index map of `Sr1csAdapter::r1cs_to_sr1cs[_with_assignment]`:
/// old witness index -> witness index in the converted constraint system.
///
/// The adapter does *not* preserve witness indices: it rebuilds the witness
/// space from scratch, scanning the R1CS rows in order (per row: the A-,
/// then B-, then C-side linear combination, terms in order) and allocating
/// the next new witness index to each previously unseen variable — original
/// *instance* variables included, since they get witness copies — followed
/// by one fresh square witness per row. This function replays that scan over
/// the same matrices the adapter reads, so declared committed-input indices
/// can be remapped into the converted numbering. The prover cross-checks the
/// result against the converted assignment, so any upstream change to the
/// adapter's allocation order fails loudly there.
pub(crate) fn r1cs_conversion_witness_map<F: Field>(
    r1cs_matrices: &[Matrix<F>],
    num_instance: usize,
) -> BTreeMap<usize, usize> {
    let num_rows = r1cs_matrices.iter().map(Vec::len).min().unwrap_or(0);
    // Old absolute variable index -> new witness index
    let mut new_index: BTreeMap<usize, usize> = BTreeMap::new();
    let mut next = 0usize;
    for row in 0..num_rows {
        for matrix in r1cs_matrices {
            for &(_, index) in &matrix[row] {
                // Variable::One stays Variable::One; everything else gets a
                // new witness on first use
                if index == 0 {
                    continue;
                }
                new_index.entry(index).or_insert_with(|| {
                    let assigned = next;
                    next += 1;
                    assigned
                });
            }
        }
        // The adapter allocates one square witness per R1CS row
        next += 1;
    }
    // Keep only the original witnesses, rebased to witness-vector indices
    new_index
        .into_iter()
        .filter(|&(old, _)| old >= num_instance)
        .map(|(old, new)| (old - num_instance, new))
        .collect()
}

/// Remap declared committed-input blocks through the R1CS-to-SR1CS
/// conversion's witness map (see [`r1cs_conversion_witness_map`]).
///
/// Panics if a declared variable appears in no constraint: it then has no
/// column in the converted system, so no commitment basis element exists
/// for it and the commitment would silently ignore the value.
pub(crate) fn remap_blocks_through_conversion(
    blocks: &[Vec<usize>],
    map: &BTreeMap<usize, usize>,
) -> Vec<Vec<usize>> {
    blocks
        .iter()
        .map(|block| {
            block
                .iter()
                .map(|w| {
                    *map.get(w).unwrap_or_else(|| {
                        panic!(
                            "committed input (witness variable {w}) does not appear in any \
                             constraint; it has no column in the converted SR1CS system"
                        )
                    })
                })
                .collect()
        })
        .collect()
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

/// Panic unless instance outlining left the matrices in the shape the verifier
/// assumes: every instance column confined to the trailing `num_instance`
/// rows (the outlining equality rows).
///
/// The verifier reconstructs the public contribution as
/// `x_A(r) = sum_i x_i L_{outline_start + i}(r)` — a Lagrange sum over those
/// trailing rows only — and takes `x_B = 0` outright. An instance column
/// anywhere else is silently unaccounted for, so honest proofs fail to verify
/// with no other symptom.
///
/// This is reachable through a live bug in `ark-relations` 0.6.0:
/// `ConstraintSystem::new_lc_add_helper` returns a coefficient-1
/// single-variable linear combination as the bare `Variable` instead of
/// interning it in `lc_map`, while `perform_instance_outlining` rewrites
/// instance variables *only* by iterating `lc_map`. A constraint side written
/// as exactly `lc!() + <public input>` therefore keeps a live instance column.
/// Writing that side with two or more terms (or a non-unit coefficient) routes
/// it through `lc_map` and outlines correctly.
///
/// Circuits reaching ZK-Pari through the R1CS-to-SR1CS adapter are unaffected:
/// the adapter rebuilds the witness space from the matrices, so instance
/// variables never survive into the converted linear combinations.
///
/// Checked once at key generation, over matrices key generation already
/// materializes, so it costs nothing per proof.
pub(crate) fn assert_instance_outlining_complete<F: Field>(
    matrices: &[Matrix<F>],
    num_instance: usize,
    num_constraints: usize,
) {
    let outline_start = num_constraints.saturating_sub(num_instance);
    for (matrix, side) in matrices.iter().zip(["A", "B"]) {
        for (row, terms) in matrix.iter().enumerate().take(outline_start) {
            for &(_, index) in terms {
                assert!(
                    index >= num_instance,
                    "instance outlining did not remove instance variable {index} from row \
                     {row} of the {side} matrix (outlining rows start at {outline_start}). \
                     The verifier only accounts for instance columns in the trailing \
                     {num_instance} rows, so this circuit would produce proofs that fail to \
                     verify. Cause: a constraint side written as a bare `lc!() + <variable>` \
                     is not interned into the constraint system's LC map and so escapes \
                     outlining; rewrite that side with two or more terms (for example \
                     `lc!() + x - y`) so it is outlined."
                );
            }
        }
    }
}
