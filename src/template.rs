//! The prover template: a circuit's constraint structure, computed once.
//!
//! [`ZkPari::prove`] rebuilds everything from scratch on every call:
//! synthesis (constraints *and* assignments), `finalize` (LC inlining), the
//! R1CS-to-SR1CS adapter, instance outlining, and matrix extraction. All of
//! that is sequential arkworks code — about 0.6 s for the 2^20-constraint
//! payment circuits — and none of it depends on the witness: the SR1CS
//! matrices are fixed by the circuit, and every SR1CS variable is either a
//! copy of an R1CS variable or the adapter's square `(a_i - b_i)^2` of one
//! R1CS row. Left in the prover, that fixed cost caps the multi-core
//! speedup (Amdahl) no matter how well the FFTs and MSMs scale.
//!
//! A [`ProverTemplate`] records exactly the witness-independent part, so
//! [`ZkPari::prove_with_template`] only runs the circuit in witness-only
//! mode (`SynthesisMode::Prove { construct_matrices: false, .. }`, which
//! skips constraint bookkeeping) and rebuilds the SR1CS assignment from the
//! recorded layout, in parallel.
//!
//! # Layout reproduction
//!
//! The template mirrors how `ark-relations` 0.6.0's
//! `Sr1csAdapter::r1cs_to_sr1cs_with_assignment` and
//! `perform_instance_outlining` lay out variables:
//!
//! 1. Rows are visited in order; within a row the `a`, `b`, `c` linear
//!    combinations in that order; within an LC its terms in order. Every
//!    R1CS variable (public or private, but not the constant) becomes an
//!    SR1CS *witness* variable on first appearance. After each row's three
//!    LCs, one witness `s_i = (a_i - b_i)^2` is appended.
//! 2. Each public variable that appeared becomes an SR1CS instance variable,
//!    in ascending R1CS index order.
//! 3. Instance outlining appends witness copies `[1, x_1, .., x_k]` of the
//!    SR1CS instance.
//!
//! Rather than trust that description, [`ProverTemplate::new`] runs the real
//! pipeline once and checks its own reconstruction against the adapter's
//! assignment slot by slot, so an upstream layout change fails loudly at
//! template construction instead of producing unverifiable proofs.
//!
//! Circuits that register the SR1CS predicate natively have no adapter
//! step; for them the template is just the matrices plus the outlining
//! copies.

use std::rc::Rc;

use ark_ff::Field;
use ark_relations::gr1cs::{
    instance_outliner::{outline_sr1cs, InstanceOutliner},
    predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL,
    ConstraintSynthesizer, ConstraintSystem, Matrix, OptimizationGoal, SynthesisError,
    SynthesisMode, R1CS_PREDICATE_LABEL,
};
use ark_relations::sr1cs::Sr1csAdapter;
use ark_std::cfg_iter;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Where one SR1CS witness slot (before the outlining copies) comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Source {
    /// A copy of R1CS variable `j` (index into `[instance || witness]`).
    Var(usize),
    /// The adapter's square variable of R1CS row `i`: `(a_i·z - b_i·z)^2`.
    Square(usize),
}

/// The witness-independent part of proving one circuit; see the module docs.
///
/// Holds the final SR1CS matrices and, for adapter-converted circuits, the
/// R1CS `A`/`B` rows needed for the square variables. For the 2^20-row
/// payment circuits that is a few hundred MB, comparable to the proving key.
#[derive(Clone, Debug)]
pub struct ProverTemplate<F: Field> {
    r1cs_num_instance: usize,
    r1cs_num_witness: usize,
    /// R1CS `A` and `B` rows (post-inlining), for [`Source::Square`].
    /// Empty for native SR1CS circuits.
    r1cs_a: Matrix<F>,
    r1cs_b: Matrix<F>,
    /// SR1CS witness layout, excluding the trailing outlining copies.
    sources: Vec<Source>,
    /// R1CS indices of the variables that form the SR1CS instance
    /// `x_1..x_k` (the constant `1` is implicit).
    instance_vars: Vec<usize>,
    /// Final SR1CS matrices over `[instance || witness]`.
    a: Matrix<F>,
    b: Matrix<F>,
    num_constraints: usize,
}

impl<F: Field> ProverTemplate<F> {
    /// Record the constraint structure of `circuit`.
    ///
    /// `circuit` must carry a full assignment (the same kind of instance one
    /// would prove); it need not satisfy the constraints, since only the
    /// layout is checked here.
    pub fn new<C: ConstraintSynthesizer<F>>(circuit: C) -> Result<Self, SynthesisError> {
        let cs = ConstraintSystem::<F>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Prove {
            construct_matrices: true,
            generate_lc_assignments: true,
        });
        circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let native_sr1cs = cs.has_predicate(SR1CS_PREDICATE_LABEL);
        let mut inner = cs.into_inner().unwrap();

        let r1cs_num_instance = inner.num_instance_variables();
        let r1cs_num_witness = inner.num_witness_variables();
        let mut r1cs_assignment = inner.assignments.instance_assignment.clone();
        r1cs_assignment.extend_from_slice(&inner.assignments.witness_assignment);

        let (r1cs_a, r1cs_b, sources, instance_vars, mut sr1cs) = if native_sr1cs {
            let sources = (r1cs_num_instance..r1cs_num_instance + r1cs_num_witness)
                .map(Source::Var)
                .collect();
            let instance_vars = (1..r1cs_num_instance).collect();
            (Vec::new(), Vec::new(), sources, instance_vars, inner)
        } else {
            let matrices = &inner.to_matrices().unwrap()[R1CS_PREDICATE_LABEL];
            let (sources, instance_vars) = adapter_layout(
                &matrices[0],
                &matrices[1],
                &matrices[2],
                r1cs_num_instance,
                r1cs_num_instance + r1cs_num_witness,
            );
            let (a, b) = (matrices[0].clone(), matrices[1].clone());
            let sr1cs = Sr1csAdapter::r1cs_to_sr1cs_with_assignment(&mut inner)
                .unwrap()
                .into_inner()
                .unwrap();
            (a, b, sources, instance_vars, sr1cs)
        };
        sr1cs
            .perform_instance_outlining(InstanceOutliner {
                pred_label: SR1CS_PREDICATE_LABEL.to_string(),
                func: Rc::new(outline_sr1cs),
            })
            .expect("instance outlining failed");
        assert_eq!(
            sr1cs.num_predicates(),
            1,
            "ZK-Pari supports exactly one predicate (SR1CS); this circuit registered more"
        );
        let matrices = &sr1cs.to_matrices().unwrap()[SR1CS_PREDICATE_LABEL];

        let template = Self {
            r1cs_num_instance,
            r1cs_num_witness,
            r1cs_a,
            r1cs_b,
            sources,
            instance_vars,
            a: matrices[0].clone(),
            b: matrices[1].clone(),
            num_constraints: sr1cs.num_constraints(),
        };

        // The reconstruction must reproduce the real pipeline's assignment
        // exactly; anything else means the layout mirrored above has
        // drifted from ark-relations, and proofs would not verify.
        let (instance, witness) = template.sr1cs_assignment(&r1cs_assignment);
        assert_eq!(
            instance, sr1cs.assignments.instance_assignment,
            "prover template: SR1CS instance layout does not match the adapter"
        );
        assert_eq!(
            witness, sr1cs.assignments.witness_assignment,
            "prover template: SR1CS witness layout does not match the adapter"
        );
        Ok(template)
    }

    /// Number of SR1CS constraints (rows of [`Self::a_matrix`]).
    pub fn num_constraints(&self) -> usize {
        self.num_constraints
    }

    /// The SR1CS `A` matrix over `[instance || witness]`.
    pub fn a_matrix(&self) -> &Matrix<F> {
        &self.a
    }

    /// The SR1CS `B` matrix over `[instance || witness]`.
    pub fn b_matrix(&self) -> &Matrix<F> {
        &self.b
    }

    /// Run `circuit` for its witness values only and lay them out as the
    /// SR1CS `(instance, witness)` assignment.
    ///
    /// # Panics
    ///
    /// If `circuit`'s variable counts differ from the template's.
    pub fn assignment_for<C: ConstraintSynthesizer<F>>(
        &self,
        circuit: C,
    ) -> Result<(Vec<F>, Vec<F>), SynthesisError> {
        let cs = ConstraintSystem::<F>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Prove {
            construct_matrices: false,
            generate_lc_assignments: false,
        });
        circuit.generate_constraints(cs.clone())?;
        let inner = cs.into_inner().unwrap();
        assert_eq!(
            (
                inner.num_instance_variables(),
                inner.num_witness_variables()
            ),
            (self.r1cs_num_instance, self.r1cs_num_witness),
            "circuit shape does not match the prover template"
        );
        let mut z = inner.assignments.instance_assignment;
        z.extend_from_slice(&inner.assignments.witness_assignment);
        Ok(self.sr1cs_assignment(&z))
    }

    /// The SR1CS `(instance, witness)` for the R1CS assignment `z`
    /// (`[instance || witness]`, `z[0] = 1`).
    fn sr1cs_assignment(&self, z: &[F]) -> (Vec<F>, Vec<F>) {
        let mut instance = Vec::with_capacity(1 + self.instance_vars.len());
        instance.push(F::ONE);
        instance.extend(self.instance_vars.iter().map(|&j| z[j]));

        let mut witness: Vec<F> = cfg_iter!(self.sources)
            .map(|source| match *source {
                Source::Var(j) => z[j],
                Source::Square(i) => {
                    (eval_row(&self.r1cs_a[i], z) - eval_row(&self.r1cs_b[i], z)).square()
                }
            })
            .collect();
        // Instance outlining's witness copies `[1, x_1, .., x_k]`.
        witness.extend_from_slice(&instance);
        (instance, witness)
    }
}

/// The adapter's variable layout for the R1CS matrices `(a, b, c)`: the
/// SR1CS witness sources and the R1CS indices that become the instance. See
/// the module docs.
fn adapter_layout<F: Field>(
    a: &Matrix<F>,
    b: &Matrix<F>,
    c: &Matrix<F>,
    num_public: usize,
    num_vars: usize,
) -> (Vec<Source>, Vec<usize>) {
    let mut seen = vec![false; num_vars];
    let mut sources = Vec::with_capacity(num_vars + a.len());
    for (i, ((a_i, b_i), c_i)) in a.iter().zip(b).zip(c).enumerate() {
        for lc in [a_i, b_i, c_i] {
            for &(_, idx) in lc {
                if idx != 0 && !seen[idx] {
                    seen[idx] = true;
                    sources.push(Source::Var(idx));
                }
            }
        }
        sources.push(Source::Square(i));
    }
    let instance_vars = (1..num_public).filter(|&j| seen[j]).collect();
    (sources, instance_vars)
}

#[inline]
fn eval_row<F: Field>(terms: &[(F, usize)], z: &[F]) -> F {
    terms
        .iter()
        .fold(F::zero(), |acc, (coeff, idx)| acc + *coeff * z[*idx])
}
