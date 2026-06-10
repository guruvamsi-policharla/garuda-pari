use std::rc::Rc;

use ark_ec::{pairing::Pairing, scalar_mul::BatchMulPreprocessing};
use ark_ff::{Field, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::circuit::{blocks_to_witness_indices, ZkPariCircuit};
use crate::data_structures::{ProvingKey, SuccinctIndex, VerifyingKey};
use crate::ZkPari;
use ark_relations::{
    gr1cs::{
        self,
        instance_outliner::{outline_sr1cs, InstanceOutliner},
        predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL,
        ConstraintSystem, OptimizationGoal, SynthesisError, SynthesisMode,
    },
    sr1cs::Sr1csAdapter,
};
use ark_std::{end_timer, rand::RngCore, start_timer, vec::Vec, UniformRand};

impl<E: Pairing> ZkPari<E> {
    /// Generate proving and verifying keys.
    ///
    /// The circuit declares its committed-input blocks (see [`ZkPariCircuit`]);
    /// block `j` is committed in `C_ci_j` under its own trapdoor `delta_j`,
    /// and all remaining witness variables are committed in `T` under
    /// `delta_w`. Plain arkworks circuits can be passed as
    /// [`crate::Uncommitted`] for proofs without committed inputs.
    pub fn keygen<C: ZkPariCircuit<E::ScalarField>, R: RngCore>(
        circuit: C,
        rng: &mut R,
    ) -> (ProvingKey<E>, VerifyingKey<E>)
    where
        E: Pairing,
        E::ScalarField: Field,
    {
        let (cs, block_indices) = Self::circuit_to_keygen_cs(circuit).unwrap();
        // Check if the constraint system has only one predicate which is Squared R1CS
        #[cfg(debug_assertions)]
        {
            assert_eq!(cs.num_predicates(), 1);
            assert_eq!(
                cs.num_constraints(),
                cs.get_predicate_num_constraints(SR1CS_PREDICATE_LABEL)
                    .unwrap()
            );
        }

        /////////////////////// Extract the constraint system information ///////////////////////
        let instance_len = cs.num_instance_variables();
        let num_constraints = cs.num_constraints();
        let num_witness = cs.num_witness_variables();
        let block_sizes: Vec<usize> = block_indices.iter().map(Vec::len).collect();

        // Mark the committed witnesses; everything else is committed in T
        let mut is_committed = vec![false; num_witness];
        for block in &block_indices {
            for &w in block {
                is_committed[w] = true;
            }
        }
        let ordinary_indices: Vec<usize> = (0..num_witness).filter(|w| !is_committed[*w]).collect();

        /////////////////////// Generators ///////////////////////
        let timer_sample_generators = start_timer!(|| "Sample generators");
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);
        end_timer!(timer_sample_generators);

        /////////////////////// Trapdoor generation ///////////////////////
        let timer_trapdoor_gen = start_timer!(|| "Trapdoor generation and exponentiations");
        let alpha = E::ScalarField::rand(rng);
        let beta = E::ScalarField::rand(rng);
        // One delta_j per committed-input block, plus delta_w for the witnesses
        let deltas: Vec<E::ScalarField> = (0..block_indices.len())
            .map(|_| E::ScalarField::rand(rng))
            .collect();
        let delta_w = E::ScalarField::rand(rng);
        let tau = E::ScalarField::rand(rng);

        let alpha_g: <E as Pairing>::G1 = g * alpha;
        let beta_g = g * beta;
        let delta_h: Vec<E::G2Affine> = deltas.iter().map(|d| (h * d).into()).collect();
        let delta_w_h = h * delta_w;
        let tau_h = h * tau;

        let delta_inverses: Vec<E::ScalarField> =
            deltas.iter().map(|d| d.inverse().unwrap()).collect();
        let delta_w_inverse = delta_w.inverse().unwrap();
        end_timer!(timer_trapdoor_gen);

        /////////////////////// Computing the FFT domain ///////////////////////
        let timer_fft_domain = start_timer!(|| "Computing the FFT domain");
        let domain = Radix2EvaluationDomain::new(num_constraints).unwrap();
        // tau must lie outside the interpolation domain K
        let v_k_at_tau = domain.evaluate_vanishing_polynomial(tau);
        assert_ne!(v_k_at_tau, E::ScalarField::zero());
        end_timer!(timer_fft_domain);
        let domain_size = domain.size();

        /////////////////////// Computing {a_i(tau)}, {b_i(tau)} ///////////////////////
        let timer_compute_a_b = start_timer!(|| "Computing a_i(tau)'s and b_i(tau)'s");
        let (a, b) = Self::compute_ai_bi_at_tau(tau, &cs, domain).unwrap();
        end_timer!(timer_compute_a_b);

        // A committed input must appear in some constraint, otherwise its CRS
        // basis element is the identity and the commitment would ignore it
        for block in &block_indices {
            for &w in block {
                assert!(
                    !(a[instance_len + w].is_zero() && b[instance_len + w].is_zero()),
                    "committed input (witness variable {w}) does not appear in any constraint; \
                     its commitment basis element would be the identity"
                );
            }
        }

        /////////////////////// Succinct Index ///////////////////////
        let succinct_index = SuccinctIndex {
            num_constraints,
            instance_len,
            committed_input_blocks: block_sizes,
        };

        /////////////////////// Powers of tau ///////////////////////
        // Sigma_R needs the largest range: beta * tau^i for i = 0..=2m+1,
        // where m is the (padded) domain size.
        let timer_powers_of_tau = start_timer!(|| "Computing powers of tau");
        let max_power = 2 * domain_size + 1;
        let mut powers_of_tau = Vec::with_capacity(max_power + 1);
        let mut cur = E::ScalarField::ONE;
        for _ in 0..=max_power {
            powers_of_tau.push(cur);
            cur *= &tau;
        }
        end_timer!(timer_powers_of_tau);

        /////////////////////// Proving key generation ///////////////////////
        let timer_pk_gen = start_timer!(|| "Generating Proving Key");

        let timer_batch_mul_prep = start_timer!(|| "Batch Mul Preprocessing startup");
        let table = BatchMulPreprocessing::new(g, max_power + 1);
        end_timer!(timer_batch_mul_prep);

        /////////////////////// Opening Keys ///////////////////////
        let timer_opening_keys = start_timer!(|| "Computing Opening Keys");

        // Sigma_A = [alpha tau^i G]_{i=0}^{m}: opens W_A of degree <= m
        let timer_sigma_a = start_timer!(|| "Computing sigma_a");
        let sigma_a_powers = powers_of_tau[0..domain_size + 1]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * alpha)
            .collect::<Vec<_>>();
        let sigma_a = table.batch_mul(&sigma_a_powers);
        end_timer!(timer_sigma_a);

        // Sigma_R = [beta tau^i G]_{i=0}^{2m+1}: opens W_R of degree <= 2m+1
        let timer_sigma_r = start_timer!(|| "Computing sigma_r");
        let sigma_r_powers = powers_of_tau[0..2 * domain_size + 2]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * beta)
            .collect::<Vec<_>>();
        let sigma_r = table.batch_mul(&sigma_r_powers);
        end_timer!(timer_sigma_r);
        end_timer!(timer_opening_keys);

        /////////////////////// Commitment Keys ///////////////////////
        let timer_commit_keys = start_timer!(|| "Computing Committing Keys");

        // Per block j:
        //   Sigma_ci_j = [(alpha a_i(tau) + beta b_i(tau))/delta_j G] for i in block j
        //   Gamma_ci_j = (beta v_K(tau)/delta_j) G: blinding direction of C_ci_j
        let timer_sigma_ci = start_timer!(|| "Computing sigma_ci");
        let mut sigma_ci = Vec::with_capacity(block_indices.len());
        let mut gamma_ci = Vec::with_capacity(block_indices.len());
        for (block, delta_j_inverse) in block_indices.iter().zip(&delta_inverses) {
            let alpha_over_delta_j = alpha * delta_j_inverse;
            let beta_over_delta_j = beta * delta_j_inverse;
            let sigma_ci_powers = block
                .par_iter()
                .map(|&w| {
                    a[instance_len + w] * alpha_over_delta_j
                        + b[instance_len + w] * beta_over_delta_j
                })
                .collect::<Vec<_>>();
            sigma_ci.push(table.batch_mul(&sigma_ci_powers));
            gamma_ci.push((g * (beta * v_k_at_tau * delta_j_inverse)).into());
        }
        end_timer!(timer_sigma_ci);

        // Sigma_W = [(alpha a_i(tau) + beta b_i(tau))/delta_w G] for the
        // ordinary witnesses, in ascending witness-index order
        let timer_sigma_w = start_timer!(|| "Computing sigma_w");
        let alpha_over_delta_w = alpha * delta_w_inverse;
        let beta_over_delta_w = beta * delta_w_inverse;
        let sigma_w_powers = ordinary_indices
            .par_iter()
            .map(|&w| {
                a[instance_len + w] * alpha_over_delta_w + b[instance_len + w] * beta_over_delta_w
            })
            .collect::<Vec<_>>();
        let sigma_w = table.batch_mul(&sigma_w_powers);
        end_timer!(timer_sigma_w);

        // A-side mask keys: (alpha v_K(tau)/delta_w) G and (alpha tau v_K(tau)/delta_w) G
        let sigma_mask_const: E::G1Affine = (g * (alpha * v_k_at_tau * delta_w_inverse)).into();
        let sigma_mask_linear: E::G1Affine =
            (g * (alpha * tau * v_k_at_tau * delta_w_inverse)).into();

        // Sigma_Q^comm = [(beta v_K(tau) tau^i / delta_w) G]_{i=0}^{m+2}
        let timer_q_comm = start_timer!(|| "Computing sigma_q_comm");
        let beta_v_k_over_delta_w = beta * v_k_at_tau * delta_w_inverse;
        let sigma_q_comm_powers = powers_of_tau[0..domain_size + 3]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * beta_v_k_over_delta_w)
            .collect::<Vec<_>>();
        let sigma_q_comm = table.batch_mul(&sigma_q_comm_powers);
        end_timer!(timer_q_comm);
        end_timer!(timer_commit_keys);
        end_timer!(timer_pk_gen);

        /////////////////////// Output keys ///////////////////////
        let vk = VerifyingKey {
            succinct_index,
            alpha_g: alpha_g.into(),
            beta_g: beta_g.into(),
            delta_h_prep: delta_h.iter().map(|d| (*d).into()).collect(),
            delta_h,
            delta_w_h: delta_w_h.into(),
            delta_w_h_prep: delta_w_h.into().into(),
            tau_h: tau_h.into(),
            tau_h_prep: tau_h.into().into(),
            g: g.into(),
            h: h.into(),
            h_prep: h.into().into(),
            domain,
        };

        let pk = ProvingKey {
            sigma_ci,
            gamma_ci,
            committed_witness_indices: block_indices,
            sigma_w,
            sigma_mask_const,
            sigma_mask_linear,
            sigma_q_comm,
            sigma_a,
            sigma_r,
            verifying_key: vk.clone(),
        };

        (pk, vk)
    }

    /// Synthesize the circuit in setup mode and return the finalized SR1CS
    /// constraint system together with the declared committed-input blocks
    /// (as witness indices).
    #[allow(clippy::type_complexity)]
    pub fn circuit_to_keygen_cs<C: ZkPariCircuit<E::ScalarField>>(
        circuit: C,
    ) -> Result<(ConstraintSystem<E::ScalarField>, Vec<Vec<usize>>), SynthesisError>
    where
        E: Pairing,
        E::ScalarField: Field,
    {
        // Start up the constraint System and synthesize the circuit
        let timer_cs_startup = start_timer!(|| "Constraint System Startup");
        let cs: gr1cs::ConstraintSystemRef<E::ScalarField> = ConstraintSystem::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        let blocks = circuit.synthesize(cs.clone())?;
        let block_indices = blocks_to_witness_indices(&blocks);
        cs.finalize();
        // Circuits that natively register the SR1CS predicate skip the R1CS-to-SR1CS conversion.
        // Both the conversion and the instance outlining only append witness
        // variables, so the declared indices stay valid.
        let native_sr1cs = cs.has_predicate(SR1CS_PREDICATE_LABEL);

        let timer_inlining = start_timer!(|| "Inlining constraints");
        let mut sr1cs_inner = if native_sr1cs {
            cs.into_inner().unwrap()
        } else {
            let sr1cs_cs = Sr1csAdapter::r1cs_to_sr1cs(&cs).unwrap();
            sr1cs_cs.set_instance_outliner(InstanceOutliner {
                pred_label: SR1CS_PREDICATE_LABEL.to_string(),
                func: Rc::new(outline_sr1cs),
            });
            sr1cs_cs.into_inner().unwrap()
        };
        let _ = sr1cs_inner.perform_instance_outlining(InstanceOutliner {
            pred_label: SR1CS_PREDICATE_LABEL.to_string(),
            func: Rc::new(outline_sr1cs),
        });
        end_timer!(timer_inlining);
        end_timer!(timer_cs_startup);
        Ok((sr1cs_inner, block_indices))
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn compute_ai_bi_at_tau(
        tau: E::ScalarField,
        new_cs: &ConstraintSystem<E::ScalarField>,
        domain: Radix2EvaluationDomain<E::ScalarField>,
    ) -> Result<(Vec<E::ScalarField>, Vec<E::ScalarField>), SynthesisError> {
        // Compute all the lagrange polynomials
        let timer_eval_all_lagrange_polys = start_timer!(|| "Evaluating all Lagrange polys");
        let lagrange_polys_at_tau = domain.evaluate_all_lagrange_coefficients(tau);
        end_timer!(timer_eval_all_lagrange_polys);

        let num_variables = new_cs.num_instance_variables() + new_cs.num_witness_variables();
        let num_constraints = new_cs.num_constraints();
        let matrices = &new_cs.to_matrices().unwrap()[SR1CS_PREDICATE_LABEL];

        let mut a = vec![E::ScalarField::zero(); num_variables];
        let mut b = vec![E::ScalarField::zero(); num_variables];

        let timer_compute_a_b = start_timer!(|| "Compute a_i(tau)'s and z_i(tau)'s");
        for (i, u_i) in lagrange_polys_at_tau
            .iter()
            .enumerate()
            .take(num_constraints)
        {
            for &(ref coeff, index) in &matrices[0][i] {
                a[index] += &(*u_i * coeff);
            }
            for &(ref coeff, index) in &matrices[1][i] {
                b[index] += &(*u_i * coeff);
            }
        }
        end_timer!(timer_compute_a_b);
        Ok((a, b))
    }
}
