use std::rc::Rc;

use ark_ec::{pairing::Pairing, scalar_mul::BatchMulPreprocessing};
use ark_ff::{Field, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::{
    data_structures::{ProvingKey, SuccinctIndex, VerifyingKey},
    Pari,
};
use ark_relations::{
    gr1cs::{
        self,
        instance_outliner::{outline_sr1cs, InstanceOutliner},
        predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL,
        ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisError, SynthesisMode,
    },
    sr1cs::Sr1csAdapter,
};
use ark_std::{end_timer, rand::RngCore, start_timer, vec::Vec, UniformRand};

impl<E: Pairing> Pari<E> {
    /// Generate proving and verifying keys for ZK-Pari.
    ///
    /// `witness_split` is the number of witness variables (in post-outlining order)
    /// committed via sigma_1 / delta_1. The remaining witness variables use sigma_2 / delta_2.
    pub fn keygen<C: ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
        circuit: C,
        witness_split: usize,
        rng: &mut R,
    ) -> (ProvingKey<E>, VerifyingKey<E>)
    where
        E: Pairing,
        E::ScalarField: Field,
    {
        let cs = Self::circuit_to_keygen_cs(circuit).unwrap();
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
        assert!(
            witness_split <= num_witness,
            "witness_split ({witness_split}) exceeds number of witness variables ({num_witness})"
        );

        /////////////////////// Generators ///////////////////////
        let timer_sample_generators = start_timer!(|| "Sample generators");
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);
        end_timer!(timer_sample_generators);

        /////////////////////// Trapdoor generation ///////////////////////
        let timer_trapdoor_gen = start_timer!(|| "Trapdoor generation and exponentiations");
        let alpha = E::ScalarField::rand(rng);
        let beta = E::ScalarField::rand(rng);
        let gamma = E::ScalarField::rand(rng);
        let delta_one = E::ScalarField::rand(rng);
        let delta_two = E::ScalarField::rand(rng);
        let tau = E::ScalarField::rand(rng);

        let alpha_g: <E as Pairing>::G1 = g * alpha;
        let beta_g = g * beta;
        let gamma_h = h * gamma;
        let delta_one_h = h * delta_one;
        let delta_two_h = h * delta_two;
        let tau_h = h * tau;

        let delta_one_inverse = delta_one.inverse().unwrap();
        let delta_two_inverse = delta_two.inverse().unwrap();

        let alpha_over_delta_one = alpha * delta_one_inverse;
        let beta_over_delta_one = beta * delta_one_inverse;
        let alpha_over_delta_two = alpha * delta_two_inverse;
        let beta_over_delta_two = beta * delta_two_inverse;
        end_timer!(timer_trapdoor_gen);

        /////////////////////// Computing the FFT domain ///////////////////////
        let timer_fft_domain = start_timer!(|| "Computing the FFT domain");
        let domain = Radix2EvaluationDomain::new(cs.num_constraints()).unwrap();
        let v_k_at_tau = domain.evaluate_vanishing_polynomial(tau);
        assert_ne!(v_k_at_tau, E::ScalarField::zero());
        end_timer!(timer_fft_domain);
        let domain_size = domain.size();
        let max_degree = domain_size - 1;

        /////////////////////// Computing {a_i(tau)}, {b_i(tau)} ////////////////////////
        let timer_compute_a_b = start_timer!(|| "Computing a_i(tau)'s and b_i(tau)'s");
        let (a, b) = Self::compute_ai_bi_at_tau(tau, &cs, domain).unwrap();
        end_timer!(timer_compute_a_b);

        /////////////////////// Succinct Index ///////////////////////
        let timer_succinct_index = start_timer!(|| "Generating Succinct Index");
        let num_public_inputs = cs.num_instance_variables();
        let succinct_index = SuccinctIndex {
            num_constraints,
            instance_len,
            witness_split,
        };
        end_timer!(timer_succinct_index);

        /////////////////////// Powers of tau ///////////////////////
        let timer_powers_of_tau = start_timer!(|| "Computing powers of tau");
        let mut powers_of_tau = vec![E::ScalarField::ONE];
        let mut cur = tau;
        // Need max_degree + 2 powers for sigma_q_comm (m+1 entries, indices 0..=m)
        for _ in 0..=max_degree + 1 {
            powers_of_tau.push(cur);
            cur *= &tau;
        }
        end_timer!(timer_powers_of_tau);

        /////////////////////// Proving key generation ///////////////////////
        let timer_pk_gen = start_timer!(|| "Generating Proving Key");

        let timer_batch_mul_prep = start_timer!(|| "Batch Mul Preprocessing startup");
        let table = BatchMulPreprocessing::new(g, max_degree + 2);
        end_timer!(timer_batch_mul_prep);

        /////////////////////// Opening Keys ///////////////////////
        let timer_opening_keys = start_timer!(|| "Computing Opening Keys");

        // Sigma_A: [alpha * tau^i * G] for i = 0..m-1 (m entries)
        let timer_sigma_a = start_timer!(|| "Computing sigma_a");
        let sigma_a_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * alpha)
            .collect::<Vec<_>>();
        let sigma_a = table.batch_mul(&sigma_a_powers);
        end_timer!(timer_sigma_a);

        // Sigma_B: [beta * tau^i * G] for i = 0..m-1 (m entries)
        let timer_sigma_b = start_timer!(|| "Computing sigma_b");
        let sigma_b_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * beta)
            .collect::<Vec<_>>();
        let sigma_b = table.batch_mul(&sigma_b_powers);
        end_timer!(timer_sigma_b);

        // Sigma_Q_opening: [tau^i * G] for i = 0..m-1 (m entries)
        let timer_sigma_q_opening = start_timer!(|| "Computing sigma_q_opening");
        let sigma_q_opening_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .copied()
            .collect::<Vec<_>>();
        let sigma_q_opening = table.batch_mul(&sigma_q_opening_powers);
        end_timer!(timer_sigma_q_opening);
        end_timer!(timer_opening_keys);

        /////////////////////// Commitment Keys ///////////////////////
        let timer_commit_keys = start_timer!(|| "Computing Commitment Keys");

        // Sigma_1: [(alpha*a_i(tau) + beta*b_i(tau))/delta_1 * G] for witness vars in partition 1
        let timer_sigma_1 = start_timer!(|| "Computing sigma_1");
        let sigma_1_powers = a[num_public_inputs..num_public_inputs + witness_split]
            .par_iter()
            .zip(&b[num_public_inputs..num_public_inputs + witness_split])
            .map(|(a_i, b_i)| *a_i * alpha_over_delta_one + *b_i * beta_over_delta_one)
            .collect::<Vec<_>>();
        let sigma_1 = table.batch_mul(&sigma_1_powers);
        end_timer!(timer_sigma_1);

        // Sigma_2: [(alpha*a_i(tau) + beta*b_i(tau))/delta_2 * G] for witness vars in partition 2
        let timer_sigma_2 = start_timer!(|| "Computing sigma_2");
        let sigma_2_powers = a[num_public_inputs + witness_split..]
            .par_iter()
            .zip(&b[num_public_inputs + witness_split..])
            .map(|(a_i, b_i)| *a_i * alpha_over_delta_two + *b_i * beta_over_delta_two)
            .collect::<Vec<_>>();
        let sigma_2 = table.batch_mul(&sigma_2_powers);
        end_timer!(timer_sigma_2);

        // Sigma_Q_comm: [tau^i / delta_2 * G] for i = 0..m (m+1 entries for blinded quotient)
        let timer_q_comm = start_timer!(|| "Computing sigma_q_comm");
        let sigma_q_comm_powers = powers_of_tau[0..max_degree + 2]
            .par_iter()
            .map(|tau_pow| *tau_pow * delta_two_inverse)
            .collect::<Vec<_>>();
        let sigma_q_comm = table.batch_mul(&sigma_q_comm_powers);
        end_timer!(timer_q_comm);
        end_timer!(timer_commit_keys);

        /////////////////////// ZK Commitment Keys ///////////////////////
        let timer_zk_keys = start_timer!(|| "Computing ZK commitment keys");
        let sigma_a_zk_1: E::G1Affine = (g * (alpha * v_k_at_tau * delta_one_inverse)).into();
        let sigma_b_zk_1: E::G1Affine = (g * (beta * v_k_at_tau * delta_one_inverse)).into();
        let sigma_a_zk_2: E::G1Affine = (g * (alpha * v_k_at_tau * delta_two_inverse)).into();
        let sigma_b_zk_2: E::G1Affine = (g * (beta * v_k_at_tau * delta_two_inverse)).into();
        end_timer!(timer_zk_keys);

        /////////////////////// Hiding Elements ///////////////////////
        let timer_hiding = start_timer!(|| "Computing hiding elements");
        let gamma_over_delta_1_g: E::G1Affine = (g * (gamma * delta_one_inverse)).into();
        let gamma_over_delta_2_g: E::G1Affine = (g * (gamma * delta_two_inverse)).into();
        let gamma_g: E::G1Affine = (g * gamma).into();
        end_timer!(timer_hiding);

        end_timer!(timer_pk_gen);

        /////////////////////// Output keys ///////////////////////
        let vk = VerifyingKey {
            succinct_index,
            alpha_g: alpha_g.into(),
            beta_g: beta_g.into(),
            gamma_h: gamma_h.into(),
            gamma_h_prep: gamma_h.into().into(),
            delta_one_h: delta_one_h.into(),
            delta_one_h_prep: delta_one_h.into().into(),
            delta_two_h_prep: delta_two_h.into().into(),
            delta_two_h: delta_two_h.into(),
            tau_h: tau_h.into(),
            tau_h_prep: tau_h.into().into(),
            g: g.into(),
            h_prep: h.into().into(),
            h: h.into(),
            domain,
        };

        let pk = ProvingKey {
            sigma_1,
            sigma_2,
            sigma_a,
            sigma_b,
            sigma_q_comm,
            sigma_q_opening,
            sigma_a_zk_1,
            sigma_b_zk_1,
            sigma_a_zk_2,
            sigma_b_zk_2,
            gamma_over_delta_1_g,
            gamma_over_delta_2_g,
            gamma_g,
            verifying_key: vk.clone(),
        };

        (pk, vk)
    }

    pub fn circuit_to_keygen_cs<C: ConstraintSynthesizer<E::ScalarField>>(
        circuit: C,
    ) -> Result<ConstraintSystem<E::ScalarField>, SynthesisError>
    where
        E: Pairing,
        E::ScalarField: Field,
        E::ScalarField: std::convert::From<i32>,
    {
        let timer_cs_startup = start_timer!(|| "Constraint System Startup");
        let cs: gr1cs::ConstraintSystemRef<E::ScalarField> = ConstraintSystem::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        circuit.generate_constraints(cs.clone())?;
        cs.finalize();

        let timer_inlining = start_timer!(|| "Inlining constraints");
        let native_sr1cs = cs.has_predicate(SR1CS_PREDICATE_LABEL);
        let mut sr1cs_inner = if native_sr1cs {
            cs.into_inner().unwrap()
        } else {
            let sr1cs_cs = Sr1csAdapter::r1cs_to_sr1cs(&cs).unwrap();
            sr1cs_cs.into_inner().unwrap()
        };

        let _ = sr1cs_inner.perform_instance_outlining(InstanceOutliner {
            pred_label: SR1CS_PREDICATE_LABEL.to_string(),
            func: Rc::new(outline_sr1cs),
        });
        end_timer!(timer_inlining);
        end_timer!(timer_cs_startup);
        Ok(sr1cs_inner)
    }

    #[allow(clippy::type_complexity)]
    fn compute_ai_bi_at_tau(
        tau: E::ScalarField,
        new_cs: &ConstraintSystem<E::ScalarField>,
        domain: Radix2EvaluationDomain<E::ScalarField>,
    ) -> Result<(Vec<E::ScalarField>, Vec<E::ScalarField>), SynthesisError> {
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
