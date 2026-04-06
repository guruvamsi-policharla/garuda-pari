use std::{ops::Neg, rc::Rc};

use crate::utils::compute_chall;
use crate::{
    data_structures::{Proof, ProvingKey},
    Pari,
};
use ark_ec::AffineRepr;
use ark_ec::{pairing::Pairing, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_ff::{Field, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain, Polynomial,
};
use ark_relations::{
    gr1cs::{
        self,
        instance_outliner::{outline_sr1cs, InstanceOutliner},
        predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL,
        ConstraintSynthesizer, ConstraintSystem, Matrix, OptimizationGoal, SynthesisError,
    },
    sr1cs::Sr1csAdapter,
};
use ark_std::{cfg_iter_mut, end_timer, rand::RngCore, start_timer, UniformRand};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<E: Pairing> Pari<E> {
    pub fn prove<C: ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
        circuit: C,
        pk: &ProvingKey<E>,
        rng: &mut R,
    ) -> Result<Proof<E>, SynthesisError>
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
        E: Pairing,
        E::ScalarField: Field,
        E::ScalarField: std::convert::From<i32>,
        E::BaseField: PrimeField,
        <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
    {
        let timer_p = start_timer!(|| "Total Proving time");
        let cs = Self::circuit_to_prover_cs(circuit)?;
        #[cfg(debug_assertions)]
        {
            assert_eq!(cs.num_predicates(), 1);
            assert_eq!(
                cs.num_constraints(),
                cs.get_predicate_num_constraints(SR1CS_PREDICATE_LABEL)
                    .unwrap()
            );
            assert!(cs.is_satisfied().unwrap());
        }

        /////////////////////// Extract the constraint system information ///////////////////////
        let timer_extract_info = start_timer!(|| "Extract constraint system information");
        let num_constraints = cs.num_constraints();
        let instance_assignment = &cs.assignments.instance_assignment;
        let witness_assignment = &cs.assignments.witness_assignment;
        let matrices = &cs.to_matrices().unwrap()[SR1CS_PREDICATE_LABEL];
        let witness_split = pk.verifying_key.succinct_index.witness_split;
        end_timer!(timer_extract_info);

        /////////////////////////// Computing the evaluation domain ///////////////////////
        let timer_eval_domain = start_timer!(|| "Computing the evaluation domain");
        let domain = GeneralEvaluationDomain::<E::ScalarField>::new(num_constraints).unwrap();
        let domain_size = domain.size();
        end_timer!(timer_eval_domain);

        /////////////////////// Sample blinding randomness ///////////////////////
        let timer_sample_blinding = start_timer!(|| "Sampling blinding randomness");
        let eta_a_1 = E::ScalarField::rand(rng);
        let eta_a_2 = E::ScalarField::rand(rng);
        let eta_b_1 = E::ScalarField::rand(rng);
        let eta_b_2 = E::ScalarField::rand(rng);
        let zeta_1 = E::ScalarField::rand(rng);
        let zeta_2 = E::ScalarField::rand(rng);
        let s = E::ScalarField::rand(rng);
        let eta_a = eta_a_1 + eta_a_2;
        let eta_b = eta_b_1 + eta_b_2;
        end_timer!(timer_sample_blinding);

        /////////////////////// Computing polynomials z_A, z_B, w_A, w_B ///////////////////////
        let timer_compute_za_zb_wa_wb = start_timer!(|| "Computing vectors z_A, z_B, w_A, w_B");
        let ((z_a, z_b), (w_a, w_b)) = Self::compute_wa_wb_za_zb(
            domain,
            &matrices[0],
            &matrices[1],
            instance_assignment,
            witness_assignment,
            num_constraints,
        )
        .unwrap();
        end_timer!(timer_compute_za_zb_wa_wb);

        //////////////////////// Interpolating polynomials ///////////////////////
        let timer_interp = start_timer!(|| "Interpolating z_a, z_b, w_a, w_b polynomials");
        let z_a_hat = Evaluations::from_vec_and_domain(z_a, domain).interpolate();
        let z_b_hat = Evaluations::from_vec_and_domain(z_b, domain).interpolate();
        let w_a_hat = Evaluations::from_vec_and_domain(w_a, domain).interpolate();
        let w_b_hat = Evaluations::from_vec_and_domain(w_b, domain).interpolate();
        end_timer!(timer_interp);

        /////////////////////// Construct vanishing polynomial for blinding ///////////////////////
        let timer_v_k = start_timer!(|| "Constructing vanishing polynomial");
        let mut v_k_coeffs = vec![E::ScalarField::zero(); domain_size + 1];
        v_k_coeffs[0] = -E::ScalarField::ONE;
        v_k_coeffs[domain_size] = E::ScalarField::ONE;
        let v_k_poly = DensePolynomial::from_coefficients_vec(v_k_coeffs);
        end_timer!(timer_v_k);

        /////////////////////// Computing the blinded quotient polynomial ///////////////////////
        let timer_quotient = start_timer!(|| "Computing the blinded quotient polynomial");
        let eta_a_v_k = DensePolynomial::from_coefficients_vec(
            v_k_poly.coeffs.iter().map(|c| *c * eta_a).collect(),
        );
        let eta_b_v_k = DensePolynomial::from_coefficients_vec(
            v_k_poly.coeffs.iter().map(|c| *c * eta_b).collect(),
        );
        let z_a_blinded = &z_a_hat + &eta_a_v_k;
        let z_b_blinded = &z_b_hat + &eta_b_v_k;
        let (q_tilde, _remainder) =
            (&z_a_blinded * &z_a_blinded - &z_b_blinded).divide_by_vanishing_poly(domain);
        #[cfg(debug_assertions)]
        assert!(_remainder.is_zero());
        end_timer!(timer_quotient);

        /////////////////////// Computing the split witness commitments (T_1, T_2) ///////////////////////
        let timer_batch_commit = start_timer!(|| "Batch commitment");

        let w_part1 = &witness_assignment[..witness_split];
        let w_part2 = &witness_assignment[witness_split..];

        let timer_t1 = start_timer!(|| "Computing T_1");
        let t_1_witness = <E::G1 as VariableBaseMSM>::msm_unchecked(&pk.sigma_1, w_part1);
        let t_1_zk = E::G1::msm_unchecked(
            &[
                pk.sigma_a_zk_1,
                pk.sigma_b_zk_1,
                pk.gamma_over_delta_1_g,
            ],
            &[eta_a_1, eta_b_1, zeta_1],
        );
        let t_1: E::G1Affine = (t_1_witness + t_1_zk).into();
        end_timer!(timer_t1);

        let timer_t2 = start_timer!(|| "Computing T_2");
        let t_2_witness = <E::G1 as VariableBaseMSM>::msm_unchecked(&pk.sigma_2, w_part2);
        let t_2_zk = E::G1::msm_unchecked(
            &[
                pk.sigma_a_zk_2,
                pk.sigma_b_zk_2,
                pk.gamma_over_delta_2_g,
            ],
            &[eta_a_2, eta_b_2, zeta_2],
        );
        let t_q = <E::G1 as VariableBaseMSM>::msm_unchecked(&pk.sigma_q_comm, &q_tilde.coeffs);
        let t_2: E::G1Affine = (t_2_witness + t_2_zk + t_q).into();
        end_timer!(timer_t2);
        end_timer!(timer_batch_commit);

        /////////////////////// Computing the Fiat-Shamir challenge ///////////////////////
        let timer_init_transcript = start_timer!(|| "Computing Challenge");
        let challenge = compute_chall::<E>(
            &pk.verifying_key,
            &instance_assignment[1..].to_vec(),
            &t_1,
            &t_2,
        );
        end_timer!(timer_init_transcript);

        /////////////////////// Blinded evaluations ///////////////////////
        let timer_eval = start_timer!(|| "Evaluating blinded v_a, v_b");
        let w_a_tilde = &w_a_hat + &eta_a_v_k;
        let w_b_tilde = &w_b_hat + &eta_b_v_k;

        let v_a = w_a_tilde.evaluate(&challenge);
        let v_b = w_b_tilde.evaluate(&challenge);

        #[cfg(debug_assertions)]
        {
            let v_q_check = q_tilde.evaluate(&challenge);
            let z_a_at_r = z_a_blinded.evaluate(&challenge);
            let z_b_at_r = z_b_blinded.evaluate(&challenge);
            let v_k_at_r = domain.evaluate_vanishing_polynomial(challenge);
            assert_eq!(
                (z_a_at_r * z_a_at_r - z_b_at_r) / v_k_at_r,
                v_q_check,
                "Blinded quotient relation failed"
            );
        }
        end_timer!(timer_eval);

        /////////////////////// Opening proofs ///////////////////////
        let timer_opening = start_timer!(|| "Batch Opening");

        let timer_open_poly = start_timer!(|| "Computing the opening polynomials");
        let one = E::ScalarField::ONE;
        let v_q_tilde_at_r = q_tilde.evaluate(&challenge);
        let w_a_r = DensePolynomial::from_coefficients_vec(vec![v_a]);
        let w_b_r = DensePolynomial::from_coefficients_vec(vec![v_b]);
        let q_r = DensePolynomial::from_coefficients_vec(vec![v_q_tilde_at_r]);
        let chall_vanishing_poly = DensePolynomial::from_coefficients_vec(vec![-challenge, one]);
        let witness_a = (&w_a_tilde - &w_a_r) / &chall_vanishing_poly;
        let witness_b = (&w_b_tilde - &w_b_r) / &chall_vanishing_poly;
        let witness_q = (&q_tilde - &q_r) / &chall_vanishing_poly;
        end_timer!(timer_open_poly);

        let timer_msms = start_timer!(|| "Computing the opening MSMs");
        let w_a_proof = E::G1::msm_unchecked(&pk.sigma_a, &witness_a.coeffs);
        let w_b_proof = E::G1::msm_unchecked(&pk.sigma_b, &witness_b.coeffs);
        let q_proof = E::G1::msm_unchecked(&pk.sigma_q_opening, &witness_q.coeffs);
        let u = w_a_proof + w_b_proof + q_proof;
        end_timer!(timer_msms);

        /////////////////////// Hiding-KZG: U_1 and U_2 ///////////////////////
        let timer_hiding_kzg = start_timer!(|| "Computing U_1 and U_2");
        let u_1_proj: E::G1 = u + E::G1::from(pk.gamma_g) * s;
        let u_1: E::G1Affine = u_1_proj.into();

        let u_2_coeff_0 = zeta_1 + zeta_2 + s * challenge;
        let u_2_coeff_1 = -s;
        let u_2: E::G1Affine = E::G1::msm_unchecked(
            &[pk.sigma_q_opening[0], pk.sigma_q_opening[1]],
            &[u_2_coeff_0, u_2_coeff_1],
        )
        .into();
        end_timer!(timer_hiding_kzg);
        end_timer!(timer_opening);

        let output = Ok(Proof {
            t_1,
            t_2,
            u_1,
            u_2,
            v_a,
            v_b,
        });

        end_timer!(timer_p);
        output
    }

    pub fn circuit_to_prover_cs<C: ConstraintSynthesizer<E::ScalarField>>(
        circuit: C,
    ) -> Result<ConstraintSystem<E::ScalarField>, SynthesisError>
    where
        E: Pairing,
        E::ScalarField: Field,
        E::ScalarField: std::convert::From<i32>,
    {
        let timer_cs_startup = start_timer!(|| "Prover constraint System Startup");
        let timer_synthesize_circuit = start_timer!(|| "Synthesize Circuit");
        let cs: gr1cs::ConstraintSystemRef<E::ScalarField> = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        circuit.generate_constraints(cs.clone())?;
        end_timer!(timer_synthesize_circuit);
        let timer_inlining = start_timer!(|| "Inlining constraints");
        cs.finalize();
        end_timer!(timer_inlining);
        let sr1cs_timer = start_timer!(|| "Convert to SR1CS");
        let sr1cs_cs =
            Sr1csAdapter::r1cs_to_sr1cs_with_assignment(&mut cs.into_inner().unwrap()).unwrap();

        let mut sr1cs_inner = sr1cs_cs.into_inner().unwrap();
        let _ = sr1cs_inner.perform_instance_outlining(InstanceOutliner {
            pred_label: SR1CS_PREDICATE_LABEL.to_string(),
            func: Rc::new(outline_sr1cs),
        });
        end_timer!(sr1cs_timer);
        end_timer!(timer_cs_startup);
        Ok(sr1cs_inner)
    }

    #[allow(clippy::type_complexity)]
    fn compute_wa_wb_za_zb(
        domain: GeneralEvaluationDomain<E::ScalarField>,
        a_mat: &Matrix<E::ScalarField>,
        b_mat: &Matrix<E::ScalarField>,
        instance_assignment: &[E::ScalarField],
        witness_assignment: &[E::ScalarField],
        num_constraints: usize,
    ) -> Result<
        (
            (Vec<E::ScalarField>, Vec<E::ScalarField>),
            (Vec<E::ScalarField>, Vec<E::ScalarField>),
        ),
        SynthesisError,
    > {
        let mut assignment: Vec<E::ScalarField> = instance_assignment.to_vec();
        let mut punctured_assignment: Vec<E::ScalarField> =
            vec![E::ScalarField::zero(); assignment.len()];
        assignment.extend_from_slice(witness_assignment);
        punctured_assignment.extend_from_slice(witness_assignment);

        let domain_size = domain.size();
        let mut z_a = vec![E::ScalarField::zero(); domain_size];
        let mut z_b = vec![E::ScalarField::zero(); domain_size];

        cfg_iter_mut!(z_a[..num_constraints])
            .zip(&mut z_b[..num_constraints])
            .zip(a_mat)
            .zip(b_mat)
            .for_each(|(((a, b), at_i), bt_i)| {
                *a = Sr1csAdapter::<E::ScalarField>::evaluate_constraint(at_i, &assignment);
                *b = Sr1csAdapter::<E::ScalarField>::evaluate_constraint(bt_i, &assignment);
            });

        let mut w_a = vec![E::ScalarField::zero(); domain_size];
        let mut w_b = vec![E::ScalarField::zero(); domain_size];

        cfg_iter_mut!(w_a[..num_constraints])
            .zip(&mut w_b[..num_constraints])
            .zip(a_mat)
            .zip(b_mat)
            .for_each(|(((a, b), at_i), bt_i)| {
                *a = Sr1csAdapter::<E::ScalarField>::evaluate_constraint(
                    at_i,
                    &punctured_assignment,
                );
                *b = Sr1csAdapter::<E::ScalarField>::evaluate_constraint(
                    bt_i,
                    &punctured_assignment,
                );
            });

        Ok(((z_a, z_b), (w_a, w_b)))
    }
}
