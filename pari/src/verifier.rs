use crate::utils::compute_chall;
use crate::{
    data_structures::{Proof, VerifyingKey},
    Pari,
};
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use ark_ff::{FftField, Field, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{end_timer, ops::Neg, start_timer};
use shared_utils::{batch_inversion_and_mul, msm_bigint_wnaf};

impl<E: Pairing> Pari<E> {
    /// Verify a ZK-Pari proof.
    ///
    /// Checks the 5-pairing equation:
    ///   e(T_1, delta_1*H) * e(T_2, delta_2*H)
    ///     = e(U_1, (tau-r)*H) * e(U_2, gamma*H) * e(v_a*alpha*G + v_b*beta*G + v_q*G, H)
    pub fn verify(proof: &Proof<E>, vk: &VerifyingKey<E>, public_input: &[E::ScalarField]) -> bool
    where
        <E::G1Affine as AffineRepr>::BaseField: PrimeField,
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let timer_verify =
            start_timer!(|| format!("Verification (|x|= {})", vk.succinct_index.instance_len));
        debug_assert_eq!(public_input.len(), vk.succinct_index.instance_len - 1);
        let Proof {
            t_1,
            t_2,
            u_1,
            u_2,
            v_a,
            v_b,
        } = proof;

        /////////////////////// Challenge Computation ///////////////////////
        let timer_transcript_init = start_timer!(|| "Computing Challenge");
        let challenge = compute_chall::<E>(vk, public_input, t_1, t_2);
        end_timer!(timer_transcript_init);

        /////////////////////// Computing x_A(r) ///////////////////////
        let timer_x_poly = start_timer!(|| "Compute x_a polynomial");
        let instance_size = vk.succinct_index.instance_len;
        let mut px_evaluations = Vec::with_capacity(instance_size);
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        px_evaluations.push(E::ScalarField::ONE);
        px_evaluations.extend_from_slice(&public_input[..(instance_size - 1)]);
        let lag_coeffs_time = start_timer!(|| "Computing last lagrange coefficients");
        let (lagrange_coeffs, vanishing_poly_at_chall_inv) =
            Self::eval_last_lagrange_coeffs::<E::ScalarField>(
                &vk.domain,
                challenge,
                r1cs_orig_num_cnstrs,
                vk.succinct_index.instance_len,
            );
        end_timer!(lag_coeffs_time);

        let x_a = lagrange_coeffs
            .into_iter()
            .zip(px_evaluations)
            .fold(E::ScalarField::zero(), |acc, (x, d)| acc + x * d);
        let z_a = x_a + v_a;
        end_timer!(timer_x_poly);

        /////////////////////// Computing the quotient evaluation ///////////////////////
        let timer_q = start_timer!(|| "Computing the quotient evaluation");
        let v_q = (z_a * z_a - v_b) * vanishing_poly_at_chall_inv;
        end_timer!(timer_q);

        /////////////////////// 5-pairing check ///////////////////////
        // e(T_1, d1H) + e(T_2, d2H) - e(U_1, tH) - e(U_2, gH) + e(r*U_1 - S, H) = 0
        // where S = v_a*aG + v_b*bG + v_q*G

        let timer_scalar_mul = start_timer!(|| "Scalar mul");
        let remainder: E::G1Affine = msm_bigint_wnaf::<E::G1>(
            &[-vk.alpha_g, -vk.beta_g, -vk.g, *u_1],
            &[
                (*v_a).into(),
                (*v_b).into(),
                v_q.into(),
                challenge.into(),
            ],
        )
        .into();
        end_timer!(timer_scalar_mul);

        let timer_pairing = start_timer!(|| "Final Pairing");
        let result = E::multi_pairing(
            [*t_1, *t_2, -*u_1, -*u_2, remainder],
            [
                vk.delta_one_h_prep.clone(),
                vk.delta_two_h_prep.clone(),
                vk.tau_h_prep.clone(),
                vk.gamma_h_prep.clone(),
                vk.h_prep.clone(),
            ],
        );
        assert!(result.is_zero());
        end_timer!(timer_pairing);
        end_timer!(timer_verify);
        true
    }

    #[cfg(feature = "sol")]
    fn eval_last_lagrange_coeffs_traced<F: FftField>(
        domain: &Radix2EvaluationDomain<F>,
        tau: F,
        start_ind: usize,
        count: usize,
    ) -> (Vec<F>, Vec<F>, Vec<F>)
    where
        E::BaseField: PrimeField + FftField,
        E::BaseField: FftField,
    {
        let size: usize = domain.size();
        let z_h_at_tau: F = domain.evaluate_vanishing_polynomial(tau);
        let mut neg_hi = Vec::new();
        let mut nom_i = Vec::new();
        let offset: F = domain.coset_offset();
        let group_gen: F = domain.group_gen();
        let _starting_g: F = offset * group_gen.pow([start_ind as u64]);
        let group_gen_inv = domain.group_gen_inv();
        let v_0_inv = domain.size_as_field_element() * offset.pow([size as u64 - 1]);
        let start_gen = group_gen.pow([start_ind as u64]);
        let mut l_i = z_h_at_tau.inverse().unwrap() * v_0_inv;
        let mut negative_cur_elem = (-offset) * (start_gen);
        let mut lagrange_coefficients_inverse = vec![F::zero(); count];
        for (_, coeff) in &mut lagrange_coefficients_inverse.iter_mut().enumerate() {
            neg_hi.push(negative_cur_elem);
            let nom = start_gen * (l_i.inverse().unwrap());
            nom_i.push(nom);
            let r_i = tau + negative_cur_elem;
            *coeff = l_i * r_i;
            l_i *= &group_gen_inv;
            negative_cur_elem *= &group_gen;
        }
        batch_inversion_and_mul(lagrange_coefficients_inverse.as_mut_slice(), &start_gen);
        (lagrange_coefficients_inverse, neg_hi, nom_i)
    }

    pub(crate) fn eval_last_lagrange_coeffs<F: FftField>(
        domain: &Radix2EvaluationDomain<F>,
        tau: F,
        start_ind: usize,
        count: usize,
    ) -> (Vec<F>, F) {
        let z_h_at_tau: F = domain.evaluate_vanishing_polynomial(tau);
        let group_gen: F = domain.group_gen();

        assert!(!z_h_at_tau.is_zero());

        let group_gen_inv = domain.group_gen_inv();
        let v_0_inv = domain.size_as_field_element();

        let start_gen = group_gen.pow([start_ind as u64]);
        let z_h_at_tau_inv = z_h_at_tau.inverse().unwrap();
        let mut l_i = z_h_at_tau_inv * v_0_inv;
        let mut negative_cur_elem = -start_gen;
        let mut lagrange_coefficients_inverse = vec![F::zero(); count];
        for coeff in &mut lagrange_coefficients_inverse.iter_mut() {
            *coeff = l_i * (tau + negative_cur_elem);
            l_i *= &group_gen_inv;
            negative_cur_elem *= &group_gen;
        }
        batch_inversion_and_mul(lagrange_coefficients_inverse.as_mut_slice(), &start_gen);
        (lagrange_coefficients_inverse, z_h_at_tau_inv)
    }
}
