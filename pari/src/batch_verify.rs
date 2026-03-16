use crate::utils::compute_chall;
use crate::{
    data_structures::{Proof, VerifyingKey},
    Pari,
};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::{Field, PrimeField, Zero};
use ark_std::{ops::Neg, rand::RngCore, UniformRand};
use shared_utils::msm_bigint_wnaf;

impl<E: Pairing> Pari<E> {
    /// Batch verification of N Pari proofs using random linear combination.
    ///
    /// Reduces N independent pairing checks to a single 3-pairing check by
    /// sampling random challenges ρ ←$ F^N and accumulating proof elements:
    ///   T̃ = Σ ρ_k · T^(k),  Ũ = Σ ρ_k · U^(k),  Ṽ = Σ (ρ_k · r^(k)) · U^(k)
    ///   ṽ_a = Σ ρ_k · v_a^(k),  ṽ_b = Σ ρ_k · v_b^(k),  ṽ_q = Σ ρ_k · v_q^(k)
    ///
    /// Then checks:
    ///   e(T̃, [δ₂]₂) · e(Ũ, [τ]₂) · e(ṽ_a·[α]₁ + ṽ_b·[β]₁ + ṽ_q·[1]₁ − Ṽ, [1]₂) = 1_T
    pub fn batch_verify(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
    ) -> bool
    where
        <E::G1Affine as AffineRepr>::BaseField: PrimeField,
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let n = proofs_and_inputs.len();
        if n == 0 {
            return true;
        }
        if n == 1 {
            return Self::verify(&proofs_and_inputs[0].0, vk, &proofs_and_inputs[0].1);
        }

        /////////////////////// Per-proof computations ///////////////////////
        // For each proof k: compute r^(k), x_A^(k), and v_q^(k)
        let mut challenges = Vec::with_capacity(n);
        let mut v_qs = Vec::with_capacity(n);

        let instance_size = vk.succinct_index.instance_len;
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        for (proof, public_input) in proofs_and_inputs.iter() {
            debug_assert_eq!(public_input.len(), instance_size - 1);

            let challenge = compute_chall::<E>(vk, public_input, &proof.t_g);

            let mut px_evaluations = Vec::with_capacity(instance_size);
            px_evaluations.push(E::ScalarField::ONE);
            px_evaluations.extend_from_slice(&public_input[..(instance_size - 1)]);

            let (lagrange_coeffs, vanishing_poly_at_chall_inv) =
                Self::eval_last_lagrange_coeffs::<E::ScalarField>(
                    &vk.domain,
                    challenge,
                    r1cs_orig_num_cnstrs,
                    instance_size,
                );

            let x_a = lagrange_coeffs
                .into_iter()
                .zip(px_evaluations)
                .fold(E::ScalarField::zero(), |acc, (l, x)| acc + l * x);
            let z_a = x_a + proof.v_a;
            let v_q = (z_a * z_a - proof.v_b) * vanishing_poly_at_chall_inv;

            challenges.push(challenge);
            v_qs.push(v_q);
        }

        /////////////////////// Random linear combination ///////////////////////
        // Sample ρ ←$ F^N and accumulate proof elements
        let rhos: Vec<E::ScalarField> = (0..n).map(|_| E::ScalarField::rand(rng)).collect();

        let t_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.t_g).collect();
        let u_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.u_g).collect();

        // T̃ = Σ_{k=1}^N ρ_k · T^(k)
        let t_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&t_bases, &rhos).into();

        // Ũ = Σ_{k=1}^N ρ_k · U^(k)
        let u_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&u_bases, &rhos).into();

        // Ṽ = Σ_{k=1}^N (ρ_k · r^(k)) · U^(k)
        let rho_r: Vec<E::ScalarField> = rhos
            .iter()
            .zip(&challenges)
            .map(|(rho, r)| *rho * *r)
            .collect();
        let v_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&u_bases, &rho_r).into();

        // ṽ_a = Σ_{k=1}^N ρ_k · v_a^(k)
        let v_a_tilde = rhos
            .iter()
            .zip(proofs_and_inputs.iter())
            .fold(E::ScalarField::zero(), |acc, (rho, (p, _))| {
                acc + *rho * p.v_a
            });

        // ṽ_b = Σ_{k=1}^N ρ_k · v_b^(k)
        let v_b_tilde = rhos
            .iter()
            .zip(proofs_and_inputs.iter())
            .fold(E::ScalarField::zero(), |acc, (rho, (p, _))| {
                acc + *rho * p.v_b
            });

        // ṽ_q = Σ_{k=1}^N ρ_k · v_q^(k)
        let v_q_tilde = rhos
            .iter()
            .zip(&v_qs)
            .fold(E::ScalarField::zero(), |acc, (rho, vq)| acc + *rho * *vq);
        /////////////////////// Final multi-pairing check ///////////////////////

        let scalar_msm: E::G1Affine = msm_bigint_wnaf::<E::G1>(
            &[vk.alpha_g, vk.beta_g, vk.g, -v_tilde],
            &[
                v_a_tilde.into(),
                v_b_tilde.into(),
                v_q_tilde.into(),
                E::ScalarField::ONE.into(),
            ],
        )
        .into();

        let result = E::multi_pairing(
            [t_tilde, u_tilde, scalar_msm],
            [
                vk.delta_two_h_prep.clone(),
                vk.tau_h_prep.clone(),
                vk.h_prep.clone(),
            ],
        );

        assert!(result.is_zero());
        true
    }
}
