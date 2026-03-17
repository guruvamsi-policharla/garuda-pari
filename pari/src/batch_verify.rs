use crate::{
    data_structures::{Proof, VerifyingKey},
    Pari,
};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::{FftField, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{ops::Neg, rand::RngCore, UniformRand};
use shared_utils::{batch_inversion_and_mul, msm_bigint_wnaf};
use std::time::{Duration, Instant};

pub struct BatchVerifyBreakdown {
    pub per_proof: Duration,
    pub msm_and_accum: Duration,
    pub pairing: Duration,
}

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

        /////////////////////// Challenge computation ///////////////////////
        // Pre-seed transcript with VK once, then clone per proof
        #[cfg(not(feature = "sol"))]
        let challenges: Vec<E::ScalarField> = {
            let base_transcript = crate::utils::seed_transcript_with_vk::<E>(vk);
            proofs_and_inputs
                .iter()
                .map(|(proof, public_input)| {
                    crate::utils::compute_chall_from_transcript::<E>(
                        &base_transcript,
                        public_input,
                        &proof.t_g,
                    )
                })
                .collect()
        };

        #[cfg(feature = "sol")]
        let challenges: Vec<E::ScalarField> = proofs_and_inputs
            .iter()
            .map(|(proof, public_input)| {
                crate::utils::compute_chall::<E>(vk, public_input, &proof.t_g)
            })
            .collect();

        /////////////////////// Per-proof computations ///////////////////////
        // Batch-evaluate Lagrange coefficients: precompute shared constants once,
        // batch-invert vanishing polynomial evaluations across all proofs
        let instance_size = vk.succinct_index.instance_len;
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        let (all_lagrange_coeffs, z_h_inv) =
            Self::batch_eval_last_lagrange_coeffs::<E::ScalarField>(
                &vk.domain,
                &challenges,
                r1cs_orig_num_cnstrs,
                instance_size,
            );

        // For each proof k: compute x_A^(k) and v_q^(k)
        let mut v_qs = Vec::with_capacity(n);

        for (((proof, public_input), lagrange_coeffs), vanishing_inv) in proofs_and_inputs
            .iter()
            .zip(all_lagrange_coeffs)
            .zip(&z_h_inv)
        {
            debug_assert_eq!(public_input.len(), instance_size - 1);

            let x_a = lagrange_coeffs
                .into_iter()
                .zip(
                    core::iter::once(E::ScalarField::ONE)
                        .chain(public_input[..(instance_size - 1)].iter().copied()),
                )
                .fold(E::ScalarField::zero(), |acc, (l, x)| acc + l * x);
            let z_a = x_a + proof.v_a;
            let v_q = (z_a * z_a - proof.v_b) * *vanishing_inv;

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

    /// Same as `batch_verify` but returns a per-phase timing breakdown.
    pub fn batch_verify_timed(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
    ) -> (bool, BatchVerifyBreakdown)
    where
        <E::G1Affine as AffineRepr>::BaseField: PrimeField,
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let n = proofs_and_inputs.len();
        assert!(n >= 2);

        /////////////////////// Phase 1: Per-proof computation ///////////////////////
        let t0 = Instant::now();

        #[cfg(not(feature = "sol"))]
        let challenges: Vec<E::ScalarField> = {
            let base_transcript = crate::utils::seed_transcript_with_vk::<E>(vk);
            proofs_and_inputs
                .iter()
                .map(|(proof, public_input)| {
                    crate::utils::compute_chall_from_transcript::<E>(
                        &base_transcript,
                        public_input,
                        &proof.t_g,
                    )
                })
                .collect()
        };

        #[cfg(feature = "sol")]
        let challenges: Vec<E::ScalarField> = proofs_and_inputs
            .iter()
            .map(|(proof, public_input)| {
                crate::utils::compute_chall::<E>(vk, public_input, &proof.t_g)
            })
            .collect();

        let instance_size = vk.succinct_index.instance_len;
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        let (all_lagrange_coeffs, z_h_inv) =
            Self::batch_eval_last_lagrange_coeffs::<E::ScalarField>(
                &vk.domain,
                &challenges,
                r1cs_orig_num_cnstrs,
                instance_size,
            );

        let mut v_qs = Vec::with_capacity(n);
        for (((proof, public_input), lagrange_coeffs), vanishing_inv) in proofs_and_inputs
            .iter()
            .zip(all_lagrange_coeffs)
            .zip(&z_h_inv)
        {
            let x_a = lagrange_coeffs
                .into_iter()
                .zip(
                    core::iter::once(E::ScalarField::ONE)
                        .chain(public_input[..(instance_size - 1)].iter().copied()),
                )
                .fold(E::ScalarField::zero(), |acc, (l, x)| acc + l * x);
            let z_a = x_a + proof.v_a;
            let v_q = (z_a * z_a - proof.v_b) * *vanishing_inv;
            v_qs.push(v_q);
        }

        let per_proof = t0.elapsed();

        /////////////////////// Phase 2: MSMs + scalar accumulation ///////////////////////
        let t1 = Instant::now();

        let rhos: Vec<E::ScalarField> = (0..n).map(|_| E::ScalarField::rand(rng)).collect();

        let t_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.t_g).collect();
        let u_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.u_g).collect();

        let t_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&t_bases, &rhos).into();
        let u_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&u_bases, &rhos).into();

        let rho_r: Vec<E::ScalarField> = rhos
            .iter()
            .zip(&challenges)
            .map(|(rho, r)| *rho * *r)
            .collect();
        let v_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&u_bases, &rho_r).into();

        let v_a_tilde = rhos
            .iter()
            .zip(proofs_and_inputs.iter())
            .fold(E::ScalarField::zero(), |acc, (rho, (p, _))| {
                acc + *rho * p.v_a
            });
        let v_b_tilde = rhos
            .iter()
            .zip(proofs_and_inputs.iter())
            .fold(E::ScalarField::zero(), |acc, (rho, (p, _))| {
                acc + *rho * p.v_b
            });
        let v_q_tilde = rhos
            .iter()
            .zip(&v_qs)
            .fold(E::ScalarField::zero(), |acc, (rho, vq)| acc + *rho * *vq);

        let msm_and_accum = t1.elapsed();

        /////////////////////// Phase 3: Final pairing ///////////////////////
        let t2 = Instant::now();

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

        let pairing = t2.elapsed();

        assert!(result.is_zero());
        (
            true,
            BatchVerifyBreakdown {
                per_proof,
                msm_and_accum,
                pairing,
            },
        )
    }

    /// Batch variant of `eval_last_lagrange_coeffs`. Precomputes domain
    /// constants and the geometric sequence once, then batch-inverts the
    /// vanishing polynomial evaluations across all challenges.
    ///
    /// Returns `(lagrange_coeffs_per_proof, z_K_inv_per_proof)`.
    fn batch_eval_last_lagrange_coeffs<F: FftField>(
        domain: &Radix2EvaluationDomain<F>,
        challenges: &[F],
        start_ind: usize,
        count: usize,
    ) -> (Vec<Vec<F>>, Vec<F>) {
        let n = challenges.len();

        // Domain constants — computed once
        let group_gen = domain.group_gen();
        let group_gen_inv = domain.group_gen_inv();
        let v_0_inv = domain.size_as_field_element();
        let start_gen = group_gen.pow([start_ind as u64]);

        // Geometric sequence: neg_elems[i] = -ω^(start_ind + i), computed once
        let mut neg_elems = Vec::with_capacity(count);
        let mut neg_cur = -start_gen;
        for _ in 0..count {
            neg_elems.push(neg_cur);
            neg_cur *= &group_gen;
        }

        // Evaluate z_K(τ^(k)) for all k, then batch-invert (1 inversion + 3N muls
        // instead of N independent inversions)
        let mut z_h_inv: Vec<F> = challenges
            .iter()
            .map(|tau| domain.evaluate_vanishing_polynomial(*tau))
            .collect();
        for z in z_h_inv.iter() {
            assert!(!z.is_zero());
        }
        batch_inversion_and_mul(&mut z_h_inv, &F::one());

        // Per-proof: fill Lagrange coefficient vectors using precomputed neg_elems
        let mut all_lagrange_coeffs = Vec::with_capacity(n);
        for (tau, z_inv) in challenges.iter().zip(&z_h_inv) {
            let mut l_i = *z_inv * v_0_inv;
            let mut coeffs = vec![F::zero(); count];
            for (coeff, neg_elem) in coeffs.iter_mut().zip(&neg_elems) {
                *coeff = l_i * (*tau + *neg_elem);
                l_i *= &group_gen_inv;
            }
            batch_inversion_and_mul(&mut coeffs, &start_gen);
            all_lagrange_coeffs.push(coeffs);
        }

        (all_lagrange_coeffs, z_h_inv)
    }
}
