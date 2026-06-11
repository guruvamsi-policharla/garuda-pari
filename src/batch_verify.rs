use crate::data_structures::{Proof, VerifyingKey};
use crate::utils::{batch_inversion_and_mul, msm_bigint_wnaf, msm_pippenger};
use crate::ZkPari;
use ark_ec::pairing::Pairing;
use ark_ec::VariableBaseMSM;
use ark_ff::{FftField, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{
    ops::Neg,
    rand::{rngs::StdRng, RngCore, SeedableRng},
};
use rayon::prelude::*;
use std::time::Instant;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BatchVerifyTimings {
    /// Number of independent batch-verification chunks. Timed sub-phases are
    /// summed across chunks when this is greater than one.
    pub partitions: usize,
    pub challenge_us: u128,
    pub lagrange_us: u128,
    pub instance_us: u128,
    pub sample_rhos_us: u128,
    pub small_msm_us: u128,
    pub c_msm_us: u128,
    pub t_msm_us: u128,
    pub u_msm_us: u128,
    pub full_msm_us: u128,
    pub scalar_accum_us: u128,
    pub last_left_us: u128,
    pub pairing_us: u128,
}

impl BatchVerifyTimings {
    fn add_assign(&mut self, other: Self) {
        self.challenge_us += other.challenge_us;
        self.lagrange_us += other.lagrange_us;
        self.instance_us += other.instance_us;
        self.sample_rhos_us += other.sample_rhos_us;
        self.small_msm_us += other.small_msm_us;
        self.c_msm_us += other.c_msm_us;
        self.t_msm_us += other.t_msm_us;
        self.u_msm_us += other.u_msm_us;
        self.full_msm_us += other.full_msm_us;
        self.scalar_accum_us += other.scalar_accum_us;
        self.last_left_us += other.last_left_us;
        self.pairing_us += other.pairing_us;
    }
}

impl<E: Pairing> ZkPari<E> {
    /// Batch verification of N proofs using a random linear combination.
    ///
    /// Reduces N independent (3 + #blocks)-pairing checks to a single
    /// (3 + #blocks)-pairing check by sampling random 128-bit challenges
    /// `rho_k` and accumulating:
    ///
    /// ```text
    /// C~_j = sum rho_k C_ci_j^(k),  T~ = sum rho_k T^(k),  U~ = sum rho_k U^(k),
    /// V~ = sum (rho_k r^(k)) U^(k),
    /// va~ = sum rho_k v_a^(k),  vR~ = sum rho_k v_R^(k)
    /// ```
    ///
    /// then checking
    ///
    /// ```text
    /// prod_j e(C~_j, delta_j H) * e(T~, delta_w H) * e(-U~, tau H)
    ///     * e(V~ - va~ alpha G - vR~ beta G, H) == 1
    /// ```
    pub fn batch_verify(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
    ) -> bool
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        Self::batch_verify_inner(proofs_and_inputs, vk, rng, None)
    }

    /// [`Self::batch_verify`] plus coarse wall-clock timings for profiling.
    pub fn batch_verify_timed(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
    ) -> (bool, BatchVerifyTimings)
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let mut timings = BatchVerifyTimings::default();
        let accepted = Self::batch_verify_inner(proofs_and_inputs, vk, rng, Some(&mut timings));
        (accepted, timings)
    }

    /// Split the claims into up to `num_partitions` contiguous chunks and
    /// batch-verify those chunks independently in parallel.
    ///
    /// This trades one global batch check for several smaller checks: it pays
    /// one final pairing per non-empty chunk, but lets the per-chunk MSMs run
    /// concurrently.
    pub fn batch_verify_partitioned(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
        num_partitions: usize,
    ) -> bool
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
        Proof<E>: Sync,
        VerifyingKey<E>: Sync,
    {
        Self::batch_verify_partitioned_timed(proofs_and_inputs, vk, rng, num_partitions).0
    }

    /// [`Self::batch_verify_partitioned`] plus per-chunk timing totals.
    pub fn batch_verify_partitioned_timed(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
        num_partitions: usize,
    ) -> (bool, BatchVerifyTimings)
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
        Proof<E>: Sync,
        VerifyingKey<E>: Sync,
    {
        let n = proofs_and_inputs.len();
        if n == 0 {
            return (true, BatchVerifyTimings::default());
        }
        let partitions = num_partitions.clamp(1, n);
        if partitions == 1 {
            return Self::batch_verify_timed(proofs_and_inputs, vk, rng);
        }

        let chunk_size = n.div_ceil(partitions);
        let chunks: Vec<_> = proofs_and_inputs.chunks(chunk_size).collect();
        let mut seeds = vec![[0u8; 32]; chunks.len()];
        for seed in &mut seeds {
            rng.fill_bytes(seed);
        }

        let results: Vec<_> = chunks
            .into_par_iter()
            .zip(seeds.into_par_iter())
            .map(|(chunk, seed)| {
                let mut chunk_rng = StdRng::from_seed(seed);
                Self::batch_verify_timed(chunk, vk, &mut chunk_rng)
            })
            .collect();

        let accepted = results.iter().all(|(accepted, _)| *accepted);
        let mut timings = BatchVerifyTimings {
            partitions: results.len(),
            ..BatchVerifyTimings::default()
        };
        for (_, chunk_timings) in results {
            timings.add_assign(chunk_timings);
        }
        (accepted, timings)
    }

    fn batch_verify_inner(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
        mut timings: Option<&mut BatchVerifyTimings>,
    ) -> bool
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let n = proofs_and_inputs.len();
        if n == 0 {
            return true;
        }
        if let Some(timings) = timings.as_deref_mut() {
            timings.partitions = 1;
        }
        // Malformed statements and proofs are rejected, not panicked on
        let num_blocks = vk.delta_h_prep.len();
        let instance_len = vk.succinct_index.instance_len;
        if proofs_and_inputs
            .iter()
            .any(|(p, x)| p.c_ci.len() != num_blocks || x.len() != instance_len - 1)
        {
            return false;
        }
        if n == 1 {
            return Self::verify(&proofs_and_inputs[0].0, vk, &proofs_and_inputs[0].1);
        }

        /////////////////////// Challenge computation ///////////////////////
        let started = timings.as_ref().map(|_| Instant::now());
        let challenges: Vec<E::ScalarField> = {
            let base_transcript = crate::utils::seed_transcript_with_vk::<E>(vk);
            proofs_and_inputs
                .iter()
                .map(|(proof, public_input)| {
                    crate::utils::compute_chall_from_transcript::<E>(
                        &base_transcript,
                        public_input,
                        &proof.c_ci,
                        &proof.t_g,
                    )
                })
                .collect()
        };
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.challenge_us = started.elapsed().as_micros();
        }

        /////////////////////// Per-proof computations ///////////////////////
        let instance_size = vk.succinct_index.instance_len;
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        let started = timings.as_ref().map(|_| Instant::now());
        let all_lagrange_coeffs = Self::batch_eval_last_lagrange_coeffs::<E::ScalarField>(
            &vk.domain,
            &challenges,
            r1cs_orig_num_cnstrs,
            instance_size,
        );
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.lagrange_us = started.elapsed().as_micros();
        }

        // For each proof k: compute x_A^(k)(r) and v_R^(k) = (x_A + v_a)^2
        let started = timings.as_ref().map(|_| Instant::now());
        let mut v_rs = Vec::with_capacity(n);
        for ((proof, public_input), lagrange_coeffs) in
            proofs_and_inputs.iter().zip(all_lagrange_coeffs)
        {
            let x_a = lagrange_coeffs
                .into_iter()
                .zip(core::iter::once(E::ScalarField::ONE).chain(public_input.iter().copied()))
                .fold(E::ScalarField::zero(), |acc, (l, x)| acc + l * x);
            v_rs.push((x_a + proof.v_a).square());
        }
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.instance_us = started.elapsed().as_micros();
        }

        /////////////////////// Random linear combination ///////////////////////
        // Sample 128-bit rho <-$ [0, 2^128)^N (sufficient for 2^-128 soundness)
        const SMALL_SCALAR_BITS: usize = 128;
        let started = timings.as_ref().map(|_| Instant::now());
        let rhos: Vec<E::ScalarField> = (0..n)
            .map(|_| {
                let mut bytes = [0u8; 16];
                rng.fill_bytes(&mut bytes);
                E::ScalarField::from_le_bytes_mod_order(&bytes)
            })
            .collect();
        let rho_bigints: Vec<<E::ScalarField as PrimeField>::BigInt> =
            rhos.iter().map(|r| r.into_bigint()).collect();
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.sample_rhos_us = started.elapsed().as_micros();
        }

        let t_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.t_g).collect();
        let u_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.u_g).collect();

        // Per block j: C~_j = Sum rho_k * C_ci_j^(k)  [128-bit MSM]
        let started = timings.as_ref().map(|_| Instant::now());
        let c_tildes: Vec<E::G1Affine> = (0..num_blocks)
            .map(|j| {
                let c_bases: Vec<E::G1Affine> =
                    proofs_and_inputs.iter().map(|(p, _)| p.c_ci[j]).collect();
                msm_pippenger::<E::G1>(&c_bases, &rho_bigints, SMALL_SCALAR_BITS).into()
            })
            .collect();
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.c_msm_us = started.elapsed().as_micros();
        }

        // T~, U~ = Sum rho_k * {T, U}^(k)  [128-bit MSMs]
        let started = timings.as_ref().map(|_| Instant::now());
        let t_tilde: E::G1Affine =
            msm_pippenger::<E::G1>(&t_bases, &rho_bigints, SMALL_SCALAR_BITS).into();
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.t_msm_us = started.elapsed().as_micros();
        }

        let started = timings.as_ref().map(|_| Instant::now());
        let u_tilde: E::G1Affine =
            msm_pippenger::<E::G1>(&u_bases, &rho_bigints, SMALL_SCALAR_BITS).into();
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.u_msm_us = started.elapsed().as_micros();
            timings.small_msm_us = timings.c_msm_us + timings.t_msm_us + timings.u_msm_us;
        }

        // V~ = Sum (rho_k * r^(k)) * U^(k)  [full-size MSM]
        let started = timings.as_ref().map(|_| Instant::now());
        let rho_r: Vec<E::ScalarField> = rhos
            .iter()
            .zip(&challenges)
            .map(|(rho, r)| *rho * *r)
            .collect();
        let v_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&u_bases, &rho_r).into();
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.full_msm_us = started.elapsed().as_micros();
        }

        // va~ = Sum rho_k * v_a^(k),  vR~ = Sum rho_k * v_R^(k)
        let started = timings.as_ref().map(|_| Instant::now());
        let v_a_tilde = rhos
            .iter()
            .zip(proofs_and_inputs.iter())
            .fold(E::ScalarField::zero(), |acc, (rho, (p, _))| {
                acc + *rho * p.v_a
            });
        let v_r_tilde = rhos
            .iter()
            .zip(&v_rs)
            .fold(E::ScalarField::zero(), |acc, (rho, vr)| acc + *rho * *vr);
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.scalar_accum_us = started.elapsed().as_micros();
        }

        /////////////////////// Final multi-pairing check ///////////////////////
        let started = timings.as_ref().map(|_| Instant::now());
        let last_left: E::G1Affine = msm_bigint_wnaf::<E::G1>(
            &[v_tilde, -vk.alpha_g, -vk.beta_g],
            &[
                E::ScalarField::ONE.into(),
                v_a_tilde.into(),
                v_r_tilde.into(),
            ],
        )
        .into();
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.last_left_us = started.elapsed().as_micros();
        }

        let mut g1_terms: Vec<E::G1Affine> = c_tildes;
        g1_terms.extend([t_tilde, -u_tilde, last_left]);
        let mut g2_terms: Vec<E::G2Prepared> = vk.delta_h_prep.clone();
        g2_terms.extend([
            vk.delta_w_h_prep.clone(),
            vk.tau_h_prep.clone(),
            vk.h_prep.clone(),
        ]);
        let started = timings.as_ref().map(|_| Instant::now());
        let result = E::multi_pairing(g1_terms, g2_terms);
        if let (Some(timings), Some(started)) = (timings.as_deref_mut(), started) {
            timings.pairing_us = started.elapsed().as_micros();
        }

        result.is_zero()
    }

    /// Batch variant of `eval_last_lagrange_coeffs`. Precomputes domain
    /// constants and the geometric sequence once, then batch-inverts the
    /// denominators across all challenges.
    ///
    /// Returns the Lagrange coefficients per proof.
    pub(crate) fn batch_eval_last_lagrange_coeffs<F: FftField>(
        domain: &Radix2EvaluationDomain<F>,
        challenges: &[F],
        start_ind: usize,
        count: usize,
    ) -> Vec<Vec<F>> {
        let n = challenges.len();

        let group_gen = domain.group_gen();
        let group_gen_inv = domain.group_gen_inv();
        let domain_size = domain.size_as_field_element();
        let start_gen = group_gen.pow([start_ind as u64]);

        // neg_elems[i] = -omega^(start_ind + i), shared across all proofs
        let mut neg_elems = Vec::with_capacity(count);
        let mut neg_cur = -start_gen;
        for _ in 0..count {
            neg_elems.push(neg_cur);
            neg_cur *= &group_gen;
        }

        // Evaluate z_H(tau_k) for all k
        let z_h_vals: Vec<F> = challenges
            .iter()
            .map(|tau| domain.evaluate_vanishing_polynomial(*tau))
            .collect();
        for z in &z_h_vals {
            assert!(!z.is_zero());
        }

        // Lagrange coefficients: L_j(tau) = omega^j * z_H(tau) / (N * (tau - omega^j)).
        // z_H is in the numerator, so we build the denominators
        // N * omega^(-j) * (tau - omega^j) and batch-invert them,
        // folding in start_gen * z_H as the numerator constant.
        let mut all_lagrange_coeffs = Vec::with_capacity(n);
        for (tau, z_h) in challenges.iter().zip(&z_h_vals) {
            let mut l_i = domain_size;
            let mut coeffs = vec![F::zero(); count];
            for (coeff, neg_elem) in coeffs.iter_mut().zip(&neg_elems) {
                *coeff = l_i * (*tau + *neg_elem);
                l_i *= &group_gen_inv;
            }
            batch_inversion_and_mul(&mut coeffs, &(start_gen * *z_h));
            all_lagrange_coeffs.push(coeffs);
        }

        all_lagrange_coeffs
    }
}
