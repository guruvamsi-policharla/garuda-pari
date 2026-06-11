use crate::data_structures::{Proof, VerifyingKey};
use crate::utils::{batch_inversion_and_mul, msm_bigint_wnaf, msm_pippenger};
use crate::ZkPari;
use ark_ec::pairing::Pairing;
use ark_ec::VariableBaseMSM;
use ark_ff::{FftField, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{ops::Neg, rand::RngCore};

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
        Self::batch_verify_inner(proofs_and_inputs, None, vk, rng)
    }

    /// Like [`Self::batch_verify`], but the **last** committed-input block of
    /// every proof is *derived*: it is not transmitted (each `proof.c_ci`
    /// holds only the first `num_blocks - 1` commitments), it is excluded
    /// from the per-proof Fiat-Shamir challenge, and the verifier supplies it
    /// as a linear combination `sum_i coeff_i * base_i` per proof. Its
    /// contribution to the batched pairing is folded into a single MSM across
    /// all proofs:
    ///
    /// ```text
    /// C~_last = sum_k rho_k * (sum_i coeff_{k,i} * base_{k,i})
    /// ```
    ///
    /// so the derived commitments are never materialized as points.
    ///
    /// # Soundness contract
    ///
    /// The caller MUST compute `derived_terms` itself from material that is
    /// absorbed into the challenge (public inputs and transmitted
    /// commitments), bound through a collision-resistant hash — never accept
    /// the terms or coefficients from the prover directly. The bases must be
    /// validated prime-order subgroup elements. Under that contract the
    /// derived commitment is fixed before the challenge is revealed, exactly
    /// as if it had been absorbed, and the random linear combination keeps
    /// the standard `2^-128` batching soundness.
    pub fn batch_verify_derived_tail(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        derived_terms: &[Vec<(E::G1Affine, E::ScalarField)>],
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
    ) -> bool
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        Self::batch_verify_inner(proofs_and_inputs, Some(derived_terms), vk, rng)
    }

    fn batch_verify_inner(
        proofs_and_inputs: &[(Proof<E>, Vec<E::ScalarField>)],
        derived_terms: Option<&[Vec<(E::G1Affine, E::ScalarField)>]>,
        vk: &VerifyingKey<E>,
        rng: &mut impl RngCore,
    ) -> bool
    where
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let n = proofs_and_inputs.len();
        if n == 0 {
            return true;
        }
        // Malformed statements and proofs are rejected, not panicked on
        let num_blocks = vk.delta_h_prep.len();
        let transmitted_blocks = num_blocks - usize::from(derived_terms.is_some());
        let instance_len = vk.succinct_index.instance_len;
        if proofs_and_inputs
            .iter()
            .any(|(p, x)| p.c_ci.len() != transmitted_blocks || x.len() != instance_len - 1)
        {
            return false;
        }
        if derived_terms.is_some_and(|terms| terms.len() != n) {
            return false;
        }
        if n == 1 {
            return match derived_terms {
                None => Self::verify(&proofs_and_inputs[0].0, vk, &proofs_and_inputs[0].1),
                Some(terms) => {
                    // Materialize the single derived commitment and check the
                    // full pairing equation with the derived-tail challenge.
                    let (bases, coeffs): (Vec<E::G1Affine>, Vec<E::ScalarField>) =
                        terms[0].iter().copied().unzip();
                    let derived: E::G1Affine =
                        <E::G1 as VariableBaseMSM>::msm_unchecked(&bases, &coeffs).into();
                    let mut proof = proofs_and_inputs[0].0.clone();
                    proof.c_ci.push(derived);
                    Self::verify_derived(&proof, vk, &proofs_and_inputs[0].1, 1)
                }
            };
        }

        /////////////////////// Challenge computation ///////////////////////
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

        /////////////////////// Per-proof computations ///////////////////////
        let instance_size = vk.succinct_index.instance_len;
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        let all_lagrange_coeffs = Self::batch_eval_last_lagrange_coeffs::<E::ScalarField>(
            &vk.domain,
            &challenges,
            r1cs_orig_num_cnstrs,
            instance_size,
        );

        // For each proof k: compute x_A^(k)(r) and v_R^(k) = (x_A + v_a)^2
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

        /////////////////////// Random linear combination ///////////////////////
        // Sample 128-bit rho <-$ [0, 2^128)^N (sufficient for 2^-128 soundness)
        const SMALL_SCALAR_BITS: usize = 128;
        let rhos: Vec<E::ScalarField> = (0..n)
            .map(|_| {
                let mut bytes = [0u8; 16];
                rng.fill_bytes(&mut bytes);
                E::ScalarField::from_le_bytes_mod_order(&bytes)
            })
            .collect();
        let rho_bigints: Vec<<E::ScalarField as PrimeField>::BigInt> =
            rhos.iter().map(|r| r.into_bigint()).collect();

        let t_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.t_g).collect();
        let u_bases: Vec<E::G1Affine> = proofs_and_inputs.iter().map(|(p, _)| p.u_g).collect();

        // Per transmitted block j: C~_j = Sum rho_k * C_ci_j^(k)  [128-bit MSM]
        let mut c_tildes: Vec<E::G1Affine> = (0..transmitted_blocks)
            .map(|j| {
                let c_bases: Vec<E::G1Affine> =
                    proofs_and_inputs.iter().map(|(p, _)| p.c_ci[j]).collect();
                msm_pippenger::<E::G1>(&c_bases, &rho_bigints, SMALL_SCALAR_BITS).into()
            })
            .collect();

        // Derived last block: C~_last = Sum_k rho_k * (Sum_i coeff_i base_i),
        // folded into ONE full-width MSM over every proof's terms instead of
        // materializing each derived commitment with its own scalar mul.
        if let Some(terms) = derived_terms {
            let total: usize = terms.iter().map(Vec::len).sum();
            let mut bases = Vec::with_capacity(total);
            let mut scalars = Vec::with_capacity(total);
            for (rho, proof_terms) in rhos.iter().zip(terms) {
                for (base, coeff) in proof_terms {
                    bases.push(*base);
                    scalars.push(*rho * *coeff);
                }
            }
            c_tildes.push(<E::G1 as VariableBaseMSM>::msm_unchecked(&bases, &scalars).into());
        }

        // T~, U~ = Sum rho_k * {T, U}^(k)  [128-bit MSMs]
        let t_tilde: E::G1Affine =
            msm_pippenger::<E::G1>(&t_bases, &rho_bigints, SMALL_SCALAR_BITS).into();
        let u_tilde: E::G1Affine =
            msm_pippenger::<E::G1>(&u_bases, &rho_bigints, SMALL_SCALAR_BITS).into();

        // V~ = Sum (rho_k * r^(k)) * U^(k)  [full-size MSM]
        let rho_r: Vec<E::ScalarField> = rhos
            .iter()
            .zip(&challenges)
            .map(|(rho, r)| *rho * *r)
            .collect();
        let v_tilde: E::G1Affine =
            <E::G1 as VariableBaseMSM>::msm_unchecked(&u_bases, &rho_r).into();

        // va~ = Sum rho_k * v_a^(k),  vR~ = Sum rho_k * v_R^(k)
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

        /////////////////////// Final multi-pairing check ///////////////////////
        let last_left: E::G1Affine = msm_bigint_wnaf::<E::G1>(
            &[v_tilde, -vk.alpha_g, -vk.beta_g],
            &[
                E::ScalarField::ONE.into(),
                v_a_tilde.into(),
                v_r_tilde.into(),
            ],
        )
        .into();

        let mut g1_terms: Vec<E::G1Affine> = c_tildes;
        g1_terms.extend([t_tilde, -u_tilde, last_left]);
        let mut g2_terms: Vec<E::G2Prepared> = vk.delta_h_prep.clone();
        g2_terms.extend([
            vk.delta_w_h_prep.clone(),
            vk.tau_h_prep.clone(),
            vk.h_prep.clone(),
        ]);
        let result = E::multi_pairing(g1_terms, g2_terms);

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
