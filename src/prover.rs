use std::rc::Rc;

use crate::circuit::{
    blocks_to_witness_indices, r1cs_conversion_witness_map, remap_blocks_through_conversion,
    ZkPariCircuit,
};
use crate::data_structures::{CommittedInputOpening, Proof, ProvingKey};
use crate::utils::compute_chall;
use crate::ZkPari;
use ark_ec::{pairing::Pairing, VariableBaseMSM};
use ark_ff::{AdditiveGroup, Field, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain, Polynomial,
};
use ark_relations::{
    gr1cs::{
        self,
        instance_outliner::{outline_sr1cs, InstanceOutliner},
        predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL,
        ConstraintSystem, Matrix, OptimizationGoal, SynthesisError, R1CS_PREDICATE_LABEL,
    },
    sr1cs::Sr1csAdapter,
};
use ark_std::{cfg_iter_mut, end_timer, rand::RngCore, start_timer, UniformRand};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<E: Pairing> ZkPari<E> {
    /// Produce a proof, sampling fresh blinding randomness for every
    /// committed-input commitment `C_ci_j`.
    pub fn prove<C: ZkPariCircuit<E::ScalarField>, R: RngCore>(
        circuit: C,
        pk: &ProvingKey<E>,
        rng: &mut R,
    ) -> Result<Proof<E>, SynthesisError>
    where
        E::ScalarField: Field,
    {
        let openings: Vec<CommittedInputOpening<E::ScalarField>> = (0..pk.sigma_ci.len())
            .map(|_| CommittedInputOpening::rand(rng))
            .collect();
        Self::prove_inner(circuit, pk, &openings, 0, rng)
    }

    /// Produce a proof with caller-supplied openings `rho_ci_j` (one per
    /// committed-input block), so that `proof.c_ci[j]` equals the commitment
    /// produced by [`ProvingKey::pedersen_commit`] on the same
    /// committed-input values.
    ///
    /// Use this when a block commitment is (derived from) public state, e.g.
    /// a ledger commitment or a verifier-computed aggregate of ledger
    /// commitments, and the proof must open it.
    pub fn prove_with_openings<C: ZkPariCircuit<E::ScalarField>, R: RngCore>(
        circuit: C,
        pk: &ProvingKey<E>,
        openings: &[CommittedInputOpening<E::ScalarField>],
        rng: &mut R,
    ) -> Result<Proof<E>, SynthesisError>
    where
        E::ScalarField: Field,
    {
        Self::prove_inner(circuit, pk, openings, 0, rng)
    }

    /// Like [`Self::prove_with_openings`], but the last `num_derived_tail`
    /// committed-input commitments are **excluded from the Fiat-Shamir
    /// challenge**, matching [`Self::verify_derived`] /
    /// [`Self::batch_verify_derived_tail`] on the verifier side.
    ///
    /// # Soundness contract
    ///
    /// Excluding a commitment from the challenge is sound **only** when that
    /// commitment is a binding, deterministic function of material that *is*
    /// absorbed (the public input and the remaining commitments) — e.g. the
    /// verifier recomputes it as a linear combination of ledger commitments
    /// with coefficients fixed by a public input that was itself derived by
    /// hashing those commitments. The caller owns that binding argument.
    pub fn prove_with_openings_derived<C: ZkPariCircuit<E::ScalarField>, R: RngCore>(
        circuit: C,
        pk: &ProvingKey<E>,
        openings: &[CommittedInputOpening<E::ScalarField>],
        num_derived_tail: usize,
        rng: &mut R,
    ) -> Result<Proof<E>, SynthesisError>
    where
        E::ScalarField: Field,
    {
        Self::prove_inner(circuit, pk, openings, num_derived_tail, rng)
    }

    fn prove_inner<C: ZkPariCircuit<E::ScalarField>, R: RngCore>(
        circuit: C,
        pk: &ProvingKey<E>,
        openings: &[CommittedInputOpening<E::ScalarField>],
        num_derived_tail: usize,
        rng: &mut R,
    ) -> Result<Proof<E>, SynthesisError>
    where
        E::ScalarField: Field,
    {
        let timer_p = start_timer!(|| "Total Proving time");
        let (cs, block_indices) = Self::circuit_to_prover_cs(circuit)?;
        // Check if the constraint system has only one predicate which is Squared R1CS
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
        // The circuit must declare exactly the committed inputs the keys were
        // generated for
        assert_eq!(
            block_indices, pk.committed_witness_indices,
            "the circuit declared different committed-input blocks than the proving key"
        );
        assert_eq!(
            openings.len(),
            block_indices.len(),
            "expected one opening per committed-input block ({}), got {}",
            block_indices.len(),
            openings.len()
        );
        end_timer!(timer_extract_info);

        /////////////////////// Computing the evaluation domain ///////////////////////
        let timer_eval_domain = start_timer!(|| "Computing the evaluation domain");
        let domain = GeneralEvaluationDomain::<E::ScalarField>::new(num_constraints).unwrap();
        let domain_size = domain.size();
        end_timer!(timer_eval_domain);

        /////////////////////// Sampling the masks ///////////////////////
        // h(X) = eta_1 + eta_2 X masks the A-side; the blocks' openings mask
        // the B-side as (rho_ci_1 + ... + rho_ci_J) v_K through the
        // committed-input commitments.
        let timer_masks = start_timer!(|| "Sampling vanishing-polynomial masks");
        let eta_1 = E::ScalarField::rand(rng);
        let eta_2 = E::ScalarField::rand(rng);
        let rho_ci: E::ScalarField = openings
            .iter()
            .fold(E::ScalarField::zero(), |acc, o| acc + o.rho);
        end_timer!(timer_masks);

        /////////////////////// Computing polynomials z_A, z_B, w_A ///////////////////////
        // After instance outlining, w_B == z_B (the B matrix has no instance
        // columns), so only three vectors are needed.
        let timer_compute_za_zb_wa = start_timer!(|| "Computing vectors z_A, z_B, w_A");
        let (z_a, z_b, w_a) = Self::compute_za_zb_wa(
            domain,
            &matrices[0],
            &matrices[1],
            instance_assignment,
            witness_assignment,
            num_constraints,
        )
        .unwrap();
        end_timer!(timer_compute_za_zb_wa);

        //////////////////////// Interpolating polynomials ///////////////////////
        let timer_interp = start_timer!(|| "Interpolating z_a, z_b, w_a polynomials");
        let z_a_hat = Evaluations::from_vec_and_domain(z_a, domain).interpolate();
        let z_b_hat = Evaluations::from_vec_and_domain(z_b, domain).interpolate();
        let w_a_hat = Evaluations::from_vec_and_domain(w_a, domain).interpolate();
        end_timer!(timer_interp);

        // x_A(r) is needed for the debug consistency check below; the masks on
        // z_A and w_A are identical, so the unmasked difference already equals
        // x_A.
        #[cfg(debug_assertions)]
        let (z_a_hat_check, z_b_hat_check) = (z_a_hat.clone(), z_b_hat.clone());

        /////////////////////// Computing the quotient polynomial ///////////////////////
        // The masked quotient is computed by expansion, never squaring the
        // masked (degree m+1) polynomial. With z := z_A^orig, b := z_B^orig,
        // h := eta_1 + eta_2 X and v := v_K = X^m - 1:
        //
        //   (z + h v)^2 - (b + rho v) = (z^2 - b) + v (2 h z + h^2 v - rho)
        //
        // so q~ = q_orig + 2 h z + h^2 v - rho with q_orig = (z^2 - b)/v_K.
        // This keeps every FFT at size <= 2m (squaring degree m+1 would round
        // the multiplication domain up to 4m).
        let timer_quotient = start_timer!(|| "Computing the quotient polynomial");
        let (q_orig, _remainder) =
            (&z_a_hat * &z_a_hat - &z_b_hat).divide_by_vanishing_poly(domain);
        #[cfg(debug_assertions)]
        assert!(_remainder.is_zero(), "constraint system is not satisfied");

        let mut q_coeffs = q_orig.coeffs;
        q_coeffs.resize(domain_size + 3, E::ScalarField::zero());
        // + 2 h z
        let two_eta_1 = eta_1.double();
        let two_eta_2 = eta_2.double();
        for (i, z_i) in z_a_hat.coeffs.iter().enumerate() {
            q_coeffs[i] += two_eta_1 * z_i;
            q_coeffs[i + 1] += two_eta_2 * z_i;
        }
        // + h^2 v_K = (eta_1^2 + 2 eta_1 eta_2 X + eta_2^2 X^2)(X^m - 1), - rho
        let eta_1_sq = eta_1.square();
        let eta_cross = (eta_1 * eta_2).double();
        let eta_2_sq = eta_2.square();
        q_coeffs[0] -= eta_1_sq + rho_ci;
        q_coeffs[1] -= eta_cross;
        q_coeffs[2] -= eta_2_sq;
        q_coeffs[domain_size] += eta_1_sq;
        q_coeffs[domain_size + 1] += eta_cross;
        q_coeffs[domain_size + 2] += eta_2_sq;
        let q_tilde = DensePolynomial::from_coefficients_vec(q_coeffs);

        // Cross-check the expansion against the definitional computation
        #[cfg(debug_assertions)]
        {
            let mask_poly =
                |poly: &DensePolynomial<E::ScalarField>, c0: E::ScalarField, c1: E::ScalarField| {
                    let mut coeffs = poly.coeffs.clone();
                    coeffs.resize(coeffs.len().max(domain_size + 2), E::ScalarField::zero());
                    coeffs[0] -= c0;
                    coeffs[1] -= c1;
                    coeffs[domain_size] += c0;
                    coeffs[domain_size + 1] += c1;
                    DensePolynomial::from_coefficients_vec(coeffs)
                };
            let z_a_masked = mask_poly(&z_a_hat_check, eta_1, eta_2);
            let z_b_masked = mask_poly(&z_b_hat_check, rho_ci, E::ScalarField::zero());
            let (q_check, rem) =
                (&z_a_masked * &z_a_masked - &z_b_masked).divide_by_vanishing_poly(domain);
            assert!(rem.is_zero());
            assert_eq!(q_tilde, q_check, "expanded quotient mismatch");
        }
        end_timer!(timer_quotient);

        /////////////////////// Applying the vanishing-polynomial masks ///////////////////////
        // w_A(X) += (eta_1 + eta_2 X) v_K(X); the B-side mask is folded into
        // R(X) below.
        let timer_masking = start_timer!(|| "Masking the polynomials");
        #[cfg(debug_assertions)]
        let x_a_poly_check = &z_a_hat - &w_a_hat;
        let w_a_masked = {
            let mut coeffs = w_a_hat.coeffs;
            coeffs.resize(coeffs.len().max(domain_size + 2), E::ScalarField::zero());
            coeffs[0] -= eta_1;
            coeffs[1] -= eta_2;
            coeffs[domain_size] += eta_1;
            coeffs[domain_size + 1] += eta_2;
            DensePolynomial::from_coefficients_vec(coeffs)
        };
        end_timer!(timer_masking);

        /////////////////////// Computing the commitments (C_ci_j, T) ///////////////////////
        let timer_batch_commit = start_timer!(|| "Batch commitment");

        // Per block j: C_ci_j = sum_i x_i Sigma_ci_j[i] + rho_ci_j Gamma_ci_j,
        // with the values gathered from the declared witness indices
        let mut c_cis = Vec::with_capacity(block_indices.len());
        for ((block, sigma_ci_j), (gamma_ci_j, opening)) in block_indices
            .iter()
            .zip(&pk.sigma_ci)
            .zip(pk.gamma_ci.iter().zip(openings))
        {
            let block_values: Vec<E::ScalarField> =
                block.iter().map(|&w| witness_assignment[w]).collect();
            let c_ci_j: E::G1Affine = (E::G1::msm_unchecked(sigma_ci_j, &block_values)
                + *gamma_ci_j * opening.rho)
                .into();
            c_cis.push(c_ci_j);
        }

        // T = sum_j w_j Sigma_W[j] + eta_1 Sigma_W[k+2] + eta_2 Sigma_W[k+3]
        //     + sum_i q~[i] Sigma_Q^comm[i]
        // where the sum ranges over the ordinary (non-committed) witnesses in
        // ascending index order, matching Sigma_W. Computed as one MSM to
        // amortize the Pippenger buckets.
        let mut is_committed = vec![false; witness_assignment.len()];
        for block in &block_indices {
            for &w in block {
                is_committed[w] = true;
            }
        }
        let ordinary_witnesses: Vec<E::ScalarField> = witness_assignment
            .iter()
            .zip(&is_committed)
            .filter(|(_, committed)| !**committed)
            .map(|(value, _)| *value)
            .collect();
        debug_assert_eq!(ordinary_witnesses.len(), pk.sigma_w.len());
        // Separate MSMs over the SRS slices (avoids copying the bases)
        let t_w = E::G1::msm_unchecked(&pk.sigma_w, &ordinary_witnesses);
        let t_mask = E::G1::msm_unchecked(
            &[pk.sigma_mask_const, pk.sigma_mask_linear],
            &[eta_1, eta_2],
        );
        let t_q = E::G1::msm_unchecked(&pk.sigma_q_comm[..q_tilde.coeffs.len()], &q_tilde.coeffs);
        let t: E::G1Affine = (t_w + t_mask + t_q).into();
        end_timer!(timer_batch_commit);

        /////////////////////// Computing the challenge ///////////////////////
        let timer_init_transcript = start_timer!(|| "Computing Challenge");
        // Derived-tail commitments are bound transitively by the caller (see
        // `prove_with_openings_derived`) and excluded from the transcript.
        assert!(
            num_derived_tail <= c_cis.len(),
            "cannot derive more blocks than exist"
        );
        let absorbed = c_cis.len() - num_derived_tail;
        let challenge = compute_chall::<E>(
            &pk.verifying_key,
            &instance_assignment[1..].to_vec(),
            &c_cis[..absorbed],
            &t,
        );
        end_timer!(timer_init_transcript);

        /////////////////////// Masked evaluation at the challenge ///////////////////////
        // v_a = z_A(r) - x_A(r) = w_A^masked(r)
        let timer_eval = start_timer!(|| "Evaluating v_a");
        let v_a = w_a_masked.evaluate(&challenge);
        end_timer!(timer_eval);

        /////////////////////// Proof of correct opening ///////////////////////
        let timer_opening = start_timer!(|| "Batch Opening");
        let timer_open_poly = start_timer!(|| "Computing the opening polynomials");

        // R(X) = z_B(X) - x_B(X) + v_K(X) q~(X)
        //      = z_B^orig(X) + rho_ci v_K(X) + v_K(X) q~(X)
        // (x_B = 0 after instance outlining, and w_B == z_B)
        let mut r_coeffs = z_b_hat.coeffs;
        r_coeffs.resize(
            (domain_size + 1).max(q_tilde.coeffs.len() + domain_size),
            E::ScalarField::zero(),
        );
        r_coeffs[0] -= rho_ci;
        r_coeffs[domain_size] += rho_ci;
        for (i, q_i) in q_tilde.coeffs.iter().enumerate() {
            r_coeffs[i] -= q_i;
            r_coeffs[i + domain_size] += q_i;
        }
        let r_poly = DensePolynomial::from_coefficients_vec(r_coeffs);

        // v_R = R(r) = (v_a + x_A(r))^2 - x_B(r); recomputed by the verifier from v_a
        let v_r = r_poly.evaluate(&challenge);
        #[cfg(debug_assertions)]
        {
            let x_a_at_r = x_a_poly_check.evaluate(&challenge);
            assert_eq!(
                v_r,
                (v_a + x_a_at_r).square(),
                "v_R must equal (v_a + x_A(r))^2"
            );
        }

        // W_A(X) = (z_A(X) - x_A(X) - v_a)/(X - r), of degree <= m
        // W_R(X) = (R(X) - v_R)/(X - r), of degree <= 2m+1
        let one = E::ScalarField::ONE;
        let chall_vanishing_poly = DensePolynomial::from_coefficients_vec(vec![-challenge, one]);
        let v_a_poly = DensePolynomial::from_coefficients_vec(vec![v_a]);
        let v_r_poly = DensePolynomial::from_coefficients_vec(vec![v_r]);
        let witness_a = (&w_a_masked - &v_a_poly) / &chall_vanishing_poly;
        let witness_r = (&r_poly - &v_r_poly) / &chall_vanishing_poly;
        end_timer!(timer_open_poly);

        // U = sum_i W_A[i] Sigma_A[i] + sum_i W_R[i] Sigma_R[i]
        // Two MSMs directly over the SRS slices: merging them into one call
        // costs a ~150MB base-vector copy at large sizes, which outweighs the
        // bucket amortization.
        let timer_msms = start_timer!(|| "Computing the opening MSMs");
        debug_assert!(witness_a.coeffs.len() <= pk.sigma_a.len());
        debug_assert!(witness_r.coeffs.len() <= pk.sigma_r.len());
        let w_a_proof =
            E::G1::msm_unchecked(&pk.sigma_a[..witness_a.coeffs.len()], &witness_a.coeffs);
        let w_r_proof =
            E::G1::msm_unchecked(&pk.sigma_r[..witness_r.coeffs.len()], &witness_r.coeffs);
        let u: E::G1Affine = (w_a_proof + w_r_proof).into();
        end_timer!(timer_msms);
        end_timer!(timer_opening);

        let output = Ok(Proof {
            c_ci: c_cis,
            t_g: t,
            u_g: u,
            v_a,
        });

        end_timer!(timer_p);
        output
    }

    /// Synthesize the circuit in proving mode and return the finalized SR1CS
    /// constraint system (with assignments) together with the declared
    /// committed-input blocks (as witness indices).
    #[allow(clippy::type_complexity)]
    pub fn circuit_to_prover_cs<C: ZkPariCircuit<E::ScalarField>>(
        circuit: C,
    ) -> Result<(ConstraintSystem<E::ScalarField>, Vec<Vec<usize>>), SynthesisError>
    where
        E: Pairing,
        E::ScalarField: Field,
    {
        // Start up the constraint System and synthesize the circuit
        let timer_cs_startup = start_timer!(|| "Prover constraint System Startup");
        let timer_synthesize_circuit = start_timer!(|| "Synthesize Circuit");
        let cs: gr1cs::ConstraintSystemRef<E::ScalarField> = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        let blocks = circuit.synthesize(cs.clone())?;
        let mut block_indices = blocks_to_witness_indices(&blocks);
        end_timer!(timer_synthesize_circuit);
        let timer_inlining = start_timer!(|| "Inlining constraints");
        cs.finalize();
        end_timer!(timer_inlining);

        let sr1cs_timer = start_timer!(|| "Convert to SR1CS");
        // Circuits that natively register the SR1CS predicate skip the R1CS-to-SR1CS conversion.
        // The conversion does NOT preserve witness indices (it rebuilds the
        // witness space by first use, interleaved with square variables and
        // public-input copies), so the declared committed-input indices are
        // remapped into the converted numbering — the same remapping keygen
        // applied. The subsequent instance outlining only appends witness
        // variables, so the (remapped) indices stay valid through it.
        let native_sr1cs = cs.has_predicate(SR1CS_PREDICATE_LABEL);
        let mut sr1cs_inner = if native_sr1cs {
            cs.into_inner().unwrap()
        } else {
            let conversion_map = r1cs_conversion_witness_map(
                &cs.to_matrices().unwrap()[R1CS_PREDICATE_LABEL],
                cs.num_instance_variables(),
            );
            let mut inner = cs.into_inner().unwrap();
            let declared_values: Vec<Vec<E::ScalarField>> = block_indices
                .iter()
                .map(|block| {
                    block
                        .iter()
                        .map(|&w| inner.assignments.witness_assignment[w])
                        .collect()
                })
                .collect();
            block_indices = remap_blocks_through_conversion(&block_indices, &conversion_map);
            let sr1cs_cs = Sr1csAdapter::r1cs_to_sr1cs_with_assignment(&mut inner).unwrap();
            let sr1cs_inner = sr1cs_cs.into_inner().unwrap();
            // The remapped indices must carry the declared variables' values;
            // this catches any drift between the adapter's allocation order
            // and r1cs_conversion_witness_map.
            for (block, values) in block_indices.iter().zip(&declared_values) {
                for (&w, value) in block.iter().zip(values) {
                    assert_eq!(
                        sr1cs_inner.assignments.witness_assignment[w], *value,
                        "R1CS-to-SR1CS conversion witness map out of sync with the adapter's \
                         allocation order"
                    );
                }
            }
            sr1cs_inner
        };

        sr1cs_inner
            .perform_instance_outlining(InstanceOutliner {
                pred_label: SR1CS_PREDICATE_LABEL.to_string(),
                func: Rc::new(outline_sr1cs),
            })
            .expect("instance outlining failed");
        end_timer!(sr1cs_timer);
        end_timer!(timer_cs_startup);
        Ok((sr1cs_inner, block_indices))
    }

    /// Evaluate the constraint rows once over the full assignment, returning
    /// `(z_A, z_B, w_A)`.
    ///
    /// After instance outlining the instance variables appear only in the
    /// last `instance_len` rows, each as `(x_i - w_copy_i)` on the A-side
    /// with an empty B-side. Hence the punctured ("instance zeroed")
    /// evaluations need no second pass:
    /// - `w_B == z_B` (no instance column in B),
    /// - `w_A == z_A` except on the outlining rows, where removing the
    ///   instance contribution subtracts `x_i`.
    #[allow(clippy::type_complexity)]
    pub(crate) fn compute_za_zb_wa(
        domain: GeneralEvaluationDomain<E::ScalarField>,
        a_mat: &Matrix<E::ScalarField>,
        b_mat: &Matrix<E::ScalarField>,
        instance_assignment: &[E::ScalarField],
        witness_assignment: &[E::ScalarField],
        num_constraints: usize,
    ) -> Result<
        (
            Vec<E::ScalarField>,
            Vec<E::ScalarField>,
            Vec<E::ScalarField>,
        ),
        SynthesisError,
    > {
        let mut assignment: Vec<E::ScalarField> = instance_assignment.to_vec();
        assignment.extend_from_slice(witness_assignment);

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

        let instance_len = instance_assignment.len();
        let outline_start = num_constraints - instance_len;
        let mut w_a = z_a.clone();
        for (i, x_i) in instance_assignment.iter().enumerate() {
            w_a[outline_start + i] -= x_i;
        }

        // Validate the outlining structure against the definitional
        // (punctured-assignment) evaluation
        #[cfg(debug_assertions)]
        {
            let mut punctured_assignment: Vec<E::ScalarField> =
                vec![E::ScalarField::zero(); instance_len];
            punctured_assignment.extend_from_slice(witness_assignment);
            for (row, (at_i, bt_i)) in a_mat.iter().zip(b_mat).enumerate() {
                let w_a_row: E::ScalarField = Sr1csAdapter::<E::ScalarField>::evaluate_constraint(
                    at_i,
                    &punctured_assignment,
                );
                let w_b_row: E::ScalarField = Sr1csAdapter::<E::ScalarField>::evaluate_constraint(
                    bt_i,
                    &punctured_assignment,
                );
                assert_eq!(w_a_row, w_a[row], "instance column outside outlining rows");
                assert_eq!(w_b_row, z_b[row], "instance column in the B matrix");
            }
        }

        Ok((z_a, z_b, w_a))
    }
}
