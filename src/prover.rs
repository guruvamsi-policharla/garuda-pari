use std::rc::Rc;

use crate::circuit::{blocks_to_witness_indices, ZkPariCircuit};
use crate::data_structures::{CommittedInputOpening, Proof, ProvingKey};
use crate::utils::compute_chall;
use crate::ZkPari;
use ark_ec::{pairing::Pairing, VariableBaseMSM};
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
        ConstraintSystem, Matrix, OptimizationGoal, SynthesisError,
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
        Self::prove_inner(circuit, pk, &openings, rng)
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
        Self::prove_inner(circuit, pk, openings, rng)
    }

    fn prove_inner<C: ZkPariCircuit<E::ScalarField>, R: RngCore>(
        circuit: C,
        pk: &ProvingKey<E>,
        openings: &[CommittedInputOpening<E::ScalarField>],
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

        /////////////////////// Applying the vanishing-polynomial masks ///////////////////////
        // z_A(X) = z_A^orig(X) + (eta_1 + eta_2 X) v_K(X), with v_K(X) = X^m - 1
        // z_B(X) = z_B^orig(X) + rho_ci v_K(X)
        let timer_masking = start_timer!(|| "Masking the polynomials");
        let apply_a_mask = |poly: &DensePolynomial<E::ScalarField>| {
            let mut coeffs = poly.coeffs.clone();
            coeffs.resize(coeffs.len().max(domain_size + 2), E::ScalarField::zero());
            coeffs[0] -= eta_1;
            coeffs[1] -= eta_2;
            coeffs[domain_size] += eta_1;
            coeffs[domain_size + 1] += eta_2;
            DensePolynomial::from_coefficients_vec(coeffs)
        };
        let apply_b_mask = |poly: &DensePolynomial<E::ScalarField>| {
            let mut coeffs = poly.coeffs.clone();
            coeffs.resize(coeffs.len().max(domain_size + 1), E::ScalarField::zero());
            coeffs[0] -= rho_ci;
            coeffs[domain_size] += rho_ci;
            DensePolynomial::from_coefficients_vec(coeffs)
        };
        let z_a_masked = apply_a_mask(&z_a_hat);
        let z_b_masked = apply_b_mask(&z_b_hat);
        let w_a_masked = apply_a_mask(&w_a_hat);
        let w_b_masked = apply_b_mask(&w_b_hat);
        end_timer!(timer_masking);

        /////////////////////// Computing the quotient polynomial ///////////////////////
        // q~(X) = (z_A(X)^2 - z_B(X)) / v_K(X), of degree <= m+2
        let timer_quotient = start_timer!(|| "Computing the quotient polynomial");
        let (q_tilde, _remainder) =
            (&z_a_masked * &z_a_masked - &z_b_masked).divide_by_vanishing_poly(domain);
        #[cfg(debug_assertions)]
        assert!(_remainder.is_zero());
        end_timer!(timer_quotient);

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
            let c_ci_j: E::G1Affine =
                (E::G1::msm_unchecked(sigma_ci_j, &block_values) + *gamma_ci_j * opening.rho)
                    .into();
            c_cis.push(c_ci_j);
        }

        // T = sum_j w_j Sigma_W[j] + eta_1 Sigma_W[k+2] + eta_2 Sigma_W[k+3]
        //     + sum_i q~[i] Sigma_Q^comm[i]
        // where the sum ranges over the ordinary (non-committed) witnesses in
        // ascending index order, matching Sigma_W
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
        let t_w = E::G1::msm_unchecked(&pk.sigma_w, &ordinary_witnesses);
        let t_mask = E::G1::msm_unchecked(
            &[pk.sigma_mask_const, pk.sigma_mask_linear],
            &[eta_1, eta_2],
        );
        let t_q = E::G1::msm_unchecked(&pk.sigma_q_comm, &q_tilde.coeffs);
        let t: E::G1Affine = (t_w + t_mask + t_q).into();
        end_timer!(timer_batch_commit);

        /////////////////////// Computing the challenge ///////////////////////
        let timer_init_transcript = start_timer!(|| "Computing Challenge");
        let challenge = compute_chall::<E>(
            &pk.verifying_key,
            &instance_assignment[1..].to_vec(),
            &c_cis,
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

        // R(X) = z_B(X) - x_B(X) + v_K(X) q~(X) = w_B^masked(X) + v_K(X) q~(X)
        let mut r_coeffs = w_b_masked.coeffs.clone();
        r_coeffs.resize(
            r_coeffs.len().max(q_tilde.coeffs.len() + domain_size),
            E::ScalarField::zero(),
        );
        for (i, q_i) in q_tilde.coeffs.iter().enumerate() {
            r_coeffs[i] -= q_i;
            r_coeffs[i + domain_size] += q_i;
        }
        let r_poly = DensePolynomial::from_coefficients_vec(r_coeffs);

        // v_R = R(r) = (v_a + x_A(r))^2 - x_B(r); recomputed by the verifier from v_a
        let v_r = r_poly.evaluate(&challenge);
        #[cfg(debug_assertions)]
        {
            let x_a_at_r = z_a_masked.evaluate(&challenge) - v_a;
            let x_b_at_r = z_b_hat.evaluate(&challenge) - w_b_hat.evaluate(&challenge);
            assert!(
                x_b_at_r.is_zero(),
                "x_B(r) must vanish after SR1CS instance outlining"
            );
            assert_eq!(v_r, (v_a + x_a_at_r).square() - x_b_at_r);
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
        let timer_msms = start_timer!(|| "Computing the opening MSMs");
        debug_assert!(witness_a.coeffs.len() <= pk.sigma_a.len());
        debug_assert!(witness_r.coeffs.len() <= pk.sigma_r.len());
        let w_a_proof = E::G1::msm_unchecked(&pk.sigma_a, &witness_a.coeffs);
        let w_r_proof = E::G1::msm_unchecked(&pk.sigma_r, &witness_r.coeffs);
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
        let block_indices = blocks_to_witness_indices(&blocks);
        end_timer!(timer_synthesize_circuit);
        let timer_inlining = start_timer!(|| "Inlining constraints");
        cs.finalize();
        end_timer!(timer_inlining);

        let sr1cs_timer = start_timer!(|| "Convert to SR1CS");
        // Circuits that natively register the SR1CS predicate skip the R1CS-to-SR1CS conversion.
        // Both the conversion and the instance outlining only append witness
        // variables, so the declared indices stay valid.
        let native_sr1cs = cs.has_predicate(SR1CS_PREDICATE_LABEL);
        let mut sr1cs_inner = if native_sr1cs {
            cs.into_inner().unwrap()
        } else {
            let sr1cs_cs =
                Sr1csAdapter::r1cs_to_sr1cs_with_assignment(&mut cs.into_inner().unwrap())
                    .unwrap();
            sr1cs_cs.into_inner().unwrap()
        };

        let _ = sr1cs_inner.perform_instance_outlining(InstanceOutliner {
            pred_label: SR1CS_PREDICATE_LABEL.to_string(),
            func: Rc::new(outline_sr1cs),
        });
        end_timer!(sr1cs_timer);
        end_timer!(timer_cs_startup);
        Ok((sr1cs_inner, block_indices))
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn compute_wa_wb_za_zb(
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
