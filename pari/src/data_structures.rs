use ark_ec::pairing::Pairing;
use ark_ec::VariableBaseMSM;
use ark_ff::Field;
use ark_poly::Radix2EvaluationDomain;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use core::ops::Sub;

/// The proving key for ZK-Pari.
///
/// Witness commitment is split into two bases (sigma_1 / delta_1 and sigma_2 / delta_2)
/// to support Pedersen-style commitments on the sigma_1 partition.
#[derive(CanonicalSerialize, Clone)]
pub struct ProvingKey<E>
where
    E: Pairing,
    E::ScalarField: Field,
{
    /// Punctured commitment key for w^(1): [(alpha*a_i(tau)+beta*b_i(tau))/delta_1 * G]
    pub sigma_1: Vec<E::G1Affine>,
    /// Punctured commitment key for w^(2): [(alpha*a_i(tau)+beta*b_i(tau))/delta_2 * G]
    pub sigma_2: Vec<E::G1Affine>,
    /// Opening key for A polynomials: [alpha*tau^i * G]
    pub sigma_a: Vec<E::G1Affine>,
    /// Opening key for B polynomials: [beta*tau^i * G]
    pub sigma_b: Vec<E::G1Affine>,
    /// Quotient commitment key: [tau^i/delta_2 * G]
    pub sigma_q_comm: Vec<E::G1Affine>,
    /// Quotient opening key: [tau^i * G]
    pub sigma_q_opening: Vec<E::G1Affine>,

    /// ZK commitment key: alpha*v_K(tau)/delta_2 * G
    pub sigma_a_zk: E::G1Affine,
    /// ZK commitment key: beta*v_K(tau)/delta_2 * G
    pub sigma_b_zk: E::G1Affine,

    /// Hiding element: (gamma/delta_1)*G
    pub gamma_over_delta_1_g: E::G1Affine,
    /// Hiding element: (gamma/delta_2)*G
    pub gamma_over_delta_2_g: E::G1Affine,
    /// Hiding element: gamma*G
    pub gamma_g: E::G1Affine,

    pub verifying_key: VerifyingKey<E>,
}

/// The verifying key for ZK-Pari
#[derive(Clone, Debug)]
pub struct VerifyingKey<E: Pairing> {
    pub succinct_index: SuccinctIndex,
    pub g: E::G1Affine,
    pub alpha_g: E::G1Affine,
    pub beta_g: E::G1Affine,
    pub gamma_h: E::G2Affine,
    pub gamma_h_prep: E::G2Prepared,
    pub delta_one_h: E::G2Affine,
    pub delta_one_h_prep: E::G2Prepared,
    pub delta_two_h: E::G2Affine,
    pub delta_two_h_prep: E::G2Prepared,
    pub tau_h: E::G2Affine,
    pub tau_h_prep: E::G2Prepared,
    pub h: E::G2Affine,
    pub h_prep: E::G2Prepared,
    pub domain: Radix2EvaluationDomain<E::ScalarField>,
}

impl<E: Pairing> CanonicalSerialize for VerifyingKey<E> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.succinct_index
            .serialize_with_mode(&mut writer, compress)?;
        self.alpha_g.serialize_with_mode(&mut writer, compress)?;
        self.beta_g.serialize_with_mode(&mut writer, compress)?;
        self.gamma_h.serialize_with_mode(&mut writer, compress)?;
        self.delta_one_h
            .serialize_with_mode(&mut writer, compress)?;
        self.delta_two_h
            .serialize_with_mode(&mut writer, compress)?;
        self.tau_h.serialize_with_mode(&mut writer, compress)?;
        self.g.serialize_with_mode(&mut writer, compress)?;
        self.h.serialize_with_mode(&mut writer, compress)?;

        Ok(())
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let mut size = 0;
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.succinct_index, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.alpha_g, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.beta_g, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.gamma_h, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.delta_one_h, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.delta_two_h, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.tau_h, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.g, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.h, compress);
        size
    }
}

/// The succinct index for ZK-Pari.
/// Contains enough information from the SR1CS to verify the proof, plus
/// the witness split point for the sigma_1/sigma_2 partition.
#[derive(CanonicalSerialize, Clone, Debug)]
pub struct SuccinctIndex {
    pub num_constraints: usize,
    pub instance_len: usize,
    /// Number of witness variables committed via sigma_1/delta_1.
    /// The remaining witness variables are committed via sigma_2/delta_2.
    pub witness_split: usize,
}

#[derive(CanonicalSerialize, Clone)]
pub struct Proof<E: Pairing> {
    /// Punctured witness commitment for w^(1) (blinded, under delta_1)
    pub t_1: E::G1Affine,
    /// Punctured witness commitment for w^(2) + quotient (blinded, under delta_2)
    pub t_2: E::G1Affine,
    /// Opening proof + hiding-KZG component
    pub u_1: E::G1Affine,
    /// Hiding-KZG auxiliary point
    pub u_2: E::G1Affine,
    /// Masked evaluation of witness-A polynomial at challenge
    pub v_a: E::ScalarField,
    /// Masked evaluation of witness-B polynomial at challenge
    pub v_b: E::ScalarField,
}

/// Opening for the Pedersen commitment embedded in T1.
///
/// In the simplified construction all vanishing-polynomial masking lives in T2,
/// so T1 = Σ w_i · Σ_1[i] + zeta_1 · (γ/δ_1)·G — a standard 2-generator
/// Pedersen commitment with a single blinding scalar.
#[derive(Clone, Debug)]
pub struct PedersenOpening<F: Field> {
    pub zeta_1: F,
}

impl<F: Field> PedersenOpening<F> {
    pub fn rand<R: RngCore>(rng: &mut R) -> Self {
        Self {
            zeta_1: F::rand(rng),
        }
    }
}

impl<F: Field> Sub for &PedersenOpening<F> {
    type Output = PedersenOpening<F>;

    fn sub(self, rhs: Self) -> PedersenOpening<F> {
        PedersenOpening {
            zeta_1: self.zeta_1 - rhs.zeta_1,
        }
    }
}

impl<E: Pairing> ProvingKey<E> {
    /// Compute the Pedersen commitment for a single value under sigma_1.
    ///
    /// Returns the G1 point:
    ///   value * Sigma1[0] + opening.zeta_1 * (gamma/delta_1)*G
    ///
    /// This matches T1 produced by the prover when `witness_split=1` and the
    /// same opening is supplied via `prove_with_pedersen_opening`.
    pub fn pedersen_commit(
        &self,
        value: E::ScalarField,
        opening: &PedersenOpening<E::ScalarField>,
    ) -> E::G1Affine {
        assert!(
            !self.sigma_1.is_empty(),
            "sigma_1 must have at least one element (witness_split >= 1)"
        );
        E::G1::msm_unchecked(
            &[self.sigma_1[0], self.gamma_over_delta_1_g],
            &[value, opening.zeta_1],
        )
        .into()
    }
}
