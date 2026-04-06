use crate::data_structures::VerifyingKey;
use ark_ec::pairing::Pairing;
#[cfg(not(feature = "sol"))]
use shared_utils::transcript::IOPTranscript;

#[cfg(not(feature = "sol"))]
pub fn compute_chall<E: Pairing>(
    vk: &VerifyingKey<E>,
    public_input: &[E::ScalarField],
    t_1: &E::G1Affine,
    t_2: &E::G1Affine,
) -> E::ScalarField {
    let mut transcript = IOPTranscript::<E::ScalarField>::new(crate::Pari::<E>::SNARK_NAME);
    let _ = transcript.append_serializable_element(b"vk", vk);
    let _ = transcript.append_serializable_element(b"input", &public_input.to_vec());
    let _ = transcript.append_serializable_element(b"comm1", t_1);
    let _ = transcript.append_serializable_element(b"comm2", t_2);
    transcript.get_and_append_challenge("r".as_bytes()).unwrap()
}

/// Pre-seed a transcript with the VK. Clone the result for each proof to avoid
/// re-serializing the VK N times during batch verification.
#[cfg(not(feature = "sol"))]
pub fn seed_transcript_with_vk<E: Pairing>(
    vk: &VerifyingKey<E>,
) -> IOPTranscript<E::ScalarField> {
    let mut transcript = IOPTranscript::<E::ScalarField>::new(crate::Pari::<E>::SNARK_NAME);
    let _ = transcript.append_serializable_element(b"vk", vk);
    transcript
}

/// Compute the Fiat-Shamir challenge from a pre-seeded transcript (already
/// contains the VK). Clones the base transcript so the caller can reuse it.
#[cfg(not(feature = "sol"))]
pub fn compute_chall_from_transcript<E: Pairing>(
    base_transcript: &IOPTranscript<E::ScalarField>,
    public_input: &[E::ScalarField],
    t_1: &E::G1Affine,
    t_2: &E::G1Affine,
) -> E::ScalarField {
    let mut transcript = base_transcript.clone();
    let _ = transcript.append_serializable_element(b"input", &public_input.to_vec());
    let _ = transcript.append_serializable_element(b"comm1", t_1);
    let _ = transcript.append_serializable_element(b"comm2", t_2);
    transcript.get_and_append_challenge("r".as_bytes()).unwrap()
}

#[cfg(feature = "sol")]
use ark_ec::AffineRepr;
#[cfg(feature = "sol")]
use ark_ff::PrimeField;

#[cfg(feature = "sol")]
pub fn compute_chall<E: Pairing>(
    vk: &VerifyingKey<E>,
    public_input: &[E::ScalarField],
    t_1: &E::G1Affine,
    t_2: &E::G1Affine,
) -> E::ScalarField
where
    E::BaseField: PrimeField,
    <E::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    use ark_ff::Field;
    use tiny_keccak::{Hasher, Keccak};
    let mut hasher = Keccak::v256();
    let mut output = [0u8; 32];

    let binding = vk.h.x().unwrap();
    let mut vk_h_x = binding.to_base_prime_field_elements();
    let binding = vk.h.y().unwrap();
    let mut vk_h_y = binding.to_base_prime_field_elements();

    let binding = vk.gamma_h.x().unwrap();
    let mut vk_gamma_h_x = binding.to_base_prime_field_elements();
    let binding = vk.gamma_h.y().unwrap();
    let mut vk_gamma_h_y = binding.to_base_prime_field_elements();

    let binding = vk.delta_one_h.x().unwrap();
    let mut vk_delta_one_h_x = binding.to_base_prime_field_elements();
    let binding = vk.delta_one_h.y().unwrap();
    let mut vk_delta_one_h_y = binding.to_base_prime_field_elements();

    let binding = vk.delta_two_h.x().unwrap();
    let mut vk_delta_two_h_x = binding.to_base_prime_field_elements();
    let binding = vk.delta_two_h.y().unwrap();
    let mut vk_delta_two_h_y = binding.to_base_prime_field_elements();

    let binding = vk.tau_h.x().unwrap();
    let mut vk_tau_h_x = binding.to_base_prime_field_elements();
    let binding = vk.tau_h.y().unwrap();
    let mut vk_tau_h_y = binding.to_base_prime_field_elements();

    hasher.update(&encode_packed(t_1.x().unwrap()));
    hasher.update(&encode_packed(t_1.y().unwrap()));
    hasher.update(&encode_packed(t_2.x().unwrap()));
    hasher.update(&encode_packed(t_2.y().unwrap()));
    hasher.update(&encode_packed(E::ScalarField::from(1)));
    for elem in public_input.iter() {
        hasher.update(&encode_packed(*elem));
    }

    hasher.update(&encode_packed(vk.g.x().unwrap()));
    hasher.update(&encode_packed(vk.g.y().unwrap()));
    hasher.update(&encode_packed(vk.alpha_g.x().unwrap()));
    hasher.update(&encode_packed(vk.alpha_g.y().unwrap()));
    hasher.update(&encode_packed(vk.beta_g.x().unwrap()));
    hasher.update(&encode_packed(vk.beta_g.y().unwrap()));
    hasher.update(&encode_packed(vk_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_gamma_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_gamma_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_gamma_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_gamma_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_one_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_one_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_one_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_one_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_two_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_two_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_two_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_two_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_y.next().unwrap()));
    hasher.finalize(&mut output);
    E::ScalarField::from_be_bytes_mod_order(&output)
}

#[cfg(feature = "sol")]
fn encode_packed<F: PrimeField>(field_element: F) -> Vec<u8> {
    use num_bigint::BigUint;

    let a: BigUint = field_element.into();
    let mut b = a.to_bytes_be();

    if b.len() < 32 {
        let mut padded = vec![0u8; 32 - b.len()];
        padded.extend_from_slice(&b);
        b = padded;
    }

    b
}
