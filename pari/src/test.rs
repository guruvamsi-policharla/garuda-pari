#[cfg(test)]
// use ark_bls12_381::{Bls12_381, Fr as Bls12_381_Fr};
use ark_bn254::Bn254;
// use ark_bls::{Bls12_381, Fr as Bls12_381_Fr};
// use ark_bn254::{Bn254, Fr as Bn254_Fr};
use crate::{
    data_structures::{Proof, ProvingKey, VerifyingKey},
    Pari,
};
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use ark_ff::{Field, UniformRand};
use ark_relations::gr1cs::ConstraintSystemRef;
use ark_relations::{
    gr1cs::{ConstraintSynthesizer, SynthesisError},
    lc,
};
use ark_std::ops::Neg;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;
use std::time::Instant;

#[test]
fn run_test() {
    let _ = test_circuit::<Bn254>();
}

#[test]
fn run_batch_test() {
    let _ = test_batch_circuit::<Bn254>();
}

fn test_circuit<E: Pairing>()
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E: Pairing,
    E::ScalarField: Field,
    E::ScalarField: std::convert::From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let a_val = E::ScalarField::rand(&mut rng);
    let b_val = E::ScalarField::rand(&mut rng);
    let circuit = Circuit1 {
        a: Some(a_val),
        b: Some(b_val),
    };
    let (pk, vk): (ProvingKey<E>, VerifyingKey<E>) = Pari::<E>::keygen(circuit.clone(), &mut rng);
    let proof: Proof<E> = Pari::prove(circuit.clone(), &pk).unwrap();
    let input_assignment = [a_val * b_val];
    assert!(Pari::<E>::verify(&proof, &vk, &input_assignment));
}

#[derive(Clone)]
struct Circuit1<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

fn test_batch_circuit<E: Pairing>()
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E: Pairing,
    E::ScalarField: Field,
    E::ScalarField: std::convert::From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let a_val = E::ScalarField::rand(&mut rng);
    let b_val = E::ScalarField::rand(&mut rng);
    let circuit = Circuit1 {
        a: Some(a_val),
        b: Some(b_val),
    };
    let (pk, vk): (ProvingKey<E>, VerifyingKey<E>) = Pari::<E>::keygen(circuit.clone(), &mut rng);

    let batch_sizes = [2, 32, 512, 8096];

    let max_n = *batch_sizes.iter().max().unwrap();
    let mut proofs_and_inputs = Vec::with_capacity(max_n);
    println!("Generating {} proofs", max_n);
    for _ in 0..max_n {
        let a = E::ScalarField::rand(&mut rng);
        let b = E::ScalarField::rand(&mut rng);
        let circuit = Circuit1 {
            a: Some(a),
            b: Some(b),
        };
        let proof: Proof<E> = Pari::prove(circuit, &pk).unwrap();
        let input = vec![a * b];
        proofs_and_inputs.push((proof, input));
    }

    println!("\n{:-<70}", "");
    println!(
        "{:<8} {:>14} {:>14} {:>10}",
        "N", "Individual", "Batch", "Speedup"
    );
    println!("{:-<70}", "");

    for &n in &batch_sizes {
        let slice = &proofs_and_inputs[..n];

        // Time individual verification: verify each proof one by one
        let start = Instant::now();
        for (proof, input) in slice.iter() {
            assert!(Pari::<E>::verify(proof, &vk, input));
        }
        let individual_elapsed = start.elapsed();

        // Time batch verification
        let start = Instant::now();
        assert!(Pari::<E>::batch_verify(slice, &vk, &mut rng));
        let batch_elapsed = start.elapsed();

        let speedup = individual_elapsed.as_secs_f64() / batch_elapsed.as_secs_f64();

        println!(
            "{:<8} {:>11.3} ms {:>11.3} ms {:>9.2}x",
            n,
            individual_elapsed.as_secs_f64() * 1000.0,
            batch_elapsed.as_secs_f64() * 1000.0,
            speedup,
        );
    }
    println!("{:-<70}", "");
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit1<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a *= &b;
            Ok(a)
        })?;

        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;

        Ok(())
    }
}
