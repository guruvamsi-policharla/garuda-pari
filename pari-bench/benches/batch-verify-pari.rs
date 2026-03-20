use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ff::{Field, PrimeField, UniformRand};
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_relations::lc;
use ark_std::ops::Neg;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;
use pari::Pari;
use std::time::Instant;

#[derive(Clone)]
struct MulCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

impl<F: Field> ConstraintSynthesizer<F> for MulCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(a * b)
        })?;
        for _ in 0..6 {
            cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        }
        Ok(())
    }
}

fn bench_batch_verify<E: Pairing>()
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E::ScalarField: Field + std::convert::From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let a_val = E::ScalarField::rand(&mut rng);
    let b_val = E::ScalarField::rand(&mut rng);
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
    };
    let (pk, vk) = Pari::<E>::keygen(circuit, &mut rng);

    let batch_sizes = [2, 32, 512, 8192, 64768];
    let max_n = *batch_sizes.last().unwrap();

    println!("Generating {} proofs...", max_n);
    let start = Instant::now();
    let mut proofs_and_inputs = Vec::with_capacity(max_n);
    for _ in 0..max_n {
        let a = E::ScalarField::rand(&mut rng);
        let b = E::ScalarField::rand(&mut rng);
        let circuit = MulCircuit {
            a: Some(a),
            b: Some(b),
        };
        let proof = Pari::prove(circuit, &pk).unwrap();
        proofs_and_inputs.push((proof, vec![a * b]));
    }
    println!(
        "Generated {} proofs in {:.1} s\n",
        max_n,
        start.elapsed().as_secs_f64()
    );

    println!(
        "{:<8} {:>15} {:>15} {:>10}",
        "N", "Individual", "Batch", "Speedup"
    );
    println!("{:-<55}", "");

    for &n in &batch_sizes {
        let slice = &proofs_and_inputs[..n];

        let start = Instant::now();
        for (proof, input) in slice.iter() {
            assert!(Pari::<E>::verify(proof, &vk, input));
        }
        let individual = start.elapsed();

        let start = Instant::now();
        assert!(Pari::<E>::batch_verify(slice, &vk, &mut rng));
        let batch = start.elapsed();

        let speedup = individual.as_secs_f64() / batch.as_secs_f64();
        println!(
            "{:<8} {:>12.3} ms {:>12.3} ms {:>9.2}x",
            n,
            individual.as_secs_f64() * 1000.0,
            batch.as_secs_f64() * 1000.0,
            speedup,
        );
    }
}

fn main() {
    bench_batch_verify::<Bn254>();
}
