use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::{AdditiveGroup, AffineRepr};
use ark_ff::{Field, PrimeField, UniformRand};
use ark_relations::gr1cs::predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL;
use ark_relations::gr1cs::predicate::PredicateConstraintSystem;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, R1CS_PREDICATE_LABEL, SynthesisError,
};
use ark_relations::lc;
use ark_std::ops::Neg;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;
use pari::Pari;
use std::time::Instant;

// ---------------------------------------------------------------------------
// R1CS multiplication circuit (configurable number of constraints)
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct MulCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    num_constraints: usize,
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
        for _ in 0..self.num_constraints {
            cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Native SR1CS range proof circuit (N-bit)
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct RangeProofCircuit {
    value: Option<u64>,
    num_bits: usize,
}

impl<F: Field> ConstraintSynthesizer<F> for RangeProofCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let value = self.value;
        let num_bits = self.num_bits;

        let v = cs.new_witness_variable(|| {
            let val = value.ok_or(SynthesisError::AssignmentMissing)?;
            let mut f = F::ZERO;
            let mut power = F::ONE;
            for i in 0..num_bits {
                if (val >> i) & 1 == 1 {
                    f += power;
                }
                power.double_in_place();
            }
            Ok(f)
        })?;

        let mut bit_vars = Vec::with_capacity(num_bits);
        for i in 0..num_bits {
            let b = cs.new_witness_variable(|| {
                let val = value.ok_or(SynthesisError::AssignmentMissing)?;
                Ok(if (val >> i) & 1 == 1 { F::ONE } else { F::ZERO })
            })?;
            bit_vars.push(b);
        }

        let mut recon_minus_v = lc!() - v;
        let mut coeff = F::ONE;
        for &b in &bit_vars {
            recon_minus_v = recon_minus_v + (coeff, b);
            coeff.double_in_place();
        }
        let zero_lc = lc!() + v - v;
        cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;

        for &b in &bit_vars {
            cs.enforce_sr1cs_constraint(|| lc!() + b, || lc!() + b)?;
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Timing helpers
// ---------------------------------------------------------------------------

fn median(times: &mut Vec<f64>) -> f64 {
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = times.len();
    if n % 2 == 0 {
        (times[n / 2 - 1] + times[n / 2]) / 2.0
    } else {
        times[n / 2]
    }
}

fn bench_mul_circuit<E: Pairing>(num_constraints: usize, iterations: usize)
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E::ScalarField: Field + From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let a_val = E::ScalarField::rand(&mut rng);
    let b_val = E::ScalarField::rand(&mut rng);
    let c_val = a_val * b_val;

    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        num_constraints,
    };

    // Keygen
    let mut keygen_times = Vec::with_capacity(iterations);
    let mut pk = None;
    let mut vk = None;
    for _ in 0..iterations {
        let start = Instant::now();
        let (p, v) = Pari::<E>::keygen(circuit.clone(), 1, &mut rng);
        keygen_times.push(start.elapsed().as_secs_f64() * 1000.0);
        pk = Some(p);
        vk = Some(v);
    }
    let pk = pk.unwrap();
    let vk = vk.unwrap();

    // Prove
    let mut prove_times = Vec::with_capacity(iterations);
    let mut proof = None;
    for _ in 0..iterations {
        let start = Instant::now();
        let p = Pari::<E>::prove(circuit.clone(), &pk, &mut rng).unwrap();
        prove_times.push(start.elapsed().as_secs_f64() * 1000.0);
        proof = Some(p);
    }
    let proof = proof.unwrap();

    // Verify
    let verify_iterations = iterations * 10;
    let mut verify_times = Vec::with_capacity(verify_iterations);
    for _ in 0..verify_iterations {
        let start = Instant::now();
        assert!(Pari::<E>::verify(&proof, &vk, &[c_val]));
        verify_times.push(start.elapsed().as_secs_f64() * 1000.0);
    }

    let cs = Pari::<E>::circuit_to_keygen_cs::<MulCircuit<E::ScalarField>>(circuit).unwrap();

    println!(
        "  R1CS MulCircuit  | {:>6} constraints | keygen {:>8.3} ms | prove {:>8.3} ms | verify {:>8.3} ms",
        cs.num_constraints(),
        median(&mut keygen_times),
        median(&mut prove_times),
        median(&mut verify_times),
    );
}

fn bench_range_proof<E: Pairing>(num_bits: usize, iterations: usize)
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E::ScalarField: Field + From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let value: u64 = 0xDEAD_BEEF_CAFE_BABE;

    let circuit = RangeProofCircuit {
        value: Some(value),
        num_bits,
    };

    // Keygen
    let mut keygen_times = Vec::with_capacity(iterations);
    let mut pk = None;
    let mut vk = None;
    for _ in 0..iterations {
        let start = Instant::now();
        let (p, v) = Pari::<E>::keygen(circuit.clone(), 1, &mut rng);
        keygen_times.push(start.elapsed().as_secs_f64() * 1000.0);
        pk = Some(p);
        vk = Some(v);
    }
    let pk = pk.unwrap();
    let vk = vk.unwrap();

    // Prove
    let mut prove_times = Vec::with_capacity(iterations);
    let mut proof = None;
    for _ in 0..iterations {
        let start = Instant::now();
        let p = Pari::<E>::prove(circuit.clone(), &pk, &mut rng).unwrap();
        prove_times.push(start.elapsed().as_secs_f64() * 1000.0);
        proof = Some(p);
    }
    let proof = proof.unwrap();

    // Verify
    let verify_iterations = iterations * 10;
    let mut verify_times = Vec::with_capacity(verify_iterations);
    for _ in 0..verify_iterations {
        let start = Instant::now();
        assert!(Pari::<E>::verify(&proof, &vk, &[]));
        verify_times.push(start.elapsed().as_secs_f64() * 1000.0);
    }

    let cs = Pari::<E>::circuit_to_keygen_cs::<RangeProofCircuit>(circuit).unwrap();

    println!(
        "  SR1CS RangeProof | {:>6} constraints | keygen {:>8.3} ms | prove {:>8.3} ms | verify {:>8.3} ms",
        cs.num_constraints(),
        median(&mut keygen_times),
        median(&mut prove_times),
        median(&mut verify_times),
    );
}

fn bench_suite<E: Pairing>(curve_name: &str, iterations: usize)
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E::ScalarField: Field + From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    println!("=== Pari ZK-SNARK Benchmarks ({}, median of {} runs) ===\n", curve_name, iterations);

    println!("--- Small circuits ---");
    bench_mul_circuit::<E>(6, iterations);
    bench_range_proof::<E>(8, iterations);
    bench_range_proof::<E>(16, iterations);
    bench_range_proof::<E>(32, iterations);
    bench_range_proof::<E>(64, iterations);

    println!("\n--- Scaling R1CS MulCircuit ---");
    for &nc in &[16, 64, 256, 1024] {
        bench_mul_circuit::<E>(nc, iterations);
    }

    println!();
}

fn main() {
    use ark_bls12_381::Bls12_381;

    let iterations = 10;

    // Warmup run (discarded) to avoid cold-cache bias
    bench_mul_circuit::<Bls12_381>(6, 2);
    bench_mul_circuit::<Bn254>(6, 2);
    println!("(warmup complete)\n");

    bench_suite::<Bn254>("BN254", iterations);
    bench_suite::<Bls12_381>("BLS12-381", iterations);
}
