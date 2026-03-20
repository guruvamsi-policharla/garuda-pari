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

fn bench_parallel_batch_verify<E: Pairing>()
where
    E::G1Affine: Neg<Output = E::G1Affine>,
    E::ScalarField: Field + std::convert::From<i32>,
    E::BaseField: PrimeField,
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    let num_threads: usize = std::env::var("NUM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        });

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let a_val = E::ScalarField::rand(&mut rng);
    let b_val = E::ScalarField::rand(&mut rng);
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
    };
    let (pk, vk) = Pari::<E>::keygen(circuit, &mut rng);

    let per_thread_sizes = [2, 32, 512, 8192, 65536];
    let max_chunk = *per_thread_sizes.iter().max().unwrap();

    println!("Threads: {}", num_threads);
    println!("Generating {} proofs (one chunk, cloned to {} threads)...", max_chunk, num_threads);
    let start = Instant::now();
    let mut base_chunk = Vec::with_capacity(max_chunk);
    for _ in 0..max_chunk {
        let a = E::ScalarField::rand(&mut rng);
        let b = E::ScalarField::rand(&mut rng);
        let circuit = MulCircuit {
            a: Some(a),
            b: Some(b),
        };
        let proof = Pari::prove(circuit, &pk).unwrap();
        base_chunk.push((proof, vec![a * b]));
    }
    println!(
        "Generated {} proofs in {:.1} s\n",
        max_chunk,
        start.elapsed().as_secs_f64()
    );

    println!(
        "{:<10} {:>15} {:>15} {:>10}",
        "N (total)", "Individual", "Parallel Batch", "Speedup"
    );
    println!("{:-<58}", "");

    for &per_thread in &per_thread_sizes {
        let total_n = per_thread * num_threads;
        let chunk = &base_chunk[..per_thread];

        // Individual verification (single-threaded, total_n proofs)
        let start = Instant::now();
        for (proof, input) in chunk.iter().cycle().take(total_n) {
            assert!(Pari::<E>::verify(proof, &vk, input));
        }
        let individual = start.elapsed();

        // Parallel batch verification: each thread verifies its chunk
        let start = Instant::now();
        std::thread::scope(|s| {
            let vk_ref = &vk;
            let handles: Vec<_> = (0..num_threads)
                .map(|i| {
                    s.spawn(move || {
                        let mut thread_rng =
                            ark_std::rand::rngs::StdRng::seed_from_u64(42 + i as u64);
                        Pari::<E>::batch_verify(chunk, vk_ref, &mut thread_rng)
                    })
                })
                .collect();
            assert!(handles.into_iter().all(|h| h.join().unwrap()));
        });
        let parallel_batch = start.elapsed();

        let speedup = individual.as_secs_f64() / parallel_batch.as_secs_f64();
        println!(
            "{:<10} {:>12.3} ms {:>12.3} ms {:>9.2}x",
            total_n,
            individual.as_secs_f64() * 1000.0,
            parallel_batch.as_secs_f64() * 1000.0,
            speedup,
        );
    }
}

fn main() {
    bench_parallel_batch_verify::<Bn254>();
}
