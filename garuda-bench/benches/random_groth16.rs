use ark_bls12_381::Bls12_381;
use ark_crypto_primitives::snark::CircuitSpecificSetupSNARK;
use ark_crypto_primitives::snark::SNARK;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, PrimeField};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError, Variable,
};
use ark_relations::lc;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_std::{
    rand::RngCore,
    rand::{rngs::StdRng, Rng, SeedableRng},
    test_rng,
};
use garuda_bench::prover_prep;
use garuda_bench::RandomCircuit;
use shared_utils::BenchResult;
use std::any::type_name;
use std::time::Duration;

fn bench<E: Pairing>(
    num_constraints: usize,
    nonzero_per_constraint: usize,
    num_keygen_iterations: u32,
    num_prover_iterations: u32,
    num_verifier_iterations: u32,
    num_thread: usize,
) -> BenchResult
where
    E::ScalarField: PrimeField + UniformRand,
{
    let mut rng = StdRng::seed_from_u64(test_rng().next_u64());
    let circuit =
        RandomCircuit::<E::ScalarField>::new(num_constraints, nonzero_per_constraint, false);
    let mut prover_time = Duration::new(0, 0);
    let mut keygen_time = Duration::new(0, 0);
    let mut verifier_time = Duration::new(0, 0);
    let mut prover_prep_time = Duration::new(0, 0);
    let (mut pk, mut vk) = (None, None);

    for _ in 0..num_keygen_iterations {
        let setup_circuit = circuit.clone();

        let start = ark_std::time::Instant::now();
        let (ipk, ivk) = Groth16::<E>::setup(setup_circuit, &mut rng).unwrap();
        pk = Some(ipk);
        vk = Some(ivk);
        keygen_time += start.elapsed();
    }

    let pk_size = pk
        .as_ref()
        .unwrap()
        .serialized_size(ark_serialize::Compress::Yes);
    let vk_size = vk
        .as_ref()
        .unwrap()
        .serialized_size(ark_serialize::Compress::Yes);

    let pvk = prepare_verifying_key(vk.as_ref().unwrap());

    let mut proof = None;

    let start = ark_std::time::Instant::now();
    prover_prep::<E, RandomCircuit<E::ScalarField>>(circuit.clone());
    prover_prep_time += start.elapsed();

    for _ in 0..num_prover_iterations {
        let prover_circuit = circuit.clone();

        let start = ark_std::time::Instant::now();
        proof = pk
            .as_ref()
            .map(|pk| Groth16::<E>::create_proof_with_reduction_no_zk(prover_circuit, pk).unwrap());
        prover_time += start.elapsed();
    }

    let proof_size = proof
        .as_ref()
        .unwrap()
        .serialized_size(ark_serialize::Compress::Yes);

    let start = ark_std::time::Instant::now();
    for _ in 0..num_verifier_iterations {
        assert!(
            Groth16::<E>::verify_with_processed_vk(&pvk, &[], proof.as_ref().unwrap()).unwrap()
        );
    }
    verifier_time += start.elapsed();

    let cs: ConstraintSystemRef<E::ScalarField> = ConstraintSystem::new_ref();
    let _ = circuit.clone().generate_constraints(cs.clone());
    cs.finalize();

    BenchResult {
        curve: type_name::<E>().to_string(),
        // Reuse the `input_size` and `num_invocations` fields to log the requested knobs.
        input_size: cs.num_instance_variables(),
        num_invocations: num_constraints,
        num_nonzero_entries: nonzero_per_constraint,
        num_constraints: cs.num_constraints(),
        predicate_constraints: cs.get_all_predicates_num_constraints(),
        num_thread,
        num_keygen_iterations: num_keygen_iterations as usize,
        num_prover_iterations: num_prover_iterations as usize,
        num_verifier_iterations: num_verifier_iterations as usize,
        pk_size,
        vk_size,
        proof_size,
        prover_time: (prover_time / num_prover_iterations),
        prover_prep_time,
        prover_corrected_time: (prover_time - prover_prep_time) / num_prover_iterations,
        verifier_time: (verifier_time / num_verifier_iterations),
        keygen_time: (keygen_time / num_keygen_iterations),
        keygen_prep_time: Duration::new(0, 0),
        keygen_corrected_time: (keygen_time / num_keygen_iterations),
    }
}

const MIN_LOG2_CONSTRAINTS: usize = 10;
const MAX_LOG2_CONSTRAINTS: usize = 15;
const NUM_KEYGEN_ITERATIONS: u32 = 1;
const NUM_PROVER_ITERATIONS: u32 = 1;
const NUM_VERIFIER_ITERATIONS: u32 = 1;

fn main() {
    let bench_num_constraints = (MIN_LOG2_CONSTRAINTS..=MAX_LOG2_CONSTRAINTS)
        .map(|i| 1 << i)
        .collect::<Vec<usize>>();
    for num_constraints in bench_num_constraints {
        let filename = format!("random-groth16-{}t.csv", 1);
        let _ = bench::<Bls12_381>(
            num_constraints,
            3,
            NUM_KEYGEN_ITERATIONS,
            NUM_PROVER_ITERATIONS,
            NUM_VERIFIER_ITERATIONS,
            1,
        )
        .save_to_csv(&filename);
    }
}
