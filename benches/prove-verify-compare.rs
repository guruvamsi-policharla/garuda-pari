//! Prove/verify timing for ZK-Pari over a repeated-multiplication circuit.
//! Output format matches the non-ZK counterpart (batch-verify branch) for
//! side-by-side comparison.

use ark_bls12_381::Bls12_381;
use ark_ff::Field;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_relations::lc;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::{test_rng, UniformRand};
use std::time::Instant;
use zkpari::{Uncommitted, ZkPari};

type E = Bls12_381;
type Fr = ark_bls12_381::Fr;

#[derive(Clone)]
struct RepeatedMulCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    num_constraints: usize,
}

impl<F: Field> ConstraintSynthesizer<F> for RepeatedMulCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut v = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            v *= &self.b.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(v)
        })?;
        for _ in 0..self.num_constraints {
            cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        }
        Ok(())
    }
}

fn main() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    println!("variant,r1cs_constraints,keygen_ms,prove_ms,verify_ms");
    for num_constraints in [1024usize, 16384, 131072] {
        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let circuit = RepeatedMulCircuit {
            a: Some(a),
            b: Some(b),
            num_constraints,
        };

        let start = Instant::now();
        let (pk, vk) = ZkPari::<E>::keygen(Uncommitted(circuit.clone()), &mut rng);
        let keygen_ms = start.elapsed().as_secs_f64() * 1000.0;

        let prove_iters = if num_constraints >= 100_000 { 3 } else { 10 };
        let start = Instant::now();
        let mut proof = None;
        for _ in 0..prove_iters {
            proof = Some(ZkPari::<E>::prove(Uncommitted(circuit.clone()), &pk, &mut rng).unwrap());
        }
        let prove_ms = start.elapsed().as_secs_f64() * 1000.0 / prove_iters as f64;
        let proof = proof.unwrap();

        let verify_iters = 200;
        let public_input = [a * b];
        let start = Instant::now();
        for _ in 0..verify_iters {
            assert!(ZkPari::<E>::verify(&proof, &vk, &public_input));
        }
        let verify_ms = start.elapsed().as_secs_f64() * 1000.0 / verify_iters as f64;

        println!("zk,{num_constraints},{keygen_ms:.1},{prove_ms:.2},{verify_ms:.3}");
    }
}
