#[cfg(test)]
use ark_bn254::Bn254;
use crate::{
    data_structures::{Proof, ProvingKey, VerifyingKey},
    Pari,
};
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ec::AdditiveGroup;
use ark_ff::PrimeField;
use ark_ff::{Field, UniformRand};
use ark_relations::gr1cs::{
    predicate::{polynomial_constraint::SR1CS_PREDICATE_LABEL, PredicateConstraintSystem},
    ConstraintSystemRef, R1CS_PREDICATE_LABEL,
};
use ark_relations::{
    gr1cs::{ConstraintSynthesizer, SynthesisError},
    lc,
};
use ark_std::ops::Neg;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;

#[test]
fn run_test() {
    let _ = test_circuit::<Bn254>(1);
}

#[test]
fn run_test_split_zero() {
    let _ = test_circuit::<Bn254>(0);
}

#[test]
fn run_batch_test() {
    let _ = test_batch_circuit::<Bn254>(1);
}

/// Verify that with witness_split=1 the first witness variable (a_val)
/// lands in the sigma_1 / Pedersen partition, not a constant or outlining copy.
#[test]
fn witness_split_targets_user_witness() {
    type E = Bn254;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    let a_val = <E as Pairing>::ScalarField::from(1234567u64);
    let b_val = <E as Pairing>::ScalarField::from(7654321u64);
    let c_val = a_val * b_val;
    let circuit = Circuit1 {
        a: Some(a_val),
        b: Some(b_val),
    };

    // Inspect the post-outlining witness assignment
    let cs = Pari::<E>::circuit_to_prover_cs(circuit.clone()).unwrap();
    let witness = &cs.assignments.witness_assignment;
    let instance = &cs.assignments.instance_assignment;

    // instance[0] is always the constant 1, instance[1..] are public inputs
    assert_eq!(instance[0], <E as Pairing>::ScalarField::from(1u64));
    assert_eq!(instance[1], c_val);

    // The first two witness variables should be a and b (user-allocated witnesses),
    // not outlining copies of instance variables.
    assert_eq!(
        witness[0], a_val,
        "witness[0] should be a_val (the first user witness), \
         but got something else -- witness_split=1 would NOT target the right variable"
    );
    assert_eq!(witness[1], b_val, "witness[1] should be b_val");

    // With witness_split=1, sigma_1 commits exactly witness[0] = a_val
    let witness_split = 1usize;
    let (pk, vk) = Pari::<E>::keygen(circuit.clone(), witness_split, &mut rng);
    assert_eq!(
        pk.sigma_1.len(),
        1,
        "sigma_1 should have exactly 1 element for witness_split=1"
    );
    assert_eq!(
        pk.sigma_2.len(),
        witness.len() - witness_split,
        "sigma_2 should cover the remaining witness variables"
    );

    // Prove and verify to confirm the full protocol works
    let proof = Pari::<E>::prove(circuit, &pk, &mut rng).unwrap();
    assert!(Pari::<E>::verify(&proof, &vk, &[c_val]));
}

fn test_circuit<E: Pairing>(witness_split: usize)
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
    let (pk, vk): (ProvingKey<E>, VerifyingKey<E>) =
        Pari::<E>::keygen(circuit.clone(), witness_split, &mut rng);
    let proof: Proof<E> = Pari::prove(circuit.clone(), &pk, &mut rng).unwrap();
    let input_assignment = [a_val * b_val];
    assert!(Pari::<E>::verify(&proof, &vk, &input_assignment));
}

#[derive(Clone)]
struct Circuit1<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

fn test_batch_circuit<E: Pairing>(witness_split: usize)
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
    let (pk, vk): (ProvingKey<E>, VerifyingKey<E>) =
        Pari::<E>::keygen(circuit.clone(), witness_split, &mut rng);

    let n = 4;
    let mut proofs_and_inputs = Vec::with_capacity(n);
    for _ in 0..n {
        let a = E::ScalarField::rand(&mut rng);
        let b = E::ScalarField::rand(&mut rng);
        let circuit = Circuit1 {
            a: Some(a),
            b: Some(b),
        };
        let proof: Proof<E> = Pari::prove(circuit, &pk, &mut rng).unwrap();
        let input = vec![a * b];
        proofs_and_inputs.push((proof, input));
    }

    assert!(Pari::<E>::batch_verify(&proofs_and_inputs, &vk, &mut rng));
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

/// Range proof circuit: proves the first witness value is in [0, 2^64).
///
/// Uses native SR1CS constraints (no R1CS-to-SR1CS conversion overhead):
///   - 64 boolean constraints: b_i^2 = b_i
///   - 1 reconstruction constraint: (sum(b_i * 2^i) - v)^2 = 0
///
/// This halves the constraint count compared to R1CS-based boolean checks.
///
/// NOTE: We avoid two arkworks `new_lc_add_helper` shortcuts that break
/// instance outlining for native SR1CS constraints:
///   1. A single-term LC with coeff=1 is returned as the raw Variable
///      (bypasses lc_map, so outlining never replaces Variable::One).
///   2. An empty LC aliases to `symbolic_lc(0)`, colliding with the first
///      real LC in the map.
/// We work around (1) by using `b^2 = b` (no Variable::One in any
/// single-term position) and (2) by expressing the zero RHS as `v - v`.
#[derive(Clone)]
struct RangeProofCircuit {
    value: Option<u64>,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for RangeProofCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let value = self.value;

        let v = cs.new_witness_variable(|| {
            let val = value.ok_or(SynthesisError::AssignmentMissing)?;
            let mut f = ConstraintF::ZERO;
            let mut power = ConstraintF::ONE;
            for i in 0..64u32 {
                if (val >> i) & 1 == 1 {
                    f += power;
                }
                power.double_in_place();
            }
            Ok(f)
        })?;

        let mut bit_vars = Vec::with_capacity(64);
        for i in 0..64u32 {
            let b = cs.new_witness_variable(|| {
                let val = value.ok_or(SynthesisError::AssignmentMissing)?;
                Ok(if (val >> i) & 1 == 1 {
                    ConstraintF::ONE
                } else {
                    ConstraintF::ZERO
                })
            })?;
            bit_vars.push(b);
        }

        // (sum(b_i * 2^i) - v)^2 = 0, using `v - v` for the zero RHS
        // to avoid the empty-LC → symbolic_lc(0) aliasing bug.
        let mut recon_minus_v = lc!() - v;
        let mut coeff = ConstraintF::ONE;
        for &b in &bit_vars {
            recon_minus_v = recon_minus_v + (coeff, b);
            coeff.double_in_place();
        }
        let zero_lc = lc!() + v - v;
        cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;

        // b_i^2 = b_i (native SR1CS boolean check)
        for &b in &bit_vars {
            cs.enforce_sr1cs_constraint(|| lc!() + b, || lc!() + b)?;
        }

        Ok(())
    }
}

/// Native SR1CS test: boolean constraint b^2 = b
#[test]
fn native_sr1cs_boolean_test() {
    type E = Bn254;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    #[derive(Clone)]
    struct BoolCircuit;

    impl<F: Field> ConstraintSynthesizer<F> for BoolCircuit {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<F>,
        ) -> Result<(), SynthesisError> {
            cs.remove_predicate(R1CS_PREDICATE_LABEL);
            let _ = cs.register_predicate(
                SR1CS_PREDICATE_LABEL,
                PredicateConstraintSystem::new_sr1cs_predicate()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
            );
            let b = cs.new_witness_variable(|| Ok(F::ONE))?;
            cs.enforce_sr1cs_constraint(|| lc!() + b, || lc!() + b)?;
            Ok(())
        }
    }

    let (pk, vk) = Pari::<E>::keygen(BoolCircuit, 0, &mut rng);
    let proof = Pari::<E>::prove(BoolCircuit, &pk, &mut rng).unwrap();
    assert!(Pari::<E>::verify(&proof, &vk, &[]));
}

#[test]
fn range_proof_test() {
    type E = Bn254;
    type Fr = <E as Pairing>::ScalarField;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    let value: u64 = 0xDEAD_BEEF_CAFE_BABE;
    let circuit = RangeProofCircuit {
        value: Some(value),
    };

    let cs = Pari::<E>::circuit_to_prover_cs(circuit.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap(), "constraint system must be satisfied");
    let witness = &cs.assignments.witness_assignment;

    // Native SR1CS: 65 user witnesses + 1 outlining copy = 66 total
    // (no SR1CS conversion overhead -- halved from 131)
    assert_eq!(witness.len(), 66, "native SR1CS should yield 66 witness vars");
    assert_eq!(cs.num_constraints(), 66, "65 user + 1 outlining constraint");

    let value_as_field: Fr = {
        let mut f = Fr::ZERO;
        let mut power = Fr::ONE;
        for i in 0..64u32 {
            if (value >> i) & 1 == 1 {
                f += power;
            }
            power.double_in_place();
        }
        f
    };

    assert_eq!(
        witness[0], value_as_field,
        "witness[0] must be the range-proved value (committed via sigma_1)"
    );

    for i in 0..64usize {
        let expected_bit = if (value >> i) & 1 == 1 { Fr::ONE } else { Fr::ZERO };
        assert_eq!(witness[1 + i], expected_bit, "bit {i} mismatch");
    }

    // witness_split=1: value -> sigma_1 (Pedersen), bits + outlining -> sigma_2
    let (pk, vk) = Pari::<E>::keygen(circuit.clone(), 1, &mut rng);
    assert_eq!(pk.sigma_1.len(), 1, "sigma_1 should commit exactly the value");
    assert_eq!(pk.sigma_2.len(), witness.len() - 1);

    let proof = Pari::<E>::prove(circuit, &pk, &mut rng).unwrap();
    assert!(Pari::<E>::verify(&proof, &vk, &[]));
}
