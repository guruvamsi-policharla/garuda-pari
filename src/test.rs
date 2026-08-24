use crate::data_structures::{CommittedInputOpening, Proof, ProvingKey, VerifyingKey};
use crate::{Uncommitted, ZkPari, ZkPariCircuit};
use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, UniformRand};
use ark_relations::gr1cs::{
    predicate::{polynomial_constraint::SR1CS_PREDICATE_LABEL, PredicateConstraintSystem},
    ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable, R1CS_PREDICATE_LABEL,
};
use ark_relations::lc;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;
use ark_std::Zero;

type E = Bls12_381;
type Fr = <Bls12_381 as Pairing>::ScalarField;

// ---------------------------------------------------------------------------
// Test circuits
// ---------------------------------------------------------------------------

/// Which committed-input blocks the multiplication circuit declares.
#[derive(Clone, Copy)]
enum CommitSpec {
    /// No committed inputs.
    None,
    /// One block: [a].
    A,
    /// One block: [a, b].
    BlockAb,
    /// Two blocks: [a] and [b].
    BlocksAThenB,
}

/// a * b = c with c public (R1CS, converted to SR1CS by the adapter).
#[derive(Clone)]
struct MulCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    spec: CommitSpec,
}

impl<F: Field> MulCircuit<F> {
    fn synthesize_constraints(
        &self,
        cs: &ConstraintSystemRef<F>,
    ) -> Result<(Variable, Variable), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            a *= &b;
            Ok(a)
        })?;

        for _ in 0..6 {
            cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + b, || lc!() + c)?;
        }
        Ok((a, b))
    }
}

impl<F: Field> ZkPariCircuit<F> for MulCircuit<F> {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        let (a, b) = self.synthesize_constraints(&cs)?;
        Ok(match self.spec {
            CommitSpec::None => vec![],
            CommitSpec::A => vec![vec![a]],
            CommitSpec::BlockAb => vec![vec![a, b]],
            CommitSpec::BlocksAThenB => vec![vec![a], vec![b]],
        })
    }
}

impl<F: Field> ConstraintSynthesizer<F> for MulCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let _ = self.synthesize_constraints(&cs)?;
        Ok(())
    }
}

/// Range proof circuit: proves `value` is in [0, 2^64), declaring the value
/// as a single committed input.
///
/// Uses native SR1CS constraints. If `value_allocated_last` is set, the 64
/// bit variables are allocated *before* the value — exercising that committed
/// inputs may live anywhere in the witness, not just at the front.
#[derive(Clone)]
struct RangeProofCircuit {
    value: Option<u64>,
    value_allocated_last: bool,
}

impl<F: Field> ZkPariCircuit<F> for RangeProofCircuit {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let value = self.value;
        let alloc_value = |cs: &ConstraintSystemRef<F>| {
            cs.new_witness_variable(|| {
                let val = value.ok_or(SynthesisError::AssignmentMissing)?;
                Ok(F::from(val))
            })
        };
        let alloc_bits = |cs: &ConstraintSystemRef<F>| -> Result<Vec<Variable>, SynthesisError> {
            (0..64u32)
                .map(|i| {
                    cs.new_witness_variable(|| {
                        let val = value.ok_or(SynthesisError::AssignmentMissing)?;
                        Ok(if (val >> i) & 1 == 1 { F::ONE } else { F::ZERO })
                    })
                })
                .collect()
        };

        let (v, bit_vars) = if self.value_allocated_last {
            let bits = alloc_bits(&cs)?;
            (alloc_value(&cs)?, bits)
        } else {
            let v = alloc_value(&cs)?;
            (v, alloc_bits(&cs)?)
        };

        // (sum(b_i * 2^i) - v)^2 = 0, using `v - v` for the zero RHS
        // to avoid the empty-LC -> symbolic_lc(0) aliasing bug.
        let mut recon_minus_v = lc!() - v;
        let mut coeff = F::ONE;
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

        Ok(vec![vec![v]])
    }
}

/// Batched range circuit for one-to-many transfers: range-checks `B` claimed
/// amounts plus the remaining balance (block 1, size B+1) and enforces the
/// theta-aggregation `sum_i theta^{i-1} v^_i + theta^B v^_rem = v_theta`
/// against the block-2 committed aggregate, with `theta` a public input.
#[derive(Clone)]
struct BatchedRangeCircuit<F: Field> {
    theta: Option<F>,
    amounts: Option<Vec<u64>>,
    remaining: Option<u64>,
    batch_size: usize,
}

impl<F: Field> ZkPariCircuit<F> for BatchedRangeCircuit<F> {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );

        let b = self.batch_size;
        let theta = self.theta;

        // Committed values: the B claimed amounts followed by the remaining balance
        let raw_values: Option<Vec<u64>> = match (self.amounts.as_ref(), self.remaining) {
            (Some(amounts), Some(remaining)) => {
                assert_eq!(amounts.len(), b);
                Some(amounts.iter().copied().chain([remaining]).collect())
            }
            _ => None,
        };
        let values: Option<Vec<F>> = raw_values
            .as_ref()
            .map(|raw| raw.iter().map(|v| F::from(*v)).collect());

        // Block 1: v^_1, ..., v^_B, v^_rem
        let mut value_vars = Vec::with_capacity(b + 1);
        for i in 0..=b {
            let vals = values.clone();
            let v = cs.new_witness_variable(move || {
                vals.ok_or(SynthesisError::AssignmentMissing).map(|v| v[i])
            })?;
            value_vars.push(v);
        }

        // Block 2: v_theta = sum_i theta^i * values[i]
        let v_theta_value: Option<F> = match (values.as_ref(), theta) {
            (Some(vals), Some(th)) => {
                let mut acc = vals[b];
                for v in vals[..b].iter().rev() {
                    acc = acc * th + v;
                }
                Some(acc)
            }
            _ => None,
        };
        let v_theta_var =
            cs.new_witness_variable(|| v_theta_value.ok_or(SynthesisError::AssignmentMissing))?;

        // theta is an ordinary public input (chosen after the ledger
        // commitments and the block-1 commitment are fixed)
        let theta_var = cs.new_input_variable(|| theta.ok_or(SynthesisError::AssignmentMissing))?;

        // 64-bit range check for every committed value
        for (i, &v) in value_vars.iter().enumerate() {
            let mut bit_vars = Vec::with_capacity(64);
            for bit in 0..64u32 {
                let raw = raw_values.clone();
                let bv = cs.new_witness_variable(move || {
                    let raw = raw.ok_or(SynthesisError::AssignmentMissing)?;
                    Ok(if (raw[i] >> bit) & 1 == 1 {
                        F::ONE
                    } else {
                        F::ZERO
                    })
                })?;
                bit_vars.push(bv);
            }
            let mut recon_minus_v = lc!() - v;
            let mut coeff = F::ONE;
            for &bv in &bit_vars {
                recon_minus_v = recon_minus_v + (coeff, bv);
                coeff.double_in_place();
            }
            let zero_lc = lc!() + v - v;
            cs.enforce_sr1cs_constraint(|| recon_minus_v, || zero_lc)?;
            for &bv in &bit_vars {
                cs.enforce_sr1cs_constraint(|| lc!() + bv, || lc!() + bv)?;
            }
        }

        // Horner aggregation: acc = v^_rem; acc = acc * theta + v^_i for i = B..1
        // Each product acc * theta is enforced with two squares:
        //   (acc + theta)^2 = s_plus,  (acc - theta)^2 = s_minus,
        //   acc * theta = (s_plus - s_minus)/4
        let quarter = F::from(4u64).inverse().unwrap();
        let mut acc_lc = lc!() + value_vars[b];
        let mut acc_val: Option<F> = values.as_ref().map(|vals| vals[b]);
        for i in (0..b).rev() {
            let (av, th) = (acc_val, theta);
            let s_plus = cs.new_witness_variable(move || {
                let a = av.ok_or(SynthesisError::AssignmentMissing)?;
                let t = th.ok_or(SynthesisError::AssignmentMissing)?;
                Ok((a + t).square())
            })?;
            let s_minus = cs.new_witness_variable(move || {
                let a = av.ok_or(SynthesisError::AssignmentMissing)?;
                let t = th.ok_or(SynthesisError::AssignmentMissing)?;
                Ok((a - t).square())
            })?;
            let lhs_plus = acc_lc.clone() + theta_var;
            let lhs_minus = acc_lc.clone() - theta_var;
            cs.enforce_sr1cs_constraint(|| lhs_plus, || lc!() + s_plus)?;
            cs.enforce_sr1cs_constraint(|| lhs_minus, || lc!() + s_minus)?;
            acc_lc = lc!() + (quarter, s_plus) + (-quarter, s_minus) + value_vars[i];
            acc_val = match (acc_val, theta, values.as_ref()) {
                (Some(a), Some(t), Some(vals)) => Some(a * t + vals[i]),
                _ => None,
            };
        }

        // (acc - v_theta)^2 = 0
        let final_lhs = acc_lc - v_theta_var;
        let zero_lc = lc!() + value_vars[0] - value_vars[0];
        cs.enforce_sr1cs_constraint(|| final_lhs, || zero_lc)?;

        Ok(vec![value_vars, vec![v_theta_var]])
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

fn rng() -> ark_std::rand::rngs::StdRng {
    ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64())
}

fn roundtrip(spec: CommitSpec, expected_blocks: usize) {
    let mut rng = rng();
    let a_val = Fr::rand(&mut rng);
    let b_val = Fr::rand(&mut rng);
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec,
    };
    let (pk, vk): (ProvingKey<E>, VerifyingKey<E>) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let proof: Proof<E> = ZkPari::prove(circuit, &pk, &mut rng).unwrap();
    assert_eq!(proof.c_ci.len(), expected_blocks);
    assert!(ZkPari::<E>::verify(&proof, &vk, &[a_val * b_val]));
    // Wrong public input must be rejected
    assert!(!ZkPari::<E>::verify(
        &proof,
        &vk,
        &[a_val * b_val + Fr::ONE]
    ));
}

#[test]
fn roundtrip_no_committed_inputs() {
    roundtrip(CommitSpec::None, 0);
}

#[test]
fn roundtrip_one_committed_input() {
    roundtrip(CommitSpec::A, 1);
}

#[test]
fn roundtrip_one_block_of_two() {
    roundtrip(CommitSpec::BlockAb, 1);
}

#[test]
fn roundtrip_two_blocks() {
    roundtrip(CommitSpec::BlocksAThenB, 2);
}

/// Plain arkworks circuits work through the `Uncommitted` wrapper.
#[test]
fn roundtrip_uncommitted_wrapper() {
    let mut rng = rng();
    let a_val = Fr::rand(&mut rng);
    let b_val = Fr::rand(&mut rng);
    let circuit = Uncommitted(MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::None,
    });
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let proof = ZkPari::<E>::prove(circuit, &pk, &mut rng).unwrap();
    assert!(proof.c_ci.is_empty());
    assert!(ZkPari::<E>::verify(&proof, &vk, &[a_val * b_val]));
}

/// The committed-input commitments in the proof must match externally
/// computed Pedersen commitments with the same openings, for both a single
/// block of two values and two blocks of one value each.
#[test]
fn committed_input_pedersen_consistency() {
    let mut rng = rng();
    let a_val = Fr::from(1234567u64);
    let b_val = Fr::from(7654321u64);

    // One block of size 2
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::BlockAb,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    assert_eq!(pk.sigma_ci.len(), 1);
    assert_eq!(pk.sigma_ci[0].len(), 2);

    let opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let expected_commitment = pk.pedersen_commit(0, &[a_val, b_val], &opening);

    let proof =
        ZkPari::<E>::prove_with_openings(circuit, &pk, core::slice::from_ref(&opening), &mut rng)
            .unwrap();
    assert_eq!(proof.c_ci[0], expected_commitment);
    assert!(ZkPari::<E>::verify(&proof, &vk, &[a_val * b_val]));

    // Two blocks of size 1, independent openings
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::BlocksAThenB,
    };
    let (pk2, vk2) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let openings = [
        CommittedInputOpening::<Fr>::rand(&mut rng),
        CommittedInputOpening::<Fr>::rand(&mut rng),
    ];
    let proof2 = ZkPari::<E>::prove_with_openings(circuit, &pk2, &openings, &mut rng).unwrap();
    assert_eq!(
        proof2.c_ci[0],
        pk2.pedersen_commit(0, &[a_val], &openings[0])
    );
    assert_eq!(
        proof2.c_ci[1],
        pk2.pedersen_commit(1, &[b_val], &openings[1])
    );
    assert!(ZkPari::<E>::verify(&proof2, &vk2, &[a_val * b_val]));
}

/// A serialized proof must deserialize and verify; verification must reject
/// (not panic on) malformed statements.
#[test]
fn proof_serialization_roundtrip_and_malformed_inputs() {
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

    let mut rng = rng();
    let a_val = Fr::rand(&mut rng);
    let b_val = Fr::rand(&mut rng);
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::A,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let proof = ZkPari::<E>::prove(circuit, &pk, &mut rng).unwrap();

    // Round-trip through the wire format (with validation)
    let mut bytes = Vec::new();
    proof.serialize_compressed(&mut bytes).unwrap();
    let parsed = Proof::<E>::deserialize_compressed(&bytes[..]).unwrap();
    assert_eq!(parsed, proof);
    assert!(ZkPari::<E>::verify(&parsed, &vk, &[a_val * b_val]));

    // Wrong public-input length: rejected, not panicked on
    assert!(!ZkPari::<E>::verify(&proof, &vk, &[]));
    assert!(!ZkPari::<E>::verify(&proof, &vk, &[a_val * b_val, a_val]));
    let batch = vec![(proof.clone(), vec![])];
    assert!(!ZkPari::<E>::batch_verify(&batch, &vk, &mut rng));

    // Wrong number of block commitments: rejected
    let mut truncated = proof.clone();
    truncated.c_ci.clear();
    assert!(!ZkPari::<E>::verify(&truncated, &vk, &[a_val * b_val]));
}

/// Proofs must be randomized: two proofs of the same statement with the same
/// key must differ in every randomized component.
#[test]
fn proofs_are_randomized() {
    let mut rng = rng();
    let a_val = Fr::rand(&mut rng);
    let b_val = Fr::rand(&mut rng);
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::A,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let proof_1 = ZkPari::<E>::prove(circuit.clone(), &pk, &mut rng).unwrap();
    let proof_2 = ZkPari::<E>::prove(circuit, &pk, &mut rng).unwrap();
    assert_ne!(proof_1.c_ci[0], proof_2.c_ci[0]);
    assert_ne!(proof_1.t_g, proof_2.t_g);
    assert_ne!(proof_1.u_g, proof_2.u_g);
    assert_ne!(proof_1.v_a, proof_2.v_a);
    assert!(ZkPari::<E>::verify(&proof_1, &vk, &[a_val * b_val]));
    assert!(ZkPari::<E>::verify(&proof_2, &vk, &[a_val * b_val]));
}

#[test]
fn batch_verify() {
    let mut rng = rng();
    let circuit = MulCircuit {
        a: Some(Fr::rand(&mut rng)),
        b: Some(Fr::rand(&mut rng)),
        spec: CommitSpec::A,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit, &mut rng);

    let n = 4;
    let mut proofs_and_inputs = Vec::with_capacity(n);
    for _ in 0..n {
        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let circuit = MulCircuit {
            a: Some(a),
            b: Some(b),
            spec: CommitSpec::A,
        };
        let proof = ZkPari::<E>::prove(circuit, &pk, &mut rng).unwrap();
        proofs_and_inputs.push((proof, vec![a * b]));
    }
    assert!(ZkPari::<E>::batch_verify(&proofs_and_inputs, &vk, &mut rng));

    // A corrupted proof in the batch must be rejected
    proofs_and_inputs[2].1[0] += Fr::ONE;
    assert!(!ZkPari::<E>::batch_verify(
        &proofs_and_inputs,
        &vk,
        &mut rng
    ));
}

/// Committed inputs may be allocated anywhere in the circuit — here the
/// range-checked value is allocated *after* its 64 bit variables, and the
/// proof still opens the expected Pedersen commitment.
#[test]
fn committed_input_allocation_order_independent() {
    let mut rng = rng();
    let value: u64 = 300;

    for value_allocated_last in [false, true] {
        let keygen_circuit = RangeProofCircuit {
            value: Some(0),
            value_allocated_last,
        };
        let (pk, vk) = ZkPari::<E>::keygen(keygen_circuit, &mut rng);

        let opening = CommittedInputOpening::<Fr>::rand(&mut rng);
        let commitment = pk.pedersen_commit(0, &[Fr::from(value)], &opening);

        let proof = ZkPari::<E>::prove_with_openings(
            RangeProofCircuit {
                value: Some(value),
                value_allocated_last,
            },
            &pk,
            core::slice::from_ref(&opening),
            &mut rng,
        )
        .unwrap();

        assert_eq!(proof.c_ci[0], commitment);
        assert!(ZkPari::<E>::verify(&proof, &vk, &[]));
    }
}

/// R1CS circuit (converted to SR1CS by the adapter) whose declared committed
/// input `a` is allocated *first* but used only *after* `b`: the adapter
/// renumbers witnesses by first use in the constraint matrices, so `a`'s
/// post-conversion index differs from its allocation index. Regression
/// circuit for the committed-input remapping across the conversion.
#[derive(Clone)]
struct LateUseCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    /// Declare a never-constrained witness as the committed input instead of `a`.
    declare_unused: bool,
}

impl<F: Field> ZkPariCircuit<F> for LateUseCircuit<F> {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let unused = cs.new_witness_variable(|| Ok(F::ZERO))?;
        let b_sq = cs.new_input_variable(|| {
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(b.square())
        })?;
        let a_sq = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(a.square())
        })?;

        // b is first-used before a, so the conversion assigns b the lower
        // new witness index
        for _ in 0..3 {
            cs.enforce_r1cs_constraint(|| lc!() + b, || lc!() + b, || lc!() + b_sq)?;
        }
        for _ in 0..3 {
            cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + a, || lc!() + a_sq)?;
        }
        Ok(vec![vec![if self.declare_unused { unused } else { a }]])
    }
}

/// Regression test for the R1CS-to-SR1CS renumbering bug: the proof's
/// committed-input commitment must open to the *declared* variable's value
/// even when the conversion reorders the witness space.
#[test]
fn committed_input_survives_r1cs_conversion_renumbering() {
    let mut rng = rng();
    let a_val = Fr::from(3u64);
    let b_val = Fr::from(5u64);
    let circuit = LateUseCircuit {
        a: Some(a_val),
        b: Some(b_val),
        declare_unused: false,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);

    let opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let proof =
        ZkPari::<E>::prove_with_openings(circuit, &pk, core::slice::from_ref(&opening), &mut rng)
            .unwrap();

    assert_eq!(
        proof.c_ci[0],
        pk.pedersen_commit(0, &[a_val], &opening),
        "C_ci must commit to the declared variable, not whichever witness the \
         conversion renumbered into its slot"
    );
    assert_ne!(
        proof.c_ci[0],
        pk.pedersen_commit(0, &[b_val], &opening),
        "C_ci must not commit to the first-used variable"
    );
    assert!(ZkPari::<E>::verify(
        &proof,
        &vk,
        &[b_val * b_val, a_val * a_val]
    ));
}

/// A committed input that appears in no constraint must be rejected at key
/// generation: on the conversion path it has no column in the converted
/// system at all.
#[test]
#[should_panic(expected = "does not appear in any constraint")]
fn unused_committed_input_rejected_on_conversion_path() {
    let mut rng = rng();
    let circuit = LateUseCircuit {
        a: Some(Fr::from(3u64)),
        b: Some(Fr::from(5u64)),
        declare_unused: true,
    };
    let _ = ZkPari::<E>::keygen(circuit, &mut rng);
}

/// The Pedersen commitments exposed by the proof are additively homomorphic.
#[test]
fn pedersen_commitments_are_homomorphic() {
    let mut rng = rng();
    let (pk, _vk) = ZkPari::<E>::keygen(
        RangeProofCircuit {
            value: Some(0),
            value_allocated_last: false,
        },
        &mut rng,
    );

    let opening_1 = CommittedInputOpening::<Fr>::rand(&mut rng);
    let opening_2 = CommittedInputOpening::<Fr>::rand(&mut rng);
    let com_1 = pk.pedersen_commit(0, &[Fr::from(300u64)], &opening_1);
    let com_2 = pk.pedersen_commit(0, &[Fr::from(400u64)], &opening_2);
    let sum_opening = &opening_1 + &opening_2;
    let expected_sum = pk.pedersen_commit(0, &[Fr::from(700u64)], &sum_opening);
    assert_eq!(
        com_1 + com_2,
        expected_sum,
        "Pedersen commitment homomorphism broken"
    );
}

/// Batched one-to-many transfer: one proof covers B range proofs via two
/// committed-input blocks and a theta-aggregated ledger commitment that the
/// verifier recomputes (and which is never transmitted).
#[test]
fn batched_transfer_theta_aggregation() {
    let mut rng = rng();
    const B: usize = 3;
    let amounts: Vec<u64> = vec![100, 250, 50];
    let balance: u64 = 1000;
    let remaining: u64 = balance - amounts.iter().sum::<u64>();

    // Setup: block 1 holds the B+1 claimed values, block 2 the aggregate
    let setup_circuit = BatchedRangeCircuit::<Fr> {
        theta: None,
        amounts: None,
        remaining: None,
        batch_size: B,
    };
    let (pk, vk) = ZkPari::<E>::keygen(setup_circuit, &mut rng);

    // Ledger commitments in the block-2 payment basis (Sigma_ci_2[0], Gamma_ci_2)
    let r_alice = CommittedInputOpening::<Fr>::rand(&mut rng);
    let com_alice = pk.pedersen_commit(1, &[Fr::from(balance)], &r_alice);
    let r_i: Vec<CommittedInputOpening<Fr>> = (0..B)
        .map(|_| CommittedInputOpening::rand(&mut rng))
        .collect();
    let com_i: Vec<_> = amounts
        .iter()
        .zip(&r_i)
        .map(|(v, r)| pk.pedersen_commit(1, &[Fr::from(*v)], r))
        .collect();

    // Remaining-balance commitment, derived homomorphically from the ledger
    let r_rem = r_i.iter().fold(r_alice.clone(), |acc, r| &acc - r);
    let com_rem: <E as Pairing>::G1Affine = (com_alice.into_group()
        - com_i
            .iter()
            .fold(<E as Pairing>::G1::zero(), |acc, c| acc + c))
    .into_affine();
    assert_eq!(
        com_rem,
        pk.pedersen_commit(1, &[Fr::from(remaining)], &r_rem)
    );

    // Block-1 commitment to the claimed values (sent before theta is drawn)
    let rho_1 = CommittedInputOpening::<Fr>::rand(&mut rng);
    let claimed: Vec<Fr> = amounts
        .iter()
        .map(|v| Fr::from(*v))
        .chain([Fr::from(remaining)])
        .collect();
    let c_ci_1 = pk.pedersen_commit(0, &claimed, &rho_1);

    // theta: bound to (com_alice, com_i, C_ci_1) in a real deployment
    let theta = Fr::rand(&mut rng);

    // Aggregate commitment and opening: com_theta = sum theta^{i-1} com_i + theta^B com_rem
    let mut theta_pow = Fr::ONE;
    let mut com_theta_acc = <E as Pairing>::G1::zero();
    let mut rho_2 = Fr::zero();
    for (com, r) in com_i.iter().zip(&r_i).chain([(&com_rem, &r_rem)]) {
        com_theta_acc += *com * theta_pow;
        rho_2 += r.rho * theta_pow;
        theta_pow *= theta;
    }
    let com_theta: <E as Pairing>::G1Affine = com_theta_acc.into_affine();
    let rho_2 = CommittedInputOpening { rho: rho_2 };

    // One proof for all B+1 range checks plus the aggregation constraint
    let circuit = BatchedRangeCircuit::<Fr> {
        theta: Some(theta),
        amounts: Some(amounts.clone()),
        remaining: Some(remaining),
        batch_size: B,
    };
    let proof = ZkPari::<E>::prove_with_openings(circuit, &pk, &[rho_1, rho_2], &mut rng).unwrap();

    // Block 1 matches the transmitted commitment; block 2 matches the
    // verifier-recomputed aggregate (never transmitted)
    assert_eq!(proof.c_ci[0], c_ci_1);
    assert_eq!(proof.c_ci[1], com_theta);
    assert!(ZkPari::<E>::verify(&proof, &vk, &[theta]));

    // A wrong theta (i.e. inconsistent aggregate) must be rejected
    assert!(!ZkPari::<E>::verify(&proof, &vk, &[theta + Fr::ONE]));
}

// ---------------------------------------------------------------------------
// HVZK simulator (Theorem 1)
// ---------------------------------------------------------------------------

/// The trapdoor simulator forges an accepting transcript for any committed
/// input commitment, with no witness — for a circuit with no public input.
#[test]
fn simulate_accepts_for_range_circuit() {
    let mut rng = rng();
    let (pk, vk, trapdoor) = ZkPari::<E>::keygen_with_trapdoor(
        RangeProofCircuit {
            value: Some(0),
            value_allocated_last: false,
        },
        &mut rng,
    );

    // Bind the simulated proof to an arbitrary public ledger commitment.
    let opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let commitment = pk.pedersen_commit(0, &[Fr::from(123_456u64)], &opening);

    let proof = ZkPari::<E>::simulate(
        &trapdoor,
        &vk,
        core::slice::from_ref(&commitment),
        &[],
        &mut rng,
    );

    assert_eq!(proof.c_ci[0], commitment, "simulator binds the commitment");
    assert!(
        ZkPari::<E>::verify(&proof, &vk, &[]),
        "simulated transcript must verify"
    );
}

/// The simulator also handles nonempty public input (exercising the instance
/// polynomial evaluations at tau and at the challenge).
#[test]
fn simulate_accepts_with_public_input() {
    let mut rng = rng();
    let circuit = MulCircuit {
        a: Some(Fr::from(3u64)),
        b: Some(Fr::from(5u64)),
        spec: CommitSpec::A,
    };
    let (pk, vk, trapdoor) = ZkPari::<E>::keygen_with_trapdoor(circuit, &mut rng);

    let public_input = [Fr::from(15u64)];
    let opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let commitment = pk.pedersen_commit(0, &[Fr::from(3u64)], &opening);

    let proof = ZkPari::<E>::simulate(
        &trapdoor,
        &vk,
        core::slice::from_ref(&commitment),
        &public_input,
        &mut rng,
    );

    assert_eq!(proof.c_ci[0], commitment);
    assert!(ZkPari::<E>::verify(&proof, &vk, &public_input));
    // The challenge binds the public input: verifying under a different
    // instance must fail.
    assert!(!ZkPari::<E>::verify(&proof, &vk, &[Fr::from(16u64)]));
}

/// A simulated proof is bound to its commitment: verifying it as if it opened
/// a different commitment fails.
#[test]
fn simulate_is_bound_to_its_commitment() {
    let mut rng = rng();
    let (pk, vk, trapdoor) = ZkPari::<E>::keygen_with_trapdoor(
        RangeProofCircuit {
            value: Some(0),
            value_allocated_last: false,
        },
        &mut rng,
    );

    let opening = CommittedInputOpening::<Fr>::rand(&mut rng);
    let commitment = pk.pedersen_commit(0, &[Fr::from(7u64)], &opening);
    let proof = ZkPari::<E>::simulate(
        &trapdoor,
        &vk,
        core::slice::from_ref(&commitment),
        &[],
        &mut rng,
    );

    let mut tampered = proof.clone();
    tampered.c_ci[0] = pk.pedersen_commit(0, &[Fr::from(8u64)], &opening);
    assert!(
        !ZkPari::<E>::verify(&tampered, &vk, &[]),
        "swapping the commitment must break the proof"
    );
}

// ---------------------------------------------------------------------------
// Instance-outlining guard
// ---------------------------------------------------------------------------

/// A native-SR1CS circuit that references its public input through a bare
/// coefficient-1 single-variable linear combination.
///
/// `ark-relations` 0.6.0 returns such an LC as the bare `Variable` instead of
/// interning it in the constraint system's LC map, and
/// `perform_instance_outlining` rewrites instance variables only by walking
/// that map — so the instance column survives outlining. The verifier reads
/// the public contribution only from the trailing outlining rows (and takes
/// `x_B = 0`), so the resulting keys would produce proofs that silently fail
/// to verify. Key generation must reject the circuit instead.
///
/// The trigger is the single-term LC, not which side it sits on, so both
/// placements are exercised.
#[derive(Clone, Copy)]
struct UnoutlinedInstanceCircuit {
    b_side: bool,
}

impl<F: Field> ZkPariCircuit<F> for UnoutlinedInstanceCircuit {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        cs.remove_predicate(R1CS_PREDICATE_LABEL);
        let _ = cs.register_predicate(
            SR1CS_PREDICATE_LABEL,
            PredicateConstraintSystem::new_sr1cs_predicate()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        );
        let w = cs.new_witness_variable(|| Ok(F::from(3u64)))?;
        let sq = cs.new_witness_variable(|| Ok(F::from(9u64)))?;
        let out = cs.new_input_variable(|| Ok(F::from(9u64)))?;
        if self.b_side {
            // (w)^2 = out
            cs.enforce_sr1cs_constraint(|| lc!() + w, || lc!() + out)?;
        } else {
            // (out)^2 = sq
            cs.enforce_sr1cs_constraint(|| lc!() + out, || lc!() + sq)?;
        }
        // No committed inputs: these tests lock in the outlining guard only,
        // and declaring a block would drag keygen's separate "committed input
        // appears in no constraint" assert into the expected-panic message.
        Ok(Vec::new())
    }
}

#[test]
#[should_panic(expected = "instance outlining did not remove instance variable")]
fn unoutlined_instance_column_in_b_rejected_at_keygen() {
    let _ = ZkPari::<E>::keygen(UnoutlinedInstanceCircuit { b_side: true }, &mut rng());
}

#[test]
#[should_panic(expected = "instance outlining did not remove instance variable")]
fn unoutlined_instance_column_in_a_rejected_at_keygen() {
    let _ = ZkPari::<E>::keygen(UnoutlinedInstanceCircuit { b_side: false }, &mut rng());
}

/// The same binding written as a multi-term linear combination is interned,
/// outlined correctly, and must key-generate and verify end to end.
#[test]
fn multi_term_instance_binding_is_outlined() {
    #[derive(Clone, Copy)]
    struct Ok2;
    impl<F: Field> ZkPariCircuit<F> for Ok2 {
        fn synthesize(
            self,
            cs: ConstraintSystemRef<F>,
        ) -> Result<Vec<Vec<Variable>>, SynthesisError> {
            cs.remove_predicate(R1CS_PREDICATE_LABEL);
            let _ = cs.register_predicate(
                SR1CS_PREDICATE_LABEL,
                PredicateConstraintSystem::new_sr1cs_predicate()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
            );
            let w = cs.new_witness_variable(|| Ok(F::from(3u64)))?;
            let out = cs.new_input_variable(|| Ok(F::from(3u64)))?;
            // (out - w)^2 = 0, both sides multi-term.
            cs.enforce_sr1cs_constraint(|| lc!() + out - w, || lc!() + w - w)?;
            Ok(vec![vec![w]])
        }
    }

    let mut rng = rng();
    let (pk, vk) = ZkPari::<E>::keygen(Ok2, &mut rng);
    let proof = ZkPari::<E>::prove(Ok2, &pk, &mut rng).unwrap();
    assert!(ZkPari::<E>::verify(&proof, &vk, &[Fr::from(3u64)]));
}

// ---------------------------------------------------------------------------
// Verifying-key transcript
// ---------------------------------------------------------------------------

/// `VerifyingKey::transcript` is public so integrators can derive the
/// challenge themselves. That documented recipe — clone the seeded state, then
/// absorb the public input, each `c_ci`, and `T` — must reproduce exactly what
/// verification computes.
#[test]
fn public_transcript_reproduces_the_challenge() {
    let mut rng = rng();
    let (a_val, b_val) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::BlocksAThenB,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let proof = ZkPari::<E>::prove(circuit, &pk, &mut rng).unwrap();
    let public_input = vec![a_val * b_val];

    let mut transcript = vk.transcript().clone();
    transcript
        .append_serializable_element(b"input", &public_input)
        .unwrap();
    for c_ci in &proof.c_ci {
        transcript
            .append_serializable_element(b"comm_ci", c_ci)
            .unwrap();
    }
    transcript
        .append_serializable_element(b"comm", &proof.t_g)
        .unwrap();

    assert_eq!(
        transcript.get_and_append_challenge(b"r").unwrap(),
        crate::utils::compute_chall::<E>(&vk, &public_input, &proof.c_ci, &proof.t_g),
    );
}

/// The seeded transcript must actually bind the key: two independently
/// generated keys for the same circuit must give different challenges for
/// identical proof material.
#[test]
fn seeded_transcript_binds_the_verifying_key() {
    let mut rng = rng();
    let (a_val, b_val) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
    let circuit = MulCircuit {
        a: Some(a_val),
        b: Some(b_val),
        spec: CommitSpec::A,
    };
    let (pk, vk) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let (_pk2, vk2) = ZkPari::<E>::keygen(circuit.clone(), &mut rng);
    let proof = ZkPari::<E>::prove(circuit, &pk, &mut rng).unwrap();
    let public_input = [a_val * b_val];

    let chall = |v| crate::utils::compute_chall::<E>(v, &public_input, &proof.c_ci, &proof.t_g);
    assert_eq!(chall(&vk), chall(&vk), "challenge derivation must be deterministic");
    assert_ne!(
        chall(&vk),
        chall(&vk2),
        "a different verifying key must give a different challenge"
    );
    // And the proof must not verify under the other key.
    assert!(!ZkPari::<E>::verify(&proof, &vk2, &public_input));
}
