//! Witness-level tests for the payment circuits: satisfiability, statement
//! binding (every public input tampered), wrong receipt position,
//! double-receive, overflow, and native-vs-in-circuit hash agreement.
//!
//! Everything here works at the constraint-system level (no SNARK), so toy
//! tree depths keep the suite fast; the benches' end-to-end flow covers
//! prove/verify against the ledger protocol.

use ark_ff::UniformRand;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::GR1CSVar;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::{Rng, SeedableRng};

use super::hasher::{hash, hash_var, HashCfg, DOM_ACCT, DOM_ILEAF, DOM_NODE, DOM_NULL, DOM_REC};
use super::indexed::{truncate_to_key, IndexedInsertion, IndexedMerkleTree};
use super::merkle::{MerklePath, MerkleTree};
use super::op::OpCircuit;
use super::recv::RecvCircuit;
use super::send::SendCircuit;
use super::Fr;

const RECEIPT_DEPTH: usize = 6;
const ACCT_DEPTH: usize = 4;

fn rng() -> StdRng {
    StdRng::seed_from_u64(20_260_901)
}

/// Whether the circuit's witnessed instance satisfies its constraints.
fn satisfied<C: ConstraintSynthesizer<Fr>>(circuit: C) -> bool {
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    cs.is_satisfied().unwrap()
}

/// Synthesize, then overwrite public-input slot `slot` (0-based, excluding
/// the leading constant) with a random value and re-check satisfiability —
/// i.e. does the statement actually bind that slot?
fn satisfied_with_tampered_input<C: ConstraintSynthesizer<Fr>>(
    circuit: C,
    slot: usize,
    rng: &mut StdRng,
) -> bool {
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    let mut inner = cs.into_inner().unwrap();
    inner.assignments.instance_assignment[1 + slot] = Fr::rand(rng);
    // ark-relations caches every linear combination's value at synthesis
    // time, and `is_satisfied` consults that cache before re-evaluating, so
    // a post-hoc tamper is invisible to cached constraints (the SNARK is
    // unaffected — keygen/prove/verify work off the matrices, which the
    // probe of this artifact confirmed reference the instance column).
    // Clearing the cache forces a fresh evaluation from the matrices'
    // linear combinations.
    inner.assignments.lc_assignment.clear();
    inner.is_satisfied().unwrap()
}

fn random_send(cfg: &HashCfg, rng: &mut StdRng) -> SendCircuit {
    let b = rng.gen_range(1u64..u64::MAX / 2);
    SendCircuit {
        cfg: cfg.clone(),
        sen: Fr::rand(rng),
        b,
        v: rng.gen_range(1..=b),
        kappa: Fr::rand(rng),
        root_null: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        rec: Fr::rand(rng),
    }
}

/// A receive instance whose consumed receipt sits in a small receipt tree
/// among unrelated leaves; returns the circuit and the tree (for
/// wrong-position tests).
fn random_recv(cfg: &HashCfg, rng: &mut StdRng) -> (RecvCircuit, MerkleTree) {
    let mut null_tree = IndexedMerkleTree::new(cfg, ACCT_DEPTH);
    for _ in 0..2 {
        null_tree.insert(truncate_to_key(Fr::rand(rng)));
    }

    let mut recv = RecvCircuit {
        cfg: cfg.clone(),
        rec: Fr::rand(rng),
        root: Fr::from(0u64), // set below
        b: rng.gen_range(0u64..u64::MAX / 2),
        v: rng.gen_range(1u64..u64::MAX / 4),
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        sen: Fr::rand(rng),
        pos: 0, // set below
        path: MerklePath {
            siblings: vec![],
            index_bits: vec![],
        },
        null_insert: IndexedInsertion::placeholder(),
    };

    let mut tree = MerkleTree::new(cfg, RECEIPT_DEPTH);
    tree.append(Fr::rand(rng));
    let index = tree.append(recv.receipt());
    tree.append(Fr::rand(rng));
    recv.pos = index as u64;
    recv.root = tree.root();
    recv.path = tree.path(index);
    recv.attach_nullifier_insertion(&mut null_tree);
    (recv, tree)
}

/// An operation-hiding send: real receipt out, branch-disabled tree gadgets.
fn random_op_send(cfg: &HashCfg, rng: &mut StdRng) -> OpCircuit {
    let b = rng.gen_range(1u64..u64::MAX / 2);
    let mut op = OpCircuit {
        cfg: cfg.clone(),
        is_send: true,
        acct: Fr::rand(rng),
        b,
        v: rng.gen_range(1..=b),
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        root_null: Fr::rand(rng),
        counterparty: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        r_dummy: Fr::rand(rng),
        root: Fr::rand(rng), // a send does not constrain the anchor
        pos: 0,
        path: MerklePath::empty(RECEIPT_DEPTH),
        null_insert: IndexedInsertion::placeholder(),
    };
    op.attach_dummy_insertion(ACCT_DEPTH);
    op
}

/// An operation-hiding receive: dummy receipt out, consuming a type-1
/// receipt from a small tree.
fn random_op_receive(cfg: &HashCfg, rng: &mut StdRng) -> OpCircuit {
    let mut null_tree = IndexedMerkleTree::new(cfg, ACCT_DEPTH);
    null_tree.insert(truncate_to_key(Fr::rand(rng)));

    let mut op = OpCircuit {
        cfg: cfg.clone(),
        is_send: false,
        acct: Fr::rand(rng),
        b: rng.gen_range(0u64..u64::MAX / 2),
        v: rng.gen_range(1u64..u64::MAX / 4),
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        root_null: Fr::from(0u64), // receive ignores this field
        counterparty: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        r_dummy: Fr::rand(rng),
        root: Fr::from(0u64), // set below
        pos: 0,               // set below
        path: MerklePath {
            siblings: vec![],
            index_bits: vec![],
        },
        null_insert: IndexedInsertion::placeholder(),
    };

    let mut tree = MerkleTree::new(cfg, RECEIPT_DEPTH);
    tree.append(Fr::rand(rng));
    let index = tree.append(op.receipt_in());
    op.pos = index as u64;
    op.root = tree.root();
    op.path = tree.path(index);
    op.attach_nullifier_insertion(&mut null_tree);
    op
}

// ---------------------------------------------------------------------------
// Hash agreement
// ---------------------------------------------------------------------------

/// Native and in-circuit hashes must agree bit for bit, for every domain
/// (both the Pedersen and the SHA-256 path) and both receipt arities.
#[test]
fn hash_native_matches_circuit() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let cs = ConstraintSystem::<Fr>::new_ref();
    let inputs: Vec<Fr> = (0..5).map(|_| Fr::rand(&mut rng)).collect();
    let vars: Vec<FpVar<Fr>> = inputs
        .iter()
        .map(|x| FpVar::new_witness(cs.clone(), || Ok(*x)).unwrap())
        .collect();

    for (dom, arity) in [
        (DOM_ACCT, 4),
        (DOM_NULL, 2),
        (DOM_REC, 4),
        (DOM_REC, 5),
        (DOM_NODE, 2),
        (DOM_ILEAF, 3),
    ] {
        let native = hash(&cfg, dom, &inputs[..arity]);
        let circuit = hash_var(&cfg, dom, &vars[..arity]).unwrap();
        assert_eq!(
            circuit.value().unwrap(),
            native,
            "hash mismatch for domain {dom} at arity {arity}"
        );
    }
    assert!(cs.is_satisfied().unwrap());
}

// ---------------------------------------------------------------------------
// R_send
// ---------------------------------------------------------------------------

#[test]
fn send_satisfiable_and_statement_binding() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let send = random_send(&cfg, &mut rng);
    assert!(satisfied(send.clone()));
    // Statement: (S, com, com', rho) — every slot must bind.
    for slot in 0..4 {
        assert!(
            !satisfied_with_tampered_input(send.clone(), slot, &mut rng),
            "tampered send statement slot {slot} still satisfiable"
        );
    }
}

/// v = 0 is a valid send (the paper's 0 <= v <= b; dummy receipts of the
/// op-hiding construction rely on it).
#[test]
fn send_allows_zero_amount() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let mut send = random_send(&cfg, &mut rng);
    send.v = 0;
    assert!(satisfied(send));
}

/// v > b must be unsatisfiable (the b - v range check).
#[test]
fn send_overdraft_unsatisfiable() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let mut send = random_send(&cfg, &mut rng);
    send.b = 10;
    send.v = 11;
    assert!(!satisfied(send));
}

// ---------------------------------------------------------------------------
// R_recv
// ---------------------------------------------------------------------------

#[test]
fn recv_satisfiable_and_statement_binding() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let (recv, _tree) = random_recv(&cfg, &mut rng);
    assert!(satisfied(recv.clone()));
    // Statement: (R, com, com', root_rho) — every slot must bind.
    for slot in 0..4 {
        assert!(
            !satisfied_with_tampered_input(recv.clone(), slot, &mut rng),
            "tampered recv statement slot {slot} still satisfiable"
        );
    }
}

#[test]
fn recv_allows_zero_amount() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let mut null_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    let (mut recv, mut tree) = random_recv(&cfg, &mut rng);
    recv.v = 0;
    // The receipt changed with v, so re-anchor it.
    let index = tree.append(recv.receipt());
    recv.pos = index as u64;
    recv.root = tree.root();
    recv.path = tree.path(index);
    recv.attach_nullifier_insertion(&mut null_tree);
    assert!(satisfied(recv));
}

/// The same receipt claimed at a wrong position must be unsatisfiable: the
/// path ordering is driven by the witnessed position's bits, and the
/// position feeds the nullifier.
#[test]
fn recv_wrong_position_unsatisfiable() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let (mut recv, tree) = random_recv(&cfg, &mut rng);
    let mut fresh_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    recv.pos = 0; // slot 0 holds someone else's receipt
    recv.path = tree.path(0);
    recv.attach_nullifier_insertion(&mut fresh_tree);
    assert!(!satisfied(recv));
}

/// Receiving the same receipt twice is unwitnessable: the indexed tree
/// rejects the duplicate nullifier outright.
#[test]
#[should_panic(expected = "duplicate key")]
fn double_receive_rejected_by_indexed_tree() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let mut null_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    let (mut recv, _tree) = random_recv(&cfg, &mut rng);
    recv.attach_nullifier_insertion(&mut null_tree); // first receive
    recv.attach_nullifier_insertion(&mut null_tree); // replay: panics
}

/// Crediting past 2^64 must be unsatisfiable (the b + v range check).
#[test]
fn recv_credit_overflow_unsatisfiable() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let mut null_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    let (mut recv, mut tree) = random_recv(&cfg, &mut rng);
    recv.b = u64::MAX - 1;
    recv.v = 2;
    let index = tree.append(recv.receipt());
    recv.pos = index as u64;
    recv.root = tree.root();
    recv.path = tree.path(index);
    recv.attach_nullifier_insertion(&mut null_tree);
    assert!(!satisfied(recv));
}

// ---------------------------------------------------------------------------
// R_op
// ---------------------------------------------------------------------------

#[test]
fn op_send_satisfiable_and_statement_binding() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let op = random_op_send(&cfg, &mut rng);
    assert!(satisfied(op.clone()));
    // Statement: (A, com, com', rho, root_rho). The first four slots bind;
    // the anchor is deliberately unconstrained in the send branch (the
    // ledger checks it natively, identically for both operations).
    for slot in 0..4 {
        assert!(
            !satisfied_with_tampered_input(op.clone(), slot, &mut rng),
            "tampered op-send statement slot {slot} still satisfiable"
        );
    }
    assert!(
        satisfied_with_tampered_input(op.clone(), 4, &mut rng),
        "the send branch must not constrain the anchor"
    );
}

#[test]
fn op_receive_satisfiable_and_statement_binding() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let op = random_op_receive(&cfg, &mut rng);
    assert!(satisfied(op.clone()));
    // The receive branch binds every slot, anchor included.
    for slot in 0..5 {
        assert!(
            !satisfied_with_tampered_input(op.clone(), slot, &mut rng),
            "tampered op-receive statement slot {slot} still satisfiable"
        );
    }
}

/// A dummy receipt (type 0) cannot be consumed: the in-circuit rho_in fixes
/// the type slot to 1, so no witness reaches a tree that holds the dummy.
#[test]
fn op_dummy_receipt_unspendable() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let mut op = random_op_receive(&cfg, &mut rng);

    // Re-anchor the consumed receipt to a *dummy* commitment
    // Com_rec(0, 0, 0, 0; r_dummy) instead of the type-1 receipt.
    let dummy = hash(
        &cfg,
        DOM_REC,
        &[
            Fr::from(0u64),
            Fr::from(0u64),
            Fr::from(0u64),
            Fr::from(0u64),
            op.r_dummy,
        ],
    );
    let mut tree = MerkleTree::new(&cfg, RECEIPT_DEPTH);
    let index = tree.append(dummy);
    let mut fresh_null_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    op.pos = index as u64;
    op.root = tree.root();
    op.path = tree.path(index);
    op.attach_nullifier_insertion(&mut fresh_null_tree);
    assert!(!satisfied(op));
}

/// The two branches synthesize the *same* circuit: identical constraint and
/// witness counts, which is what makes the operation type unobservable.
#[test]
fn op_branches_are_shape_identical() {
    let mut rng = rng();
    let cfg = HashCfg::new();
    let shape = |c: OpCircuit| {
        let cs = ConstraintSystem::<Fr>::new_ref();
        c.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        (
            cs.num_constraints(),
            cs.num_witness_variables(),
            cs.num_instance_variables(),
        )
    };
    assert_eq!(
        shape(random_op_send(&cfg, &mut rng)),
        shape(random_op_receive(&cfg, &mut rng))
    );
}

