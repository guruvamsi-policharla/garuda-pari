//! Experiment 3 (phase 3a) — prover cost of the payment circuits (BLS12-381).
//!
//! Benchmarks the paper's private-transfer relations (`zkpari::circuits`):
//!
//!   - *R_send*: three Pedersen commitment openings plus range checks — no
//!     tree, no PRF, no depth parameter. Account commitments are
//!     `Com_acct(b, kappa, root_null; r)`, so the owner's
//!     indexed-nullifier-tree root is bound inside the commitment and an
//!     account's entire public state is one hash.
//!
//!   - *R_recv*: carries all the hashing — the receipt's MMR opening at a
//!     witnessed position `pos` (path ordering driven by the bits of pos,
//!     depth fixed at 40), the nullifier derived in-circuit as
//!     CRPRF_kappa(recv, pos) — never published — and the paper's
//!     `AccVerifyInsert` into the receiver's user-maintained indexed
//!     nullifier tree (with the non-membership low-leaf argument, so
//!     double-receives are impossible). The tree roots are witnesses, bound
//!     inside `com` / `com'`; the statement is `(R, com, com', root_rho)`.
//!     The nullifier-tree depth is swept over {10, 20}.
//!
//!   - *R_op*: the operation-hiding relation — a witness-selected OR of the
//!     send and receive branches over the shared statement
//!     `(A, com, com', rho, root_rho)`. Both branches share every gadget
//!     (the selector muxes the balance delta, roots, and published-receipt
//!     preimage, and gates the receive-only equalities), so the cost is
//!     operation-independent by construction; the rows here prove with the
//!     receive branch, the more constrained witness.
//!
//! Hashes follow the Sapling split (see `src/circuits/hasher.rs`):
//! Pedersen over Jubjub for Merkle nodes, indexed-tree leaves, and
//! commitments; SHA-256 for the single CRPRF call site (nullifier
//! derivation — R_send has no PRF call).
//!
//! What stays native and unbenchmarked here: the ledger's root-history
//! check on the revealed receipt anchor (root_rho in the retained set of
//! recent roots), receiver registration, and R_reg entirely (a Schnorr-style
//! proof outside the SNARK).
//!
//! The circuits are plain R1CS (ark-r1cs-std) fed through the R1CS-to-SR1CS
//! adapter, so both counts are reported: `r1cs` is what the gadgets emit,
//! `sr1cs` is what the prover pays for (each R1CS row splits into squares,
//! plus outlining rows; the FFT domain rounds up to a power of two).
//! `prove` includes circuit synthesis, as everywhere in these benches.
//!
//! Before the table, an end-to-end flow runs as a correctness gate: Alice
//! sends 300 to Bob (real prove/verify), the ledger compare-and-swaps her
//! (single) account commitment, appends the receipt to the MMR, and records
//! the new root in its history; Bob locates the receipt's position in the
//! public log, derives the nullifier under his own key, inserts it into his
//! local indexed tree, recommits `(b + v, kappa, root_null')`, and proves
//! R_recv against the recorded anchor. The receive submission is
//! `(R, com', root_rho, proof)` — no nullifier and no tree root on the
//! wire. Tampering with any public input of either statement is rejected,
//! a proof for the same receipt at a wrong position is rejected, and
//! replaying the same receive against Bob's updated commitment is rejected
//! (the old `com` no longer matches the ledger).
//!
//! Threads: single-threaded by default. Set `ZKPARI_BENCH_THREADS=0` for all
//! cores, or `=N` for N.
//!
//! Run with: cargo bench --bench circuits

mod common;

use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::{rngs::StdRng, Rng, SeedableRng};
use ark_std::UniformRand;

use common::*;
use zkpari::circuits::hasher::HashCfg;
use zkpari::circuits::indexed::{truncate_to_key, IndexedInsertion, IndexedMerkleTree};
use zkpari::circuits::merkle::{root_from_path, MerklePath, MerkleTree};
use zkpari::circuits::op::OpCircuit;
use zkpari::circuits::recv::RecvCircuit;
use zkpari::circuits::send::SendCircuit;
use zkpari::ZkPari;

/// Depths of the user-maintained (indexed) nullifier trees
/// (2^10 / 2^20 lifetime receipts per account). R_recv and R_op have one.
const ACCT_TREE_DEPTHS: &[usize] = &[10, 20];

/// Depth of the global receipt tree (membership path):
/// 2^40 receipts of capacity, ~4 months of history at 100K TPS.
const RECEIPT_DEPTH: usize = 40;

const PROVE_ITERS: usize = 5;

fn main() {
    in_bench_pool(run);
}

struct Row {
    name: String,
    r1cs: Option<usize>,
    sr1cs: usize,
    instance_len: usize,
    domain: usize,
    keygen_ms: f64,
    prove_ms: f64,
    verify_us: f64,
    proof_bytes: usize,
}

/// Keygen/prove/verify a circuit and collect one table row.
/// `r1cs` is the pre-adapter constraint count (None for native SR1CS).
fn measure<C: ConstraintSynthesizer<Fr> + Clone>(
    name: &str,
    circuit: C,
    public_input: &[Fr],
    r1cs: Option<usize>,
    prove_iters: usize,
    rng: &mut StdRng,
) -> Row {
    eprint!("  {name:<24} keygen ...");
    let mut keys = None;
    let keygen_ms = median_ms(1, || {
        keys = Some(ZkPari::<E>::keygen(circuit.clone(), rng));
    });
    let (pk, vk) = keys.unwrap();

    eprint!(" prove x{prove_iters} ...");
    let mut proof = None;
    let prove_ms = median_ms(prove_iters, || {
        proof = Some(ZkPari::<E>::prove(circuit.clone(), &pk, rng).expect("proving failed"));
    });
    let proof = proof.unwrap();
    assert!(
        ZkPari::<E>::verify(&proof, &vk, public_input),
        "sanity verification failed for {name}"
    );

    eprint!(" verify ...");
    let verify_us = 1000.0
        * time_ms(100, 500, || {
            std::hint::black_box(ZkPari::<E>::verify(&proof, &vk, public_input));
        });
    eprintln!(" done");

    Row {
        name: name.to_string(),
        r1cs,
        sr1cs: vk.succinct_index.num_constraints,
        instance_len: vk.succinct_index.instance_len,
        domain: vk.domain.size as usize,
        keygen_ms,
        prove_ms,
        verify_us,
        proof_bytes: compressed_size(&proof),
    }
}

/// R1CS constraints a gadget circuit emits, before the SR1CS adapter.
/// Also asserts the witnessed instance actually satisfies the constraints,
/// catching native/in-circuit hash mismatches before the expensive keygen.
fn r1cs_count<C: ConstraintSynthesizer<Fr>>(circuit: C) -> usize {
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit
        .generate_constraints(cs.clone())
        .expect("synthesis failed");
    let count = cs.num_constraints();
    cs.finalize();
    assert_eq!(
        cs.is_satisfied(),
        Ok(true),
        "instance does not satisfy the circuit"
    );
    count
}

fn run() {
    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║  3a. ZK-Pari payment circuits — BLS12-381                            ║");
    println!("║      private transfer: R_send, R_recv, and operation-hiding R_op     ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Threads: {}.", thread_label());
    println!("Hashes (Sapling split): Pedersen/Jubjub (8-bit byte windows) for");
    println!("          Merkle nodes, indexed leaves, and commitments; SHA-256 for");
    println!("          the nullifier CRPRF (receive side only — R_send has no");
    println!("          hashing beyond its three commitment openings).");
    println!("Private transfer: nullifier = CRPRF_kappa(recv, pos), derived and");
    println!("          inserted in-circuit (AccVerifyInsert); the nullifier-tree");
    println!("          root lives inside the account commitment. Nullifier-tree");
    println!("          depth swept over {ACCT_TREE_DEPTHS:?}, receipt-tree opening");
    println!("          fixed at depth {RECEIPT_DEPTH} and bound to the witnessed position.");
    println!("R_op: one circuit for both operations; a witness bit selects the");
    println!("          branch, so sends and receives are indistinguishable on the");
    println!("          wire and cost the same to prove.");
    println!();

    let mut rng = StdRng::seed_from_u64(20_260_825);

    // Fast satisfiability gate at toy depths: catches native/in-circuit
    // hash mismatches (and R_op branch-shape drift) in seconds, before any
    // keygen.
    {
        let cfg = HashCfg::new();
        r1cs_count(random_send(&cfg, &mut rng));
        r1cs_count(random_recv(&cfg, 6, 4, &mut rng));
        let n_send = r1cs_count(random_op_send(&cfg, 6, 4, &mut rng));
        let n_recv = r1cs_count(random_op_receive(&cfg, 6, 4, &mut rng));
        assert_eq!(
            n_send, n_recv,
            "R_op branches must synthesize the same constraint count"
        );
    }

    e2e_flow(&mut rng);

    // ── Benchmark table ─────────────────────────────────────────────────
    let cfg = HashCfg::new();
    let mut rows = Vec::new();

    {
        let send = random_send(&cfg, &mut rng);
        rows.push(measure(
            "R_send",
            send.clone(),
            &send.public_input(),
            Some(r1cs_count(send.clone())),
            PROVE_ITERS,
            &mut rng,
        ));
    }

    for &depth in ACCT_TREE_DEPTHS {
        let recv = random_recv(&cfg, RECEIPT_DEPTH, depth, &mut rng);
        rows.push(measure(
            &format!("R_recv d{depth}"),
            recv.clone(),
            &recv.public_input(),
            Some(r1cs_count(recv.clone())),
            PROVE_ITERS,
            &mut rng,
        ));
    }

    for &depth in ACCT_TREE_DEPTHS {
        let op = random_op_receive(&cfg, RECEIPT_DEPTH, depth, &mut rng);
        rows.push(measure(
            &format!("R_op d{depth}"),
            op.clone(),
            &op.public_input(),
            Some(r1cs_count(op.clone())),
            PROVE_ITERS,
            &mut rng,
        ));
    }

    println!();
    println!("  circuit                  │    r1cs │    sr1cs │   domain │ |x| │ keygen ms │ prove ms │ verify us │ proof B");
    println!("  ─────────────────────────┼─────────┼──────────┼──────────┼─────┼───────────┼──────────┼───────────┼────────");
    for r in &rows {
        println!(
            "  {:<24} │ {:>7} │ {:>8} │ {:>8} │ {:>3} │ {:>9.1} │ {:>8.1} │ {:>9.1} │ {:>6}",
            r.name,
            r.r1cs.map_or_else(|| "—".to_string(), |n| n.to_string()),
            r.sr1cs,
            r.domain,
            r.instance_len,
            r.keygen_ms,
            r.prove_ms,
            r.verify_us,
            r.proof_bytes,
        );
    }
    println!();
    println!("  |x| counts the leading constant 1. Proofs are 2 G1 + 1 F.");
    println!();
}

// ── Random instances for the table ──────────────────────────────────────

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

fn random_recv(
    cfg: &HashCfg,
    receipt_depth: usize,
    null_depth: usize,
    rng: &mut StdRng,
) -> RecvCircuit {
    // The receiver's nullifier tree, with a few earlier receipts consumed.
    let mut null_tree = IndexedMerkleTree::new(cfg, null_depth);
    for _ in 0..3 {
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

    // A small receipt tree with unrelated receipts around ours.
    let mut tree = MerkleTree::new(cfg, receipt_depth);
    for _ in 0..3 {
        tree.append(Fr::rand(rng));
    }
    let index = tree.append(recv.receipt());
    for _ in 0..3 {
        tree.append(Fr::rand(rng));
    }
    recv.pos = index as u64;
    recv.root = tree.root();
    recv.path = tree.path(index);

    // The nullifier depends on (kappa, pos), so it is derived only now.
    recv.attach_nullifier_insertion(&mut null_tree);
    recv
}

fn random_op_send(
    cfg: &HashCfg,
    receipt_depth: usize,
    null_depth: usize,
    rng: &mut StdRng,
) -> OpCircuit {
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
        root: Fr::rand(rng), // unconstrained on the send branch
        pos: 0,
        path: MerklePath::empty(receipt_depth),
        null_insert: IndexedInsertion::placeholder(),
    };
    op.attach_dummy_insertion(null_depth);
    op
}

fn random_op_receive(
    cfg: &HashCfg,
    receipt_depth: usize,
    null_depth: usize,
    rng: &mut StdRng,
) -> OpCircuit {
    let mut null_tree = IndexedMerkleTree::new(cfg, null_depth);
    for _ in 0..3 {
        null_tree.insert(truncate_to_key(Fr::rand(rng)));
    }

    let mut op = OpCircuit {
        cfg: cfg.clone(),
        is_send: false,
        acct: Fr::rand(rng),
        b: rng.gen_range(0u64..u64::MAX / 2),
        v: rng.gen_range(1u64..u64::MAX / 4),
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        root_null: Fr::from(0u64), // ignored on the receive branch
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

    let mut tree = MerkleTree::new(cfg, receipt_depth);
    for _ in 0..3 {
        tree.append(Fr::rand(rng));
    }
    let index = tree.append(op.receipt_in());
    for _ in 0..3 {
        tree.append(Fr::rand(rng));
    }
    op.pos = index as u64;
    op.root = tree.root();
    op.path = tree.path(index);
    op.attach_nullifier_insertion(&mut null_tree);
    op
}

// ── End-to-end correctness gate ─────────────────────────────────────────

fn e2e_flow(rng: &mut StdRng) {
    const ACCT_DEPTH: usize = 10;
    let cfg = HashCfg::new();

    println!(
        "End-to-end private transfer (receipts d{RECEIPT_DEPTH}, nullifier tree d{ACCT_DEPTH}): \
         Alice sends 300 to Bob"
    );

    // Trusted setup, one CRS per relation. Keygen only needs the circuit
    // *shape* (tree depths), so any instance of the right depths works.
    let (send_pk, send_vk) = ZkPari::<E>::keygen(random_send(&cfg, rng), rng);
    let (recv_pk, recv_vk) =
        ZkPari::<E>::keygen(RecvCircuit::blank(&cfg, RECEIPT_DEPTH, ACCT_DEPTH), rng);

    // Global ledger state: the receipt MMR and the retained root history
    // (the W most recent roots; receive anchors must be in it).
    let mut receipt_tree = MerkleTree::new(&cfg, RECEIPT_DEPTH);
    let mut root_history: Vec<Fr> = vec![receipt_tree.root()];
    for _ in 0..5 {
        let noise = Fr::rand(rng);
        receipt_tree.append(noise); // receipts of other users
        root_history.push(receipt_tree.root());
    }

    // Registration commits the empty-tree root inside the account
    // commitment. The ledger stores exactly one commitment per account.
    let empty_root = IndexedMerkleTree::new(&cfg, ACCT_DEPTH).root();
    let alice = SendCircuit {
        cfg: cfg.clone(),
        sen: Fr::rand(rng),
        b: 1000,
        v: 300,
        kappa: Fr::rand(rng),
        root_null: empty_root,
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        rec: Fr::rand(rng), // Bob's identifier
    };
    let mut ledger_alice = alice.com();

    let bob_kappa = Fr::rand(rng);
    let bob_r = Fr::rand(rng);
    let mut bob_null_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    assert_eq!(bob_null_tree.root(), empty_root);

    // 1. Alice proves R_send; the ledger verifies, compare-and-swaps her
    //    single commitment (key and nullifier-tree root unchanged), appends
    //    rho to the receipt MMR, and records the new root in its history.
    //    Statement order: (S, com, com', rho).
    let send_proof = ZkPari::<E>::prove(alice.clone(), &send_pk, rng).expect("send proving failed");
    let send_x = alice.public_input();
    assert!(
        ZkPari::<E>::verify(&send_proof, &send_vk, &send_x),
        "send proof rejected"
    );
    assert_eq!(
        send_x[1], ledger_alice,
        "statement must open Alice's account"
    );
    ledger_alice = send_x[2]; // swap in com'
    let receipt_index = receipt_tree.append(send_x[3]); // rho joins the MMR
    root_history.push(receipt_tree.root());
    let anchor = *root_history.last().unwrap();

    // 2. Alice forwards the opening (rho, v, S, R, r'') privately. Bob
    //    locates rho's position in the public log, derives the nullifier
    //    from (kappa_Bob, "recv", pos), inserts it into his local indexed
    //    tree, recommits (b + v, kappa, root_null'), and proves R_recv
    //    against the latest anchor. The submission is
    //    (R, com', root_rho, proof) — no nullifier and no tree root on the
    //    wire. Statement order: (R, com, com', root_rho).
    let mut bob = RecvCircuit {
        cfg: cfg.clone(),
        rec: alice.rec,
        root: anchor,
        b: 500,
        v: alice.v,
        kappa: bob_kappa,
        r: bob_r,
        r_new: Fr::rand(rng),
        r_receipt: alice.r_receipt,
        sen: alice.sen,
        pos: receipt_index as u64,
        path: receipt_tree.path(receipt_index),
        null_insert: IndexedInsertion::placeholder(),
    };
    bob.attach_nullifier_insertion(&mut bob_null_tree);
    // Register Bob: one commitment, empty-tree root bound inside it.
    let mut ledger_bob = bob.com();
    assert_eq!(bob.null_insert.old_root, empty_root);

    assert_eq!(
        bob.receipt(),
        alice.receipt(),
        "receipt must reconstruct identically on both sides"
    );
    assert_eq!(
        root_from_path(&cfg, bob.receipt(), &bob.path),
        anchor,
        "native path check failed"
    );

    let recv_proof = ZkPari::<E>::prove(bob.clone(), &recv_pk, rng).expect("recv proving failed");
    let recv_x = bob.public_input();
    assert!(
        ZkPari::<E>::verify(&recv_proof, &recv_vk, &recv_x),
        "recv proof rejected"
    );
    assert!(
        root_history.contains(&recv_x[3]),
        "revealed anchor must be in the ledger's root history"
    );
    assert_eq!(recv_x[1], ledger_bob, "statement must open Bob's account");
    ledger_bob = recv_x[2]; // swap in com'
    assert_eq!(
        ledger_bob,
        bob.com_new(),
        "credited commitment must open to (b + v, kappa, root_null')"
    );
    assert_eq!(
        bob.null_insert.new_root,
        bob_null_tree.root(),
        "committed root must match Bob's updated tree"
    );

    // 3. Tampering with *any* public input of either statement must be
    //    rejected. (A double-receive cannot even be witnessed: the indexed
    //    tree rejects duplicate keys, and no low leaf satisfying the
    //    in-circuit ordering exists for a present key.)
    for i in 0..recv_x.len() {
        let mut bad = recv_x.clone();
        bad[i] = Fr::rand(rng);
        assert!(
            !ZkPari::<E>::verify(&recv_proof, &recv_vk, &bad),
            "tampered recv statement slot {i} accepted"
        );
    }
    for i in 0..send_x.len() {
        let mut bad = send_x.clone();
        bad[i] = Fr::rand(rng);
        assert!(
            !ZkPari::<E>::verify(&send_proof, &send_vk, &bad),
            "tampered send statement slot {i} accepted"
        );
    }

    // 4. The same receipt at a wrong position must be rejected: the MMR
    //    opening pins rho to its true position, and the position pins the
    //    nullifier. Slot 0 holds another user's receipt, so no witness
    //    exists — the constraint system is unsatisfiable, and a proof
    //    forced from the bad witness fails verification.
    let mut cheat = bob.clone();
    cheat.pos = 0;
    cheat.path = receipt_tree.path(0);
    let mut cheat_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH); // Bob's pre-receive state
    cheat.attach_nullifier_insertion(&mut cheat_tree);

    let cs = ConstraintSystem::<Fr>::new_ref();
    cheat
        .clone()
        .generate_constraints(cs.clone())
        .expect("synthesis failed");
    cs.finalize();
    assert_eq!(
        cs.is_satisfied(),
        Ok(false),
        "wrong-position witness must not satisfy R_recv"
    );
    if let Ok(forged) = ZkPari::<E>::prove(cheat.clone(), &recv_pk, rng) {
        assert!(
            !ZkPari::<E>::verify(&forged, &recv_vk, &cheat.public_input()),
            "wrong-position proof accepted"
        );
    }

    // 5. Replaying the same receive against Bob's updated commitment is
    //    rejected: the original statement's `com` no longer matches the
    //    ledger, and rebinding the proof to the current commitment fails
    //    verification.
    assert_ne!(
        recv_x[1], ledger_bob,
        "replay: old com must no longer match the ledger"
    );
    let mut replay = recv_x.clone();
    replay[1] = ledger_bob;
    assert!(
        !ZkPari::<E>::verify(&recv_proof, &recv_vk, &replay),
        "replay against updated commitment accepted"
    );

    // Keep the linter honest about the updated ledger state.
    let _ = ledger_alice;

    println!("  send + receive verified, ledger stores one commitment per account,");
    println!("  tampering, wrong-position, and receive-replay rejected");
    println!();
}
