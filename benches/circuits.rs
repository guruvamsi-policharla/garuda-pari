//! Experiment 3 (phase 3a) — prover cost of the payment circuits (BLS12-381).
//!
//! Two payment flavours share this table:
//!
//!   - *Confidential transfer* (Zether-style): a native-SR1CS range proof on
//!     the amount, declared as the single committed-input block, so the
//!     proof's C_ci is itself the ledger's Pedersen commitment. Proof is
//!     3 G1 + 1 F, of which C_ci is ledger state (incremental 2 G1 + 1 F).
//!
//!   - *Private transfer* (the paper's R_send / R_recv): unlinkable payments
//!     over hash-based account commitments opened in-circuit as public
//!     inputs. Zero committed-input blocks — the proof is 2 G1 + 1 F and
//!     verification is 3 pairings. Both relations verify the paper's
//!     `AccVerifyInsert` *in-circuit*: the per-account nullifier/tag trees
//!     are user-maintained indexed Merkle trees (with the non-membership
//!     low-leaf argument, so double-receives are impossible), the statement
//!     carries (root, root'), and the ledger's only tree work is
//!     compare-and-swap on 32-byte roots. Batch verification cost is
//!     independent of circuit size, so the added constraints are free for
//!     the ledger — they only cost the prover.
//!     The account-tree depth is swept over {10, 20}; the receipt-tree
//!     membership path in R_recv is fixed at depth 40.
//!
//!   Hashes follow the Sapling split (see `common/private/hasher.rs`):
//!   Pedersen over Jubjub for Merkle nodes, indexed-tree leaves, and
//!   commitments; SHA-256 for the two CRPRF call sites (nullifier and tag
//!   derivation, R_send only — R_recv has no PRF call).
//!
//!   What stays native and unbenchmarked here: the ledger's root-history
//!   check on the revealed receipt anchor (rootrho in the retained set of
//!   recent roots), receiver registration, and R_reg entirely.
//!
//! The gadget circuits are plain R1CS (ark-r1cs-std) fed through the
//! R1CS-to-SR1CS adapter, so both counts are reported: `r1cs` is what the
//! gadgets emit, `sr1cs` is what the prover pays for (each R1CS row splits
//! into squares, plus outlining rows; the FFT domain rounds up to a power of
//! two). `prove` includes circuit synthesis, as everywhere in these benches.
//!
//! Before the table, an end-to-end flow runs as a correctness gate: Alice
//! sends 300 to Bob (real prove/verify), the ledger compare-and-swaps her
//! account commitment and tag root, appends the receipt, and records the new
//! root in its history; Bob proves receipt + nullifier insertion against
//! that anchor, the ledger checks the anchor is in its history, and tampered
//! public inputs are rejected.
//!
//! Threads: single-threaded by default. Set `ZKPARI_BENCH_THREADS=0` for all
//! cores, or `=N` for N.
//!
//! Run with: cargo bench --bench circuits

mod common;

use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::{rngs::StdRng, Rng, SeedableRng};
use ark_std::UniformRand;

use common::private::hasher::HashCfg;
use common::private::indexed::{truncate_to_key, IndexedInsertion, IndexedMerkleTree};
use common::private::merkle::{root_from_path, MerkleTree};
use common::private::recv::RecvCircuit;
use common::private::send::SendCircuit;
use common::*;
use zkpari::{Uncommitted, ZkPari, ZkPariCircuit};

/// Depths of the user-maintained (indexed) nullifier/tag trees
/// (2^10 / 2^20 lifetime payments per account).
const ACCT_TREE_DEPTHS: &[usize] = &[10, 20];

/// Depth of the global receipt tree (R_recv membership path):
/// 2^40 receipts of capacity, ~4 months of history at 100K TPS.
const RECEIPT_DEPTH: usize = 40;

/// Bit widths for the confidential-transfer range proof.
const RANGE_BITS: &[usize] = &[32, 64];

const PROVE_ITERS: usize = 5;

fn main() {
    in_bench_pool(run);
}

struct Row {
    name: String,
    r1cs: Option<usize>,
    sr1cs: usize,
    instance_len: usize,
    blocks: usize,
    domain: usize,
    keygen_ms: f64,
    prove_ms: f64,
    verify_us: f64,
    proof_bytes: usize,
}

/// Keygen/prove/verify a circuit and collect one table row.
/// `r1cs` is the pre-adapter constraint count (None for native SR1CS).
fn measure<C: ZkPariCircuit<Fr> + Clone>(
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
        blocks: vk.succinct_index.committed_input_blocks.len(),
        domain: vk.domain.size as usize,
        keygen_ms,
        prove_ms,
        verify_us,
        proof_bytes: proof_element_bytes(&proof),
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
    assert_eq!(cs.is_satisfied(), Ok(true), "instance does not satisfy the circuit");
    count
}

fn run() {
    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║  3a. ZK-Pari payment circuits — BLS12-381                            ║");
    println!("║      confidential transfer (range) and private transfer (send/recv)  ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Threads: {}.", thread_label());
    println!("Hashes (Sapling split): Pedersen/Jubjub (8-bit byte windows) for");
    println!("          Merkle nodes, indexed leaves, and commitments; SHA-256 for");
    println!("          the nullifier/tag CRPRFs (R_send only).");
    println!("Private transfer: indexed-tree insertion (AccVerifyInsert) proved");
    println!("          in-circuit; account-tree depth swept over {ACCT_TREE_DEPTHS:?},");
    println!("          receipt-tree membership fixed at depth {RECEIPT_DEPTH}.");
    println!();

    let mut rng = StdRng::seed_from_u64(20_260_825);

    e2e_flow(&mut rng);

    // ── Benchmark table ─────────────────────────────────────────────────
    let cfg = HashCfg::new();
    let mut rows = Vec::new();

    for &bits in RANGE_BITS {
        let circuit = ConfidentialRangeCircuit {
            value: rng.gen::<u64>() >> (64 - bits),
            bits,
        };
        rows.push(measure(
            &format!("confidential range {bits}b"),
            circuit,
            &[],
            None,
            PROVE_ITERS,
            &mut rng,
        ));
    }

    for &depth in ACCT_TREE_DEPTHS {
        let send = random_send(&cfg, depth, &mut rng);
        rows.push(measure(
            &format!("R_send d{depth}"),
            Uncommitted(send.clone()),
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
            Uncommitted(recv.clone()),
            &recv.public_input(),
            Some(r1cs_count(recv.clone())),
            PROVE_ITERS,
            &mut rng,
        ));
    }

    println!();
    println!("  circuit                  │    r1cs │    sr1cs │   domain │ |x| │ blocks │ keygen ms │ prove ms │ verify us │ proof B");
    println!("  ─────────────────────────┼─────────┼──────────┼──────────┼─────┼────────┼───────────┼──────────┼───────────┼────────");
    for r in &rows {
        println!(
            "  {:<24} │ {:>7} │ {:>8} │ {:>8} │ {:>3} │ {:>6} │ {:>9.1} │ {:>8.1} │ {:>9.1} │ {:>6}",
            r.name,
            r.r1cs.map_or_else(|| "—".to_string(), |n| n.to_string()),
            r.sr1cs,
            r.domain,
            r.instance_len,
            r.blocks,
            r.keygen_ms,
            r.prove_ms,
            r.verify_us,
            r.proof_bytes,
        );
    }
    println!();
    println!("  |x| counts the leading constant 1. Proofs are (2 + blocks) G1 + 1 F.");
    println!();
}

// ── Random instances for the table ──────────────────────────────────────

fn random_send(cfg: &HashCfg, tag_depth: usize, rng: &mut StdRng) -> SendCircuit {
    // The sender's tag tree, with a few earlier payments in it.
    let mut tag_tree = IndexedMerkleTree::new(cfg, tag_depth);
    for _ in 0..3 {
        tag_tree.insert(truncate_to_key(Fr::rand(rng)));
    }

    let b = rng.gen_range(1u64..u64::MAX / 2);
    let mut send = SendCircuit {
        cfg: cfg.clone(),
        sen: Fr::rand(rng),
        b,
        v: rng.gen_range(1..=b),
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        rec: Fr::rand(rng),
        zeta: Fr::rand(rng),
        tag_insert: IndexedInsertion::placeholder(),
    };
    send.attach_tag_insertion(&mut tag_tree);
    send
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
        nullifier: Fr::rand(rng),
        root: Fr::from(0u64), // set below
        b: rng.gen_range(0u64..u64::MAX / 2),
        v: rng.gen_range(1u64..u64::MAX / 4),
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        sen: Fr::rand(rng),
        path: common::private::merkle::MerklePath {
            siblings: vec![],
            index_bits: vec![],
        },
        null_insert: IndexedInsertion::placeholder(),
    };
    recv.attach_nullifier_insertion(&mut null_tree);

    // A small receipt tree with unrelated receipts around ours.
    let mut tree = MerkleTree::new(cfg, receipt_depth);
    for _ in 0..3 {
        tree.append(Fr::rand(rng));
    }
    let index = tree.append(recv.receipt());
    for _ in 0..3 {
        tree.append(Fr::rand(rng));
    }
    recv.root = tree.root();
    recv.path = tree.path(index);
    recv
}

// ── End-to-end correctness gate ─────────────────────────────────────────

fn e2e_flow(rng: &mut StdRng) {
    const ACCT_DEPTH: usize = 10;
    let cfg = HashCfg::new();

    println!(
        "End-to-end private transfer (receipts d{RECEIPT_DEPTH}, account trees d{ACCT_DEPTH}): \
         Alice sends 300 to Bob"
    );

    // Trusted setup, one CRS per relation. Keygen only needs the circuit
    // *shape* (tree depths), so any instance of the right depths works.
    let (send_pk, send_vk) = ZkPari::<E>::keygen(
        Uncommitted(random_send(&cfg, ACCT_DEPTH, rng)),
        rng,
    );
    let (recv_pk, recv_vk) = ZkPari::<E>::keygen(
        Uncommitted(RecvCircuit::blank(&cfg, RECEIPT_DEPTH, ACCT_DEPTH)),
        rng,
    );

    // Global ledger state: the receipt tree and the retained root history
    // (the W most recent roots; receive anchors must be in it).
    let mut receipt_tree = MerkleTree::new(&cfg, RECEIPT_DEPTH);
    let mut root_history: Vec<Fr> = vec![receipt_tree.root()];
    for _ in 0..5 {
        let noise = Fr::rand(rng);
        receipt_tree.append(noise); // receipts of other users
        root_history.push(receipt_tree.root());
    }

    // Alice's account. She maintains her own tag tree; the ledger stores
    // only (com, roottag).
    let mut alice_tag_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);
    alice_tag_tree.insert(truncate_to_key(Fr::rand(rng))); // an earlier payment
    let mut alice = SendCircuit {
        cfg: cfg.clone(),
        sen: Fr::rand(rng),
        b: 1000,
        v: 300,
        kappa: Fr::rand(rng),
        r: Fr::rand(rng),
        r_new: Fr::rand(rng),
        r_receipt: Fr::rand(rng),
        rec: Fr::rand(rng), // Bob's identifier
        zeta: Fr::rand(rng),
        tag_insert: IndexedInsertion::placeholder(),
    };
    let mut ledger_alice = (alice.com(), alice_tag_tree.root()); // (com, roottag)

    // Bob's account and his nullifier tree; ledger stores (com, rootnull).
    let bob_kappa = Fr::rand(rng);
    let bob_r = Fr::rand(rng);
    let mut bob_null_tree = IndexedMerkleTree::new(&cfg, ACCT_DEPTH);

    // 1. Alice inserts the tag into her tree and proves R_send; the ledger
    //    verifies, then compare-and-swaps her commitment and tag root.
    //    Statement order: (Sen, com, com', roottag, roottag', rho, tag).
    alice.attach_tag_insertion(&mut alice_tag_tree);
    let send_proof =
        ZkPari::<E>::prove(Uncommitted(alice.clone()), &send_pk, rng).expect("send proving failed");
    let send_x = alice.public_input();
    assert!(
        ZkPari::<E>::verify(&send_proof, &send_vk, &send_x),
        "send proof rejected"
    );
    assert_eq!(send_x[1], ledger_alice.0, "statement must open Alice's account");
    assert_eq!(send_x[3], ledger_alice.1, "statement must extend Alice's tag root");
    ledger_alice = (send_x[2], send_x[4]); // swap in com' and roottag'
    let receipt_index = receipt_tree.append(send_x[5]); // rho joins the tree

    // The ledger records the new root in its retained history; receivers
    // later reveal one of these roots as their membership anchor.
    root_history.push(receipt_tree.root());
    let anchor = *root_history.last().unwrap();

    // 2. Bob learns (v, Sen, nullifier, r'') out of band, inserts the
    //    nullifier into his tree, computes the receipt path from the public
    //    log against the latest anchor, and proves R_recv.
    //    Statement order: (Rec, com, rootnull, com', rootnull', nf, rootrho).
    let bob_rootnull_before = bob_null_tree.root();
    let mut bob = RecvCircuit {
        cfg: cfg.clone(),
        rec: alice.rec,
        nullifier: alice.nullifier(),
        root: anchor,
        b: 500,
        v: alice.v,
        kappa: bob_kappa,
        r: bob_r,
        r_new: Fr::rand(rng),
        r_receipt: alice.r_receipt,
        sen: alice.sen,
        path: receipt_tree.path(receipt_index),
        null_insert: IndexedInsertion::placeholder(),
    };
    bob.attach_nullifier_insertion(&mut bob_null_tree);
    let mut ledger_bob = (bob.com(), bob_rootnull_before); // (com, rootnull)

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

    let recv_proof =
        ZkPari::<E>::prove(Uncommitted(bob.clone()), &recv_pk, rng).expect("recv proving failed");
    let recv_x = bob.public_input();
    assert!(
        ZkPari::<E>::verify(&recv_proof, &recv_vk, &recv_x),
        "recv proof rejected"
    );
    assert!(
        root_history.contains(&recv_x[6]),
        "revealed anchor must be in the ledger's root history"
    );
    assert_eq!(recv_x[1], ledger_bob.0, "statement must open Bob's account");
    assert_eq!(recv_x[2], ledger_bob.1, "statement must extend Bob's nullifier root");
    ledger_bob = (recv_x[3], recv_x[4]); // swap in com' and rootnull'
    assert_eq!(ledger_bob.0, bob.com_new(), "credited commitment must open to b + v");
    assert_eq!(
        ledger_bob.1,
        bob_null_tree.root(),
        "ledger root must match Bob's updated tree"
    );

    // 3. Tampered statements must be rejected. (A double-receive cannot even
    //    be witnessed: the indexed tree rejects duplicate keys, and no low
    //    leaf satisfying the in-circuit ordering exists for a present key.)
    let mut bad = recv_x.clone();
    bad[5] = Fr::rand(rng); // different nullifier
    assert!(
        !ZkPari::<E>::verify(&recv_proof, &recv_vk, &bad),
        "tampered nullifier accepted"
    );
    let mut bad = recv_x.clone();
    bad[6] = Fr::rand(rng); // anchor outside the root history
    assert!(
        !ZkPari::<E>::verify(&recv_proof, &recv_vk, &bad),
        "tampered receipt root accepted"
    );
    let mut bad = recv_x.clone();
    bad[4] = Fr::rand(rng); // wrong post-insertion nullifier root
    assert!(
        !ZkPari::<E>::verify(&recv_proof, &recv_vk, &bad),
        "tampered nullifier root accepted"
    );
    let mut bad = send_x.clone();
    bad[4] = Fr::rand(rng); // wrong post-insertion tag root
    assert!(
        !ZkPari::<E>::verify(&send_proof, &send_vk, &bad),
        "tampered tag root accepted"
    );

    // Keep the linter honest about the updated ledger state.
    let _ = ledger_alice;

    println!("  send + receive verified, ledger roots swapped, tampering rejected");
    println!();
}
