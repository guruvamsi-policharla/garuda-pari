# Experiment 3 (phase 3a) — payment circuits (BLS12-381)

Machine: Apple M5 Pro, 18 cores
Date: 2026-08-25
Commit: 74b143c + working tree
Profile: `cargo bench` (release)
Threads: **single-threaded** (the default). Set `ZKPARI_BENCH_THREADS=0`
         for all cores, or `=N` for N.
Sampling: prove = median of 5; verify = mean over a >=100 ms budget loop;
          keygen = a single sample.

## Circuits

Two payment flavours, one table:

- **Confidential transfer** (Zether-style): a native-SR1CS range proof on the
  amount, declared as the single committed-input block, so the proof's `C_ci`
  *is* the ledger's Pedersen commitment. Balances chain homomorphically under
  the one CRS basis. Proof = 3 G1 + 1 F (176 B); since `C_ci` is ledger
  state, the incremental proof material is 2 G1 + 1 F. Bit width swept over
  {32, 64}. See `examples/confidential_transfer.rs` for the full flow.

- **Private transfer** (the paper's R_send / R_recv): unlinkable payments.
  Account commitments are Poseidon values `Com_acct(b, kappa; r)` opened
  in-circuit as public inputs — **zero** committed-input blocks, so the proof
  is 2 G1 + 1 F (128 B) and verification is 3 pairings regardless of relation.
  - R_send: two account openings, the pay/pad PRFs, the receipt commitment
    (5 Poseidon calls), the `1 <= v <= b` range checks, **and the in-circuit
    tag-tree insertion**. Statement (paper order):
    `(Sen, com, com', roottag, roottag', rho, tag)`.
  - R_recv: two account openings, the receipt opening, a Poseidon Merkle
    membership path under a revealed anchor (fixed at depth 40 — 2^40
    receipts of capacity, ~4 months of history at 100K TPS), **and
    the in-circuit nullifier-tree insertion**. Statement (paper order):
    `(Rec, com, rootnull, com', rootnull', nullifier, rootrho)`.

### In-circuit `AccVerifyInsert`

The per-account nullifier/tag trees are *user-maintained* **indexed Merkle
trees** (sorted linked list in the leaves); the ledger stores only their
32-byte roots. The paper's `mt.AccVerifyInsert(root, key, pi_mt) = root'`
is verified **inside the SNARK** rather than natively:

- The low-leaf argument (`low.value < key < low.next_value`, or
  `next_value = 0` at the list maximum) proves *non-membership*, so
  double-receives are unsatisfiable — the tree owner is the adversary here,
  and an append-only tree would not give this.
- Cost: four hash-chains of `depth` permutations (old low leaf under `root`,
  updated low leaf and the empty slot under the intermediate root, new leaf
  under `root'`), three leaf hashes, and two 128-bit comparisons. Tree keys
  are the low 128 bits of the Poseidon-output nullifier/tag (full field
  elements cannot be order-compared soundly without decomposition anyway;
  128 bits keeps collisions negligible). Measured marginal cost:
  ~1,170 R1CS per tree level.
- What the ledger does per transaction: compare `root` against its stored
  root, swap in `root'`. No hashing, no `pi_mt` (~depth x 32 B) on the wire.
  Since ZK-Pari batch verification is independent of circuit size
  (experiment 2), the added constraints cost the ledger nothing at the
  margin — only the prover pays.
- Ledger state stays O(accounts): 96 B per account `(com, rootnull,
  roottag)` + the receipt-MMR frontier. At 100K TPS a validator-held
  nullifier set would grow ~1.9 TB/week (60.5 G inserts x 32 B, unprunable);
  this design grows only with registrations.

Account-tree depth is swept over {10, 20} (2^10 / 2^20 lifetime payments per
account). What stays native: the ledger's root-history check on the revealed
receipt anchor (`rootrho in T`, the W most recently recorded roots — a set
lookup; hence `rootrho` is a public input to R_recv, and there is no
validator signature at all), receiver registration, and R_reg entirely.

Poseidon: width 5 (rate 4 + capacity 1), alpha = 5, 8 full / 60 partial
rounds, Grain-LFSR parameters; one config serves all commitments, PRFs, and
both tree node types (domain-separated by a constant first absorption).

The gadget circuits are plain R1CS (ark-r1cs-std) fed through the
R1CS-to-SR1CS adapter: `r1cs` is what the gadgets emit, `sr1cs` is what the
prover pays for (~2x), and the FFT domain rounds `sr1cs` up to a power of
two. `prove` includes circuit synthesis, as everywhere in these benches.

Before the table, the bench runs an end-to-end flow (receipts depth 40,
account trees depth 10) as a correctness gate: Alice sends 300 to Bob with a
real R_send prove/verify, the ledger compare-and-swaps `(com, roottag)`,
appends the receipt, and records the new root in its history; Bob
reconstructs the identical receipt from out-of-band data, inserts the
nullifier into his tree, and proves R_recv against the latest anchor; the
ledger checks the anchor is in its root history and swaps `(com, rootnull)`.
Tampered statements (nullifier, anchor, either post-insertion root) are
rejected.

## Results (`cargo bench --bench circuits`)

```
  circuit                  │  r1cs │ sr1cs │ domain │ |x| │ blocks │ keygen ms │ prove ms │ verify us │ proof B
  ─────────────────────────┼───────┼───────┼────────┼─────┼────────┼───────────┼──────────┼───────────┼────────
  confidential range 32b   │     — │    34 │     64 │   1 │      1 │       7.1 │      4.8 │     824.7 │    176
  confidential range 64b   │     — │    66 │    128 │   1 │      1 │      10.4 │      7.9 │     823.0 │    176
  R_send tag d10           │ 15682 │ 31379 │  32768 │   8 │      0 │    1240.9 │   1018.9 │     736.2 │    128
  R_send tag d20           │ 27422 │ 54859 │  65536 │   8 │      0 │    2279.1 │   1880.8 │     745.1 │    128
  R_recv rcpt40 null d10   │ 26853 │ 53721 │  65536 │   8 │      0 │    2263.0 │   1937.2 │     769.9 │    128
  R_recv rcpt40 null d20   │ 38593 │ 77201 │ 131072 │   8 │      0 │    4403.1 │   3391.8 │     769.6 │    128

  |x| counts the leading constant 1. Proofs are (2 + blocks) G1 + 1 F.
```

For reference, the same relations *without* the in-circuit insertion (the
native-`pi_mt` variant, measured earlier on the same machine): R_send was
1,970 R1CS / 159 ms and R_recv (receipt depth 32) 10,789 R1CS / 987 ms. The
insertion adds ~13.7k R1CS at depth 10 (+~1,170 per extra level) — i.e. the
in-circuit `AccVerifyInsert` dominates R_send and roughly doubles R_recv.
Deepening the receipt tree from 32 to 40 added ~2.4k R1CS (~294 per level,
one Poseidon permutation each) without crossing an FFT-domain boundary, so
R_recv prove times moved by only ~0.1 s.

## Reading the numbers

- A confidential transfer needs two 64-bit range proofs (amount + remaining
  balance), so the prover-side cost of a full transfer is ~16 ms
  single-threaded; the two `C_ci` values double as the ledger commitments.
- Private-transfer proving is ~1-2 s (R_send) and ~2-3.5 s (R_recv)
  single-threaded, dominated by the indexed-tree insertion and, for R_recv,
  the depth-40 receipt path. These are client-side costs and parallelize.
- Verification is flat (~0.75 ms) and *independent of everything*: with zero
  blocks it is 3 pairings + an 8-element public-input evaluation. The wire
  format per operation matches the paper's submit line — 5 field elements
  (`(Sen, com', roottag', rho, tag)` or `(Rec, com', rootnull', nf,
  rootrho)`; `com` and the pre-roots come from ledger state) + the 128 B
  proof — no insertion proof.
- Trade summary for moving `AccVerifyInsert` in-circuit: prover pays ~0.9 s
  (d10) to ~1.7 s (d20) extra per operation; the ledger sheds ~2-3 x depth
  Poseidon hashes per transaction (~3-9 cores' worth at 100K TPS) and
  ~0.4-1 KB per transaction on the wire, while its per-proof batch-verify
  cost is unchanged.
