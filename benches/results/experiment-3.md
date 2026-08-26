# Experiment 3 (phase 3a) — payment circuits (BLS12-381)

Machine: Apple M5 Pro, 18 cores
Date: 2026-08-26
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
  Account commitments are hash values `Com_acct(b, kappa; r)` opened
  in-circuit as public inputs — **zero** committed-input blocks, so the proof
  is 2 G1 + 1 F (128 B) and verification is 3 pairings regardless of relation.
  - R_send: two account openings, the pay/pad PRFs, the receipt commitment
    (5 hash calls), the `1 <= v <= b` range checks, **and the in-circuit
    tag-tree insertion**. Statement (paper order):
    `(Sen, com, com', roottag, roottag', rho, tag)`.
  - R_recv: two account openings, the receipt opening, a Merkle
    membership path under a revealed anchor (fixed at depth 40 — 2^40
    receipts of capacity, ~4 months of history at 100K TPS), **and
    the in-circuit nullifier-tree insertion**. Statement (paper order):
    
    `(Rec, com, rootnull, com', rootnull', nullifier, rootrho)`.

### Hash instantiation: the Sapling split

The scheme's hashes (`benches/common/private/hasher.rs`) follow Sapling:
**Pedersen over Jubjub** for everything structural — Merkle nodes,
indexed-tree leaves, and the account/receipt commitments — and **SHA-256**
for the two CRPRF call sites (nullifier and tag derivation; R_send pays
both, R_recv has no PRF call at all). The split exists because the two
roles need different properties: the trees and commitments need collision
resistance / binding, where Pedersen is ~14x cheaper in-circuit than
SHA-256; the PRF sites need genuine pseudorandomness, which Pedersen lacks
— by bit-linearity the tag and nullifier points (identical preimages up to
the 1-byte domain tag) would differ by the public constant `G_pad - G_pay`,
making published tags linkable to revealed nullifiers. Sapling resolves
this identically (Pedersen trees + BLAKE2s PRFs; we use SHA-256 in the
same role).

Both primitives share a byte serialization: a 1-byte domain tag plus the
canonical 32-byte LE encoding of each field element (the in-circuit
`to_bytes_le` enforces canonical decomposition). Pedersen digests are the
x-coordinate of a fixed-base MSM with one 8-bit window of doubling powers
per input byte, sliced to the exact preimage length so padding is never
paid for (~5.6 R1CS/bit); x-truncation (P vs -P) stays collision-resistant
under DL. SHA-256 digests are truncated to their low 253 bits so native
and in-circuit outputs agree; with fixed-length input and the key in
front, SHA-256(dom || kappa || Sen || zeta) is a standard PRF
instantiation. Deployment notes: benchmark generators come from a fixed
seed (real ones would be nothing-up-my-sleeve), and the commitment
randomness windows would use a doubling chain of a single base so the
randomness term is exactly r*H (Sapling's windowed Pedersen commitment) —
identical circuit cost.

### In-circuit `AccVerifyInsert`

The per-account nullifier/tag trees are *user-maintained* **indexed Merkle
trees** (sorted linked list in the leaves); the ledger stores only their
32-byte roots. The paper's `mt.AccVerifyInsert(root, key, pi_mt) = root'`
is verified **inside the SNARK** rather than natively:

- The low-leaf argument (`low.value < key < low.next_value`, or
  `next_value = 0` at the list maximum) proves *non-membership*, so
  double-receives are unsatisfiable — the tree owner is the adversary here,
  and an append-only tree would not give this.
- Cost: four hash-chains of `depth` node hashes (old low leaf under `root`,
  updated low leaf and the empty slot under the intermediate root, new leaf
  under `root'`), three leaf hashes, and two 128-bit comparisons. Tree keys
  are the low 128 bits of the hash-output nullifier/tag (full field
  elements cannot be order-compared soundly without decomposition anyway;
  128 bits keeps collisions negligible). Measured marginal cost: ~12.7k
  R1CS per tree level (4 Pedersen node hashes at ~3.2k each).
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
  circuit                  │    r1cs │    sr1cs │   domain │ |x| │ blocks │ keygen ms │ prove ms │ verify us │ proof B
  ─────────────────────────┼─────────┼──────────┼──────────┼─────┼────────┼───────────┼──────────┼───────────┼────────
  confidential range 32b   │       — │       34 │       64 │   1 │      1 │       7.3 │      4.9 │     861.0 │    176
  confidential range 64b   │       — │       66 │      128 │   1 │      1 │      10.6 │      8.2 │     870.5 │    176
  R_send d10               │  324584 │   649183 │  1048576 │   8 │      0 │   30382.1 │  20826.8 │     771.6 │    128
  R_send d20               │  451924 │   903863 │  1048576 │   8 │      0 │   32871.3 │  22193.2 │     779.9 │    128
  R_recv d10               │  287811 │   575637 │  1048576 │   8 │      0 │   29915.6 │  21899.9 │     779.2 │    128
  R_recv d20               │  415151 │   830317 │  1048576 │   8 │      0 │   31702.1 │  23012.9 │     778.4 │    128

  |x| counts the leading constant 1. Proofs are (2 + blocks) G1 + 1 F.
```

Where the constraints go: a Pedersen tree level is ~3.2k R1CS (x4 per
account-tree level inside the indexed insertion, x1 per receipt-path
level), the two SHA-256 PRF calls in R_send are ~155k together (2
compressions each at ~40k, plus the byte decompositions), and the
commitments/leaf hashes fill the rest. R_recv d10 is exactly the
all-Pedersen circuit (287,811 = the Pedersen-only ablation figure);
R_send = Pedersen part + 155k of SHA-256. All four rows land in the same
2^20 FFT domain, which is why prove times cluster at 21-23 s despite the
r1cs spread — the FFT dominates once the domain is fixed.

## Hash ablation history

Before settling on the Sapling split, the same relations were measured
under uniform single-hash instantiations (same statements, tree shapes, and
proof sizes; only the hash differs). Poseidon rows are from a clean run;
SHA-256 rows carry a ~5-10% error bar (a duplicate process ran concurrently
for part of that measurement); Pedersen-only rows were constraint-counted
but not timed (bracketed by the Poseidon and hybrid timings):

```
  R_send poseidon d10      │   15682 │    31379 │    32768 │  1240.9 keygen │   1018.9 prove
  R_send poseidon d20      │   27422 │    54859 │    65536 │  2279.1        │   1880.8
  R_recv poseidon d10      │   26853 │    53721 │    65536 │  2263.0        │   1937.2
  R_recv poseidon d20      │   38593 │    77201 │   131072 │  4403.1        │   3391.8
  R_send pedersen d10      │  169998 │       (constraint-counted only)
  R_recv pedersen d10      │  287811 │       (= hybrid R_recv: no PRF call)
  R_send sha256 d10        │ 3924651 │  7849317 │  8388608 │ 256622.8       │ 204336.4
  R_recv sha256 d10        │ 6985358 │ 13970731 │ 16777216 │ 476294.1       │ 392335.9
```

Per unit: one Poseidon permutation is ~294 R1CS, one Pedersen tree level
~3.2k, one SHA-256 compression ~40.4k (a SHA tree level needs two). So
relative to Poseidon-everything, the Sapling split costs the prover ~11-21x
(prove 1-3.4 s -> 21-23 s); relative to SHA-256-everything it saves ~10-18x
(204-392 s -> 21-23 s). Verification and proof size are identical across
all instantiations (~0.78 ms, 128 B, same 8-element statement) — the hash
choice lives entirely on the prover side of the ledger boundary. The split
buys standard assumptions (DL on Jubjub + SHA-256) instead of trusting an
algebraic hash for everything; Poseidon-everything remains the datapoint
for the SNARK-friendly end of the spectrum.

For reference, the same relations *without* the in-circuit insertion (the
native-`pi_mt` variant, measured earlier under Poseidon on the same
machine): R_send was 1,970 R1CS / 159 ms and R_recv (receipt depth 32)
10,789 R1CS / 987 ms.

## Reading the numbers

- A confidential transfer needs two 64-bit range proofs (amount + remaining
  balance), so the prover-side cost of a full transfer is ~16 ms
  single-threaded; the two `C_ci` values double as the ledger commitments.
- Private-transfer proving is ~21-23 s single-threaded across the board
  (everything sits in the same 2^20 domain), dominated by the indexed-tree
  insertion, the depth-40 receipt path (R_recv), and the two SHA-256 PRFs
  (R_send). These are client-side costs and parallelize.
- Verification is flat (~0.78 ms) and *independent of everything*: with zero
  blocks it is 3 pairings + an 8-element public-input evaluation. The wire
  format per operation matches the paper's submit line — 5 field elements
  (`(Sen, com', roottag', rho, tag)` or `(Rec, com', rootnull', nf,
  rootrho)`; `com` and the pre-roots come from ledger state) + the 128 B
  proof — no insertion proof.
- Trade summary for moving `AccVerifyInsert` in-circuit: the prover carries
  the 4-chain insertion (~12.7k R1CS per account-tree level); the ledger
  sheds ~2-3 x depth hashes per transaction and ~0.4-1 KB per transaction
  on the wire, while its per-proof batch-verify cost is unchanged.
