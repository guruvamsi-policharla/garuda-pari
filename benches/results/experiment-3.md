# Experiment 3 (phase 3a) — payment circuits (BLS12-381)

Machine: Apple M5 Pro, 18 cores
Date: 2026-09-02 (previous runs 2026-08-26/27/31; this run adds the
      operation-hiding R_op rows and drops the committed-input-based
      confidential-transfer rows, removed with committed inputs)
Commit: 7b1657e
Profile: `cargo bench` (release)
Threads: **single-threaded** (the default). Set `ZKPARI_BENCH_THREADS=0`
         for all cores, or `=N` for N.
Sampling: prove = median of 5; verify = mean over a >=100 ms budget loop;
          keygen = a single sample.

## Circuits

The paper's private-transfer relations, now living in `src/circuits/`
behind the `circuits` feature:

- **Private transfer** (the paper's R_send / R_recv): unlinkable payments.
  An account's entire public state is **one hash commitment**
  `Com_acct(b, kappa, rootnull; r)` — three data slots: balance, PRF key,
  and the root of the owner's indexed nullifier tree — opened in-circuit as
  a public input. **Zero** committed-input blocks, so the proof is
  2 G1 + 1 F (128 B) and verification is 3 pairings regardless of relation.
  Nullifiers are derived from the receipt's MMR position under the
  *receiver's* key (`nullifier = CRPRF_kappa(recv, pos)`, mirroring
  Sapling), which moves every hash except the commitment openings out of
  R_send:
  - R_send: three Pedersen commitment openings — `com -> (b, kappa,
    rootnull)`, `com' -> (b - v, kappa, rootnull)` with the *same* root
    witness (a send never touches the tree), `rho = Com_rec(v, Sen, Rec;
    r'')` — plus the `1 <= v <= b` range checks. **No tree, no PRF, no
    depth parameter.** Statement (paper order): `(Sen, com, com', rho)`.
  - R_recv: the same two account openings (old root in `com`, post-insertion
    root in `com'`) and the receipt opening, the MMR opening of `rho` at
    witnessed position `pos` under a revealed anchor (fixed at depth 40 —
    2^40 receipts of capacity, ~4 months of history at 100K TPS; the path's
    left/right ordering is driven by the bits of `pos`, so the proof binds
    the position), the in-circuit nullifier derivation (the scheme's single
    SHA-256 call), **and the in-circuit nullifier-tree insertion**. The
    nullifier *and both tree roots* are witnesses — nothing tree-related
    ever appears on the wire. Statement (paper order):
    `(Rec, com, com', rootrho)`.

  Both statements are 4 public values (|x| = 5 with the constant-one
  input). Deriving the nullifier from the unique MMR position (rather than
  from sender-chosen material) is the Faerie-Gold hedge: distinct receipts
  always carry distinct nullifiers, so no send can block another pending
  payment. Since the nullifier is position-derived under the receiver's
  key, the sender cannot evaluate it and never learns when (or whether)
  its payment is claimed.

- **Operation hiding** (the paper's R_op, §"Hiding the operation type"):
  one circuit for both operations over the shared statement
  `(A, com, com', rho, rootrho)` (|x| = 6), with a witness bit selecting
  the branch. The selector muxes the balance delta, the committed
  nullifier roots, and the published receipt's preimage, and gates the
  receive-only equalities (the MMR root check and the indexed-insert root
  checks). Receipts gain a trailing *type* slot: sends publish their real
  receipt with type 1, receives publish a dummy fixed to type 0, and the
  in-circuit consumed receipt pins type = 1 — so dummies are unspendable
  and the MMR grows by exactly one leaf per operation either way. Both
  branches synthesize the **identical** constraint count (asserted in the
  bench gate and unit tests), so neither the wire format nor the proving
  cost leaks the operation type.

### Hash instantiation: the Sapling split

The scheme's hashes (`src/circuits/hasher.rs`) follow Sapling:
**Pedersen over Jubjub** for everything structural — Merkle nodes,
indexed-tree leaves, and the account/receipt commitments — and **SHA-256**
for the single CRPRF call site (nullifier derivation; R_recv pays it once,
R_send has no PRF call at all). The split exists because the two roles
need different properties: the trees and commitments need collision
resistance / binding, where Pedersen is ~14x cheaper in-circuit than
SHA-256; the nullifier site needs genuine pseudorandomness under a secret
key, which Pedersen lacks — by bit-linearity, nullifiers at known
positions would differ by *public* generator combinations, so learning any
one nullifier (or key-independent structure of the tree) would reveal all
of the account's others. Sapling resolves this identically (Pedersen trees
+ BLAKE2s nullifier PRF; we use SHA-256 in the same role).

Both primitives share a byte serialization: a 1-byte domain tag plus the
canonical 32-byte LE encoding of each field element (the in-circuit
`to_bytes_le` enforces canonical decomposition). Pedersen digests are the
x-coordinate of a fixed-base MSM with one 8-bit window of doubling powers
per input byte, sliced to the exact preimage length so padding is never
paid for (~5.6 R1CS/bit); x-truncation (P vs -P) stays collision-resistant
under DL. Both commitments now hash 4 field elements (129-byte preimages).
SHA-256 digests are truncated to their low 253 bits so native and
in-circuit outputs agree; with fixed-length input and the key in front,
SHA-256(dom || kappa || pos) is a standard PRF instantiation (the domain
byte is the paper's `recv` label). Deployment notes: benchmark generators
come from a fixed seed (real ones would be nothing-up-my-sleeve), and the
commitment randomness windows would use a doubling chain of a single base
so the randomness term is exactly r*H (Sapling's windowed Pedersen
commitment) — identical circuit cost.

### In-circuit `AccVerifyInsert` (R_recv only)

The per-account nullifier tree is a *user-maintained* **indexed Merkle
tree** (sorted linked list in the leaves); its root lives *inside* the
account commitment, so the ledger stores nothing about it. The paper's
`mt.AccVerifyInsert(rootnull, nullifier, pi_mt) = rootnull'` is verified
**inside the SNARK** rather than natively:

- The low-leaf argument (`low.value < key < low.next_value`, or
  `next_value = 0` at the list maximum) proves *non-membership*, so
  double-receives are unsatisfiable — the tree owner is the adversary here,
  and an append-only tree would not give this.
- Cost: four hash-chains of `depth` node hashes (old low leaf under `root`,
  updated low leaf and the empty slot under the intermediate root, new leaf
  under `root'`), three leaf hashes, and two 128-bit comparisons. Tree keys
  are the low 128 bits of the hash-output nullifier (full field elements
  cannot be order-compared soundly without decomposition anyway; 128 bits
  keeps collisions negligible). Measured marginal cost: ~12.7k R1CS per
  tree level (4 Pedersen node hashes at ~3.2k each).
- What the ledger does per transaction: verify the proof and
  compare-and-swap the account's **single 32-byte commitment**. No
  hashing, no `pi_mt` (~depth x 32 B) on the wire, no nullifier, and no
  tree root either. Since ZK-Pari batch verification is independent of
  circuit size (experiment 2), the added constraints cost the ledger
  nothing at the margin — only the prover pays.
- Ledger state stays O(accounts): **32 B per account** (one commitment) +
  the receipt-MMR frontier and bounded root history. At 100K TPS a
  validator-held nullifier set would grow ~1.9 TB/week (60.5 G inserts x
  32 B, unprunable); this design grows only with registrations.

Nullifier-tree depth is swept over {10, 20} (2^10 / 2^20 lifetime receipts
per account); only R_recv has a depth parameter. What stays native: the
ledger's root-history check on the revealed receipt anchor (`rootrho in T`,
the W most recently recorded roots — a set lookup; hence `rootrho` is a
public input to R_recv, and there is no validator signature at all),
receiver registration, and R_reg entirely.

The gadget circuits are plain R1CS (ark-r1cs-std) fed through the
R1CS-to-SR1CS adapter: `r1cs` is what the gadgets emit, `sr1cs` is what the
prover pays for (~2x), and the FFT domain rounds `sr1cs` up to a power of
two. `prove` includes circuit synthesis, as everywhere in these benches.

Before the table, the bench runs an end-to-end flow (receipts depth 40,
nullifier tree depth 10) as a correctness gate: Alice sends 300 to Bob with
a real R_send prove/verify, the ledger compare-and-swaps her single
commitment, appends `rho` to the receipt MMR, and records the new root in
its history; Bob locates `rho`'s position in the public log, derives the
nullifier from `(kappa_Bob, recv, pos)`, inserts it into his local indexed
tree, recommits `(b + v, kappa, rootnull')`, and proves R_recv against the
recorded anchor — the submission is `(Rec, com', rootrho, proof)`, with no
nullifier and no tree root on the wire. The gate then checks that
tampering with *any* of the 8 public-input slots (4 recv + 4 send) is
rejected, that a claim of the same receipt at a wrong position is both
unwitnessable (the constraint system is unsatisfiable — the MMR opening
pins `rho` to its true position, and the position pins the nullifier) and
rejected as a forged proof, and that replaying the receive against Bob's
updated commitment is rejected.

## Results (2026-09-02, `cargo bench --bench circuits`)

```
  circuit                  │    r1cs │    sr1cs │   domain │ |x| │ keygen ms │ prove ms │ verify us │ proof B
  ─────────────────────────┼─────────┼──────────┼──────────┼─────┼───────────┼──────────┼───────────┼────────
  R_send                   │   19293 │    38595 │    65536 │   5 │    1896.8 │   1577.1 │     747.5 │    128
  R_recv d10               │  370020 │   740049 │  1048576 │   5 │   28672.8 │  20867.5 │     760.3 │    128
  R_recv d20               │  497360 │   994729 │  1048576 │   5 │   31594.8 │  21896.1 │     750.0 │    128
  R_op d10                 │  378369 │   756749 │  1048576 │   6 │   30677.4 │  21022.7 │     742.5 │    128
  R_op d20                 │  505709 │  1011429 │  1048576 │   6 │   30553.9 │  21558.5 │     756.2 │    128

  |x| counts the leading constant 1. Proofs are 2 G1 + 1 F.
```

Where the constraints go: R_send is exactly its three Pedersen openings
(two 129-byte account commitments, one 129-byte receipt commitment, plus
the canonical byte decompositions of their inputs) and the range checks —
19.3k R1CS, landing in a **2^16 domain**, 16x smaller than R_recv's. In
R_recv, a Pedersen tree level is ~3.2k R1CS (x1 per receipt-path level =
~128k for the depth-40 opening, x4 per nullifier-tree level inside the
indexed insertion = ~12.7k/level), the single SHA-256 nullifier call is
~79k (2 compressions plus the byte decompositions of key and position),
and the commitments/leaf hashes fill the rest. R_op costs R_recv + 8,349
R1CS at either depth: it hashes two receipts instead of one (the published
receipt — real or dummy, over a muxed preimage — plus the consumed one),
both with the wider 5-slot preimage that carries the type slot, and adds
the selector muxes and conditional gating, which are cheap. All heavy rows
land in the same 2^20 FFT domain — R_op d20 fits with ~3.5% headroom
(1,011,429 of 1,048,576) — which is why their prove times cluster at
21-22 s.

## Construction history

Two earlier variants of these relations were measured on the same machine
and hash split.

**2026-08-27 — position-derived nullifiers, tree roots as public inputs.**
Account state was a pair `(com, rootnull)` with `Com_acct(b, kappa; r)`
two-slot commitments; R_recv's statement carried both roots
(`|x| = 7`) and R_send's openings had no root slot:

```
  R_send (public-root)     │   16110 │    32229 │    32768 │   5 │    1112.8 keygen │    876.0 prove
  R_recv d10 (public-root) │  366837 │   733687 │  1048576 │   7 │   30195.5        │  20897.7
  R_recv d20 (public-root) │  494177 │   988367 │  1048576 │   7 │   31885.2        │  22607.0
```

Moving the root inside the commitment costs each account opening one more
32-byte slot: +3,184 R1CS in both relations. For R_recv that is noise
(same 2^20 domain, prove within 0.2%); for R_send it pushed 32,229 ->
38,597 SR1CS across the 2^15 boundary, doubling the FFT domain and the
prove time (876 ms -> 1,523 ms). In exchange the account's public state
drops to one 32-byte commitment, R_recv's statement loses two elements,
and sends stop revealing that the tree was untouched (a prerequisite for
the op-hiding variant, where no padding insertions are needed).

**2026-08-26 — sender-derived nullifiers (tag-tree variant).** The
nullifier came from sender-chosen material, which forced a tag-tree
insertion and *two* SHA-256 PRF calls into R_send and kept the nullifier
in R_recv's statement:

```
  R_send d10 (old)         │  324584 │   649183 │  1048576 │   8 │   30382.1 keygen │  20826.8 prove
  R_send d20 (old)         │  451924 │   903863 │  1048576 │   8 │   32871.3        │  22193.2
  R_recv d10 (old)         │  287811 │   575637 │  1048576 │   8 │   29915.6        │  21899.9
  R_recv d20 (old)         │  415151 │   830317 │  1048576 │   8 │   31702.1        │  23012.9
```

Relative to that starting point, the current construction cuts R_send by
~17x in R1CS and ~14x in prove time (20.8 s -> 1.52 s), at the price of
one SHA-256 call added to R_recv (+79k R1CS, prove within noise — same
FFT domain). Per payment (one send + one receive), total prover work
dropped from 42.7 s to 22.5 s at d10.

## Hash ablation history

Before settling on the Sapling split, the *tag-tree* variant's relations
were measured under uniform single-hash instantiations (same statements,
tree shapes, and proof sizes; only the hash differs). Poseidon rows are
from a clean run; SHA-256 rows carry a ~5-10% error bar (a duplicate
process ran concurrently for part of that measurement); Pedersen-only rows
were constraint-counted but not timed:

```
  R_send poseidon d10      │   15682 │    31379 │    32768 │  1240.9 keygen │   1018.9 prove
  R_send poseidon d20      │   27422 │    54859 │    65536 │  2279.1        │   1880.8
  R_recv poseidon d10      │   26853 │    53721 │    65536 │  2263.0        │   1937.2
  R_recv poseidon d20      │   38593 │    77201 │   131072 │  4403.1        │   3391.8
  R_send pedersen d10      │  169998 │       (constraint-counted only)
  R_recv pedersen d10      │  287811 │       (= tag-tree hybrid R_recv: no PRF call)
  R_send sha256 d10        │ 3924651 │  7849317 │  8388608 │ 256622.8       │ 204336.4
  R_recv sha256 d10        │ 6985358 │ 13970731 │ 16777216 │ 476294.1       │ 392335.9
```

Per unit: one Poseidon permutation is ~294 R1CS, one Pedersen tree level
~3.2k, one SHA-256 compression ~40.4k (a SHA tree level needs two).
Verification and proof size are identical across all instantiations
(~0.72-0.83 ms, 128 B) — hash and construction choices live entirely on
the prover side of the ledger boundary.

For reference, the same relations *without* the in-circuit insertion (the
native-`pi_mt` variant, measured earlier under Poseidon on the same
machine): R_send was 1,970 R1CS / 159 ms and R_recv (receipt depth 32)
10,789 R1CS / 987 ms.

## Reading the numbers

- A private *send* is ~1.6 s single-threaded (2^16 domain) — cheap enough
  to be interactive. The receive carries all the heavy machinery
  (~21-22 s: the depth-40 receipt opening, the SHA-256 nullifier, and the
  indexed-tree insertion) but is asynchronous by design: Bob can claim
  whenever he likes, against any anchor in the ledger's retained history.
  These are client-side costs and parallelize.
- Hiding the operation type costs a receive almost nothing (+2.2% R1CS,
  prove within noise) — but it costs a *send* the full receive machinery,
  since every operation now proves the R_op circuit (~21 s instead of
  ~1.6 s). That is the real price of operation hiding, and it is a
  deployment choice: run R_send/R_recv for cheap sends and visible
  operation types, or R_op for full uniformity.
- Verification is flat (~0.74-0.76 ms) and *independent of everything*:
  3 pairings + a 5- or 6-element public-input evaluation.
  The wire format per operation matches the paper's submit lines —
  `(Sen, com', rho)` for a send, `(Rec, com', rootrho)` for a receive,
  `(A, com', rho, rootrho)` under operation hiding (`com` comes from
  ledger state; no nullifier and no tree root ever appear) — three or four
  field elements plus the 128 B proof. No insertion proof, no receipt
  path.
- Trade summary for moving `AccVerifyInsert` in-circuit: the prover carries
  the 4-chain insertion (~12.7k R1CS per nullifier-tree level); the ledger
  sheds ~2-3 x depth hashes per transaction and ~0.4-1 KB per transaction
  on the wire, while its per-proof batch-verify cost is unchanged and its
  per-account state is a single 32-byte commitment.
