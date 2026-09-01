# Experiment 3 (phase 3a) — payment circuits (BLS12-381)

Machine: Apple M5 Pro, 18 cores
Date: 2026-08-27
Commit: 3e9900b + working tree
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
  Account commitments are hash values `Com_acct(b, kappa, root_null; r)` —
  three data slots: balance, PRF key, and the root of the owner's indexed
  nullifier tree. Registration commits the empty-tree root. Receipt
  commitments are `Com_rec(v, S, R; r'')` — three data slots, no nullifier
  inside. Opened in-circuit as public inputs. **Zero** committed-input
  blocks, so the proof is 2 G1 + 1 F (128 B) and verification is 3 pairings
  regardless of relation. An account's entire public state is one
  commitment. Nullifiers are derived from the receipt's MMR position under
  the *receiver's* key (`nullifier = CRPRF_kappa(recv, pos)`, mirroring
  Sapling), which moves every hash except the commitment openings out of
  R_send:
  - R_send: three Pedersen commitment openings — `com -> (b, kappa, root_null)`,
    `com' -> (b - v, kappa, root_null)` with key and root unchanged,
    `rho = Com_rec(v, S, R; r'')` — plus the `1 <= v <= b` range checks.
    **No tree, no PRF, no depth parameter.** Statement (paper order):
    `(S, com, com', rho)`.
  - R_recv: the same two account openings (now carrying `root_null` /
    `root_null'`) and the receipt opening, the MMR opening of `rho` at
    witnessed position `pos` under a revealed anchor (fixed at depth 40 —
    2^40 receipts of capacity, ~4 months of history at 100K TPS; the path's
    left/right ordering is driven by the bits of `pos`, so the proof binds
    the position), the in-circuit nullifier derivation (the scheme's single
    SHA-256 call), **and the in-circuit nullifier-tree insertion**. The
    nullifier *and both tree roots* live in the witness — they never appear
    on the wire. Statement (paper order): `(R, com, com', root_rho)`.

  Deriving the nullifier from the unique MMR position (rather than from
  sender-chosen material) is the Faerie-Gold hedge: distinct receipts always
  carry distinct nullifiers, so no send can block another pending payment.
  Since the nullifier is position-derived under the receiver's key, the
  sender cannot evaluate it and never learns when (or whether) its payment
  is claimed.

### Hash instantiation: the Sapling split

The scheme's hashes (`benches/common/private/hasher.rs`) follow Sapling:
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
under DL. SHA-256 digests are truncated to their low 253 bits so native
and in-circuit outputs agree; with fixed-length input and the key in
front, SHA-256(dom || kappa || pos) is a standard PRF instantiation (the
domain byte is the paper's `recv` label). Deployment notes: benchmark
generators come from a fixed seed (real ones would be
nothing-up-my-sleeve), and the commitment randomness windows would use a
doubling chain of a single base so the randomness term is exactly r*H
(Sapling's windowed Pedersen commitment) — identical circuit cost.

### In-circuit `AccVerifyInsert` (R_recv only)

The per-account nullifier tree is a *user-maintained* **indexed Merkle
tree** (sorted linked list in the leaves); its root lives *inside* the
account commitment. The paper's `mt.AccVerifyInsert(root_null, nullifier,
pi_mt) = root_null'` is verified **inside the SNARK** rather than natively:

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
- What the ledger does per transaction: compare `com` against the stored
  account commitment, swap in `com'`. No hashing, no `pi_mt` (~depth x 32 B)
  on the wire, no nullifier, and no tree root. Since ZK-Pari batch
  verification is independent of circuit size (experiment 2), the added
  constraints cost the ledger nothing at the margin — only the prover pays.
- Ledger state stays O(accounts): 32 B per account (`com`) + the
  receipt-MMR frontier and bounded root history. At 100K TPS a
  validator-held nullifier set would grow ~1.9 TB/week (60.5 G inserts x
  32 B, unprunable); this design grows only with registrations.

Nullifier-tree depth is swept over {10, 20} (2^10 / 2^20 lifetime receipts
per account); only R_recv has a depth parameter now. What stays native: the
ledger's root-history check on the revealed receipt anchor (`root_rho in T`,
the W most recently recorded roots — a set lookup; hence `root_rho` is a
public input to R_recv, and there is no validator signature at all),
receiver registration, and R_reg entirely.

The gadget circuits are plain R1CS (ark-r1cs-std) fed through the
R1CS-to-SR1CS adapter: `r1cs` is what the gadgets emit, `sr1cs` is what the
prover pays for (~2x), and the FFT domain rounds `sr1cs` up to a power of
two. `prove` includes circuit synthesis, as everywhere in these benches.

Before the table, the bench runs an end-to-end flow (receipts depth 40,
nullifier tree depth 10) as a correctness gate: Alice sends 300 to Bob with
a real R_send prove/verify, the ledger compare-and-swaps her (single)
commitment, appends `rho` to the receipt MMR, and records the new root in
its history; Bob locates `rho`'s position in the public log, derives the
nullifier from `(kappa_Bob, recv, pos)`, inserts it into his own indexed
tree, recommits `(b + v, kappa, root_null')`, and proves R_recv against the
recorded anchor. The receive submission is `(R, com', root_rho, proof)` —
no nullifier and no tree root on the wire. The gate then checks that
tampering with *any* of the 8 public-input slots (4 recv + 4 send) is
rejected, that a claim of the same receipt at a wrong position is both
unwitnessable (the constraint system is unsatisfiable — the MMR opening
pins `rho` to its true position, and the position pins the nullifier) and
rejected as a forged proof, and that replaying the same receive against
Bob's updated commitment is rejected (the old `com` no longer matches the
ledger).

## Results (`cargo bench --bench circuits`)

```
  circuit                  │    r1cs │    sr1cs │   domain │ |x| │ blocks │ keygen ms │ prove ms │ verify us │ proof B
  ─────────────────────────┼─────────┼──────────┼──────────┼─────┼────────┼───────────┼──────────┼───────────┼────────
  confidential range 32b   │       — │       34 │       64 │   1 │      1 │       7.6 │      4.9 │     857.6 │    176
  confidential range 64b   │       — │       66 │      128 │   1 │      1 │      10.6 │      8.1 │     847.7 │    176
  R_send                   │   19294 │    38597 │    65536 │   5 │      0 │    2133.1 │   1644.2 │     783.8 │    128
  R_recv d10               │  370021 │   740051 │  1048576 │   5 │      0 │   31895.1 │  22307.7 │     762.5 │    128
  R_recv d20               │  497361 │   994731 │  1048576 │   5 │      0 │   33526.9 │  23252.5 │     779.7 │    128

  |x| counts the leading constant 1. Proofs are (2 + blocks) G1 + 1 F.
```

Where the constraints go: R_send is exactly its three Pedersen openings
(two 129-byte account commitments — now matching the receipt's three data
slots plus randomness — plus the canonical byte decompositions of their
inputs) and the range checks — 19.3k R1CS, landing in a **2^16 domain**.
Folding `root_null` into the account hash added one 32-byte Pedersen slot
to each of the two account openings (~3.2k R1CS), which pushed SR1CS just
over 2^15 (38,597 of 32,768) and doubled the FFT domain relative to the
two-slot account commitment. Still 16x smaller than R_recv's 2^20. In
R_recv, a Pedersen tree level is ~3.2k R1CS (x1 per receipt-path level =
~128k for the depth-40 opening, x4 per nullifier-tree level inside the
indexed insertion = ~12.7k/level), the single SHA-256 nullifier call is
~79k (2 compressions plus the byte decompositions of key and position),
and the commitments/leaf hashes fill the rest. Both R_recv rows land in
the same 2^20 FFT domain (d20: 994,731 of 1,048,576), which is why their
prove times cluster at 22-23 s. R_recv's statement shrank from 6 to 4
public inputs (`|x|` 7 → 5), matching R_send.

## Construction history

Putting `root_null` inside the account commitment (this run, same machine
and hash split) made the account's entire public state one hash. Against
the immediately previous numbers (two-slot `Com_acct(b, kappa; r)`, tree
roots public in R_recv):

```
  R_send (prev)            │   16110 │    32229 │    32768 │   5 │    1112.8 keygen │    876.0 prove
  R_recv d10 (prev)        │  366837 │   733687 │  1048576 │   7 │   30195.5        │  20897.7
  R_recv d20 (prev)        │  494177 │   988367 │  1048576 │   7 │   31885.2        │  22607.0
```

The extra Pedersen slot costs ~3.2k R1CS on both relations. R_send's prove
time roughly doubled (876 ms → 1.64 s) because SR1CS crossed 2^15 into a
**2^16 domain**; R_recv stayed in 2^20, so prove is within noise. The
ledger dropped the per-account `root_null` field (64 B → 32 B) and R_recv's
on-wire statement lost two public inputs.

The construction before that (measured 2026-08-26, same machine and hash
split) derived the nullifier from sender-chosen material, which forced a
tag-tree insertion and *two* SHA-256 PRF calls into R_send and kept the
nullifier in R_recv's statement:

```
  R_send d10 (old)         │  324584 │   649183 │  1048576 │   8 │   30382.1 keygen │  20826.8 prove
  R_send d20 (old)         │  451924 │   903863 │  1048576 │   8 │   32871.3        │  22193.2
  R_recv d10 (old)         │  287811 │   575637 │  1048576 │   8 │   29915.6        │  21899.9
  R_recv d20 (old)         │  415151 │   830317 │  1048576 │   8 │   31702.1        │  23012.9
```

Moving nullifier derivation to the receiver (from the receipt's MMR
position) cut R_send by ~17x in R1CS and ~13x in prove time (20.8 s →
1.64 s at the current three-slot account commitment), at the price of one
SHA-256 call added to R_recv (+79k R1CS, prove within noise of the old
figure — same FFT domain). Since every payment is one send + one receive,
total prover work per payment roughly halved (42.7 s → 23.9 s at d10),
and the send-side latency (the interactive half) dropped ~13x.

## Hash ablation history

Before settling on the Sapling split, the *old* construction's relations
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
  R_recv pedersen d10      │  287811 │       (= old hybrid R_recv: no PRF call)
  R_send sha256 d10        │ 3924651 │  7849317 │  8388608 │ 256622.8       │ 204336.4
  R_recv sha256 d10        │ 6985358 │ 13970731 │ 16777216 │ 476294.1       │ 392335.9
```

Per unit: one Poseidon permutation is ~294 R1CS, one Pedersen tree level
~3.2k, one SHA-256 compression ~40.4k (a SHA tree level needs two).
Amusingly, the *new* all-hashing-on-the-receiver R_send (16.1k R1CS,
876 ms) now matches the old Poseidon-everything R_send d10 (15.7k,
1019 ms) — the construction change bought on the send side what the
SNARK-friendly hash used to. Verification and proof size are identical
across all instantiations (~0.75-0.83 ms, 128 B) — hash and construction
choices live entirely on the prover side of the ledger boundary.

For reference, the same relations *without* the in-circuit insertion (the
native-`pi_mt` variant, measured earlier under Poseidon on the same
machine): R_send was 1,970 R1CS / 159 ms and R_recv (receipt depth 32)
10,789 R1CS / 987 ms.

## Reading the numbers

- A confidential transfer needs two 64-bit range proofs (amount + remaining
  balance), so the prover-side cost of a full transfer is ~16 ms
  single-threaded; the two `C_ci` values double as the ledger commitments.
- A private *send* is now ~1.64 s single-threaded (**2^16 domain**) — still
  cheap enough to be interactive. The receive carries all the heavy
  machinery (~22-23 s: the depth-40 receipt opening, the SHA-256 nullifier,
  and the indexed-tree insertion) but is asynchronous by design: Bob can
  claim whenever he likes, against any anchor in the ledger's retained
  history. These are client-side costs and parallelize.
- Verification is flat (~0.76-0.78 ms) and *independent of everything*:
  with zero blocks it is 3 pairings + a small public-input evaluation. The
  wire format per operation matches the paper's submit lines —
  `(S, com', rho)` for a send, `(R, com', root_rho)` for a receive (`com`
  comes from ledger state; no nullifier and no tree root ever appear) —
  plus the 128 B proof. No insertion proof, no receipt path.
- Trade summary for moving `AccVerifyInsert` in-circuit: the prover carries
  the 4-chain insertion (~12.7k R1CS per nullifier-tree level); the ledger
  sheds ~2-3 x depth hashes per transaction and ~0.4-1 KB per transaction
  on the wire, while its per-proof batch-verify cost is unchanged. Folding
  the tree root into the account commitment additionally drops 32 B of
  per-account ledger state and two public inputs from R_recv.
