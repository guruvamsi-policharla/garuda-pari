# Private Transfers with Hidden Amounts (ZK-Pari)

This document explains the `private_transfer` example, which demonstrates a
Zether-like private payment system built on ZK-Pari (Pari with
vanishing-polynomial masks and committed inputs).

Run the example:

```bash
cargo run --release --example private_transfer -p zkpari
```

## Core Idea

In a normal payment system, balances are stored in plaintext. In Zether,
balances are stored as **Pedersen commitments**.

ZK-Pari splits the assignment into ordinary public inputs, **committed
inputs**, and private witnesses. The committed inputs are grouped into
independently committed *blocks* (this example uses a single block; the
batched example below uses two), and each block `j` gets its own commitment
in the proof:

```
C_ci_j = sum_i x_i * Sigma_ci_j[i] + rho_ci_j * Gamma_ci_j
```

with CRS basis

| CRS element | Value                                        | Role     |
|-------------|----------------------------------------------|----------|
| `Sigma_ci_j[i]` | `((alpha a_i(tau) + beta b_i(tau))/delta_j) G` | Encodes the i-th committed value |
| `Gamma_ci_j`    | `(beta v_K(tau)/delta_j) G`                    | Blinding |

This **is** a standard Pedersen vector commitment, and it is exactly the
ledger object we need: range proofs and balance commitments come for free
from the same proof. With one committed input (the 64-bit value being
range-proved), the proof's `C_ci` is a 2-generator Pedersen commitment to the
transfer value.

## How zero-knowledge works (vanishing-polynomial masks)

Unlike the earlier hiding-channel construction (separate `gamma`-direction),
all hiding lives in **vanishing-polynomial directions**:

- The B-side polynomial is masked as `z_B(X) += rho_ci * v_K(X)`, where
  `rho_ci` is the *opening randomness of `C_ci`*. The `rho_ci * v_K`
  contribution carried by `C_ci` (via `Gamma_ci`) cancels against the
  `-rho_ci` constant the mask induces in the quotient.
- The A-side polynomial is masked as `z_A(X) += (eta_1 + eta_2 X) * v_K(X)`.
  The two mask directions `(alpha v_K(tau)/delta_w) G` and
  `(alpha tau v_K(tau)/delta_w) G` are committed inside `T`. They give the
  honest-verifier simulator independent uniform randomness at the challenge
  `r` and at the trapdoor `tau`, making the scheme statistically HVZK with
  simulation distance at most `1/(|F| - |K|)`.

Both masks vanish on the constraint domain `K`, so satisfiability is
untouched.

A proof is `(C_ci_1..C_ci_J, T, U, v_a)` = **(2 + #blocks) G1 + 1 F** — with
one block, 176 bytes on BLS12-381 compressed. When a block commitment is
already public state — as in this example, where it is the ledger
commitment — it need not be transmitted, leaving `(T, U, v_a)` =
**2 G1 + 1 F** (128 bytes), the Glock-optimized Pari size. Verification is
the single (3 + #blocks)-pairing equation

```
prod_j e(C_ci_j, delta_j H) * e(T, delta_w H) = e(U, tau H - r H) * e(v_a alpha G + v_R beta G, H)
```

with `v_R = (v_a + x_A(r))^2 - x_B(r)` recomputed by the verifier from `v_a`
(`x_B = 0` after SR1CS instance outlining).

## Protocol Walkthrough

### 1. Trusted Setup

```rust
let (pk, vk) = ZkPari::<E>::keygen(dummy_circuit, &mut rng);
```

Generate the CRS for a 64-bit range proof circuit. The circuit itself
declares its committed inputs by implementing `ZkPariCircuit`: synthesis
returns the blocks as lists of witness `Variable`s —

```rust
impl<F: Field> ZkPariCircuit<F> for RangeProofCircuit {
    fn synthesize(self, cs: ConstraintSystemRef<F>) -> Result<Vec<Vec<Variable>>, SynthesisError> {
        let v = cs.new_witness_variable(|| ...)?;
        // ... 64 bit variables, reconstruction + boolean constraints ...
        Ok(vec![vec![v]])    // block 0 = [v]
    }
}
```

so there is no positional convention to maintain: the value being
range-proved can be allocated anywhere (even produced mid-circuit by a
gadget), and key generation derives the commitment basis from the declared
variables. All non-declared witnesses are committed inside `T`.

### 2. Account Creation

Each account stores a Pedersen commitment to its balance:

```rust
let alice_opening = CommittedInputOpening::<Fr>::rand(&mut rng);
let alice_com = pk.pedersen_commit(0, &[Fr::from(1000u64)], &alice_opening);
```

The **opening** (a single scalar `rho_ci`) is Alice's secret — like a private
key for her balance. The **commitment** is public. Nobody can learn `1000`
from seeing `alice_com`.

### 3. Transfer

Alice wants to send 300 tokens to Bob. She performs three steps:

#### 3a. Commit to the transfer amount

```rust
let delta_opening = CommittedInputOpening::<Fr>::rand(&mut rng);
let com_delta = pk.pedersen_commit(0, &[Fr::from(300u64)], &delta_opening);
```

#### 3b. Derive the remaining-balance commitment

Because Pedersen commitments are additively homomorphic, Alice computes the
remaining-balance commitment by **group subtraction** — no arithmetic on the
secret balance happens in public:

```rust
let remaining_opening = &alice.opening - &delta_opening;
let com_remaining = (alice.commitment.into_group() - com_delta.into_group()).into_affine();
```

Algebraically:

```
com_alice     = 1000 * G_pay + rho_alice * G~_pay
com_delta     =  300 * G_pay + rho_delta * G~_pay
com_remaining =  700 * G_pay + (rho_alice - rho_delta) * G~_pay
```

Nobody computed 700 explicitly in the group — it fell out of the algebra.

#### 3c–3d. Two range proofs with controlled C_ci

Alice calls `prove_with_openings` for both values, passing the **same
opening** used to create each commitment. The prover then uses that opening
as the B-side mask `rho_ci`, which forces the proof's `C_ci` to exactly match
the externally computed commitment:

```rust
let proof_delta = ZkPari::<E>::prove_with_openings(
    RangeProofCircuit { value: Some(300) },
    &pk,
    core::slice::from_ref(&delta_opening),  // c_ci[0] will equal com_delta
    &mut rng,
).unwrap();
```

The A-side masks `(eta_1, eta_2)` are still freshly random in every proof.

### 4. Validator Checks

The validator (e.g., a smart contract) checks three things with **no secret
knowledge**:

1. **Both range proofs verify.** Each committed value is in \[0, 2^{64}).

2. **C_ci consistency.** `proof_delta.c_ci[0] == com_delta` and
   `proof_remaining.c_ci[0] == com_remaining`. This ties each proof to a
   specific ledger commitment.

3. **Balance conservation.**
   `proof_delta.c_ci[0] + proof_remaining.c_ci[0] == com_alice`. The two
   committed values sum to Alice's old balance, preventing money creation.

```rust
let sum = (proof_delta.c_ci[0].into_group() + proof_remaining.c_ci[0].into_group()).into_affine();
assert_eq!(sum, alice.commitment);
```

Together these checks guarantee: Alice split her hidden balance into two
non-negative parts, one going to Bob.

### 5. Ledger Update

Balances update homomorphically:

- **Alice:** her commitment becomes `proof_remaining.c_ci[0]` (commitment to 700).
- **Bob:** his commitment becomes `old_com_bob + proof_delta.c_ci[0]`
  (commitment to 500 + 300 = 800).

Bob also updates his opening by adding the delta opening scalar, so he can
spend from the updated balance in a future transfer. In this example the
opening travels out of band; the paper's eVRF-based *verifiable randomness
recovery* derives it from a shared secret instead, so nothing extra needs to
be transmitted or verifiably encrypted.

### 6. Batch Verification

`batch_verify` reduces N 4-pairing checks to a single 4-pairing check via
a random linear combination with 128-bit scalars, asymptotically replacing
per-proof pairings with one 128-bit MSM per proof element.

## Security Properties

| Property                  | Mechanism                                                          |
|---------------------------|--------------------------------------------------------------------|
| **Hiding**                | Pedersen commitments with `rho_ci * Gamma_ci` blinding             |
| **Range validity**        | ZK-Pari proves values are in \[0, 2^{64})                         |
| **No wrap-around**        | Range proofs prevent transferring negative amounts                 |
| **Balance conservation**  | Group-level check `com_delta + com_remaining == com_sender`        |
| **Zero-knowledge**        | Vanishing-poly masks `(eta_1, eta_2, rho_ci)`; statistical HVZK with distance `1/(|F|-|K|)` |

## Batched One-to-Many Transfers (`batched_private_transfer`)

The paper's Section 2 construction is implemented in the
`batched_private_transfer` example:

```bash
cargo run --release --example batched_private_transfer -p zkpari
```

A sender pays B recipients in one transaction with **one proof of
`3 G1 + 1 F` (176 bytes), independent of B** — instead of B+1 separate range
proofs. It uses two independently committed input blocks (each with its own
`delta_j`, adding one pairing to the verification equation):

| Block | Contents | Commitment |
|-------|----------|------------|
| 1 (size B+1) | claimed amounts `v^_1..v^_B` and remaining balance `v^_rem` | `C_ci_1`, transmitted with the proof |
| 2 (size 1)   | the aggregate `v_theta = sum_i theta^{i-1} v^_i + theta^B v^_rem` | `com_theta = sum_i theta^{i-1} com_i + theta^B com_rem`, **recomputed by the verifier from the ledger commitments — never transmitted** |

The flow:

1. The sender publishes per-recipient transfer commitments
   `com_i = v_i * G_pay + r_i * G~_pay` in the block-2 payment basis
   `(G_pay, G~_pay) = (Sigma_ci_2[0], Gamma_ci_2)`, and the block-1
   commitment `C_ci_1` to the claimed amounts.
2. The challenge `theta` is derived by Fiat-Shamir from
   `(com_sender, com_1..com_B, C_ci_1)` — everything it must be sampled
   *after* — and enters the circuit as an ordinary public input.
3. The circuit range-checks all B+1 committed values and enforces the
   Horner-evaluated aggregation
   `sum_i theta^{i-1} v^_i + theta^B v^_rem = v_theta` (each product costs
   two native SR1CS squares via `4 * a * t = (a+t)^2 - (a-t)^2`).
4. The verifier recomputes `com_rem = com_sender - sum_i com_i` and
   `com_theta`, reassembles the proof as
   `Proof { c_ci: vec![C_ci_1, com_theta], .. }`, and runs the single
   5-pairing `verify`. By Schwartz-Zippel, agreement at a random `theta`
   guarantees (w.h.p.) the range-checked claimed values equal the values
   inside the ledger commitments — so no recipient receives a negative
   amount and the sender's remaining balance is non-negative.

Measured on BLS12-381 (the example's scaling section):

| B | proof | naive (B+1 proofs) | ratio |
|---|-------|--------------------|-------|
| 2   | 176 B | 432 B    | 2.5x  |
| 8   | 176 B | 1200 B   | 6.8x  |
| 32  | 176 B | 4272 B   | 24.3x |
| 128 | 176 B | 16560 B  | 94.1x |

Note: the CRS is circuit-specific, so each batch size B needs its own setup
(senders can pad with zero-amount transfers to hit a supported B).

## Extensions from the paper (not implemented here)

- **Verifiable randomness recovery:** deriving `rho` from a two-party
  exponent-VRF inside the circuit lets the receiver recompute the opening of
  an incoming transfer locally, eliminating verifiable encryption.

## Griefing Attack (Caveat)

As noted in the Zether paper, accounts are susceptible to a griefing attack:
an attacker can front-run a transfer by depositing a tiny amount to the
sender's account, changing the balance commitment and invalidating the
in-flight proof. The Zether paper suggests maintaining two separate accounts
per user (one to receive, one to send) with periodic automatic rollovers.
This defense is not implemented in the example.

## Proof Cost

Each 64-bit range proof:

- **65 native SR1CS constraints** (64 boolean + 1 reconstruction), plus one
  outlining constraint
- proof = `3 G1 + 1 F` (176 bytes on BLS12-381); incrementally `2 G1 + 1 F`
  (128 bytes) since `C_ci` is the ledger commitment itself
- verification = 1 multi-pairing of size 4

A full transfer requires two range proofs plus one G1 addition for the
balance conservation check.
