# Private Transfers with Hidden Amounts (ZK-Pari)

This document explains the `private_transfer` example, which demonstrates a
Zether-like private payment system built on the ZK-Pari proof system.

Run the example:

```bash
cargo run --example private_transfer -p pari
```

## Core Idea

In a normal payment system, balances are stored in plaintext. In Zether,
balances are stored as **Pedersen commitments**.

ZK-Pari's key insight is that the proof element **T1 already has the structure
of a Pedersen commitment**, so range proofs and balance commitments come for
free from the same proof. In the simplified construction, all
vanishing-polynomial masking lives in T2, leaving T1 in clean
witness-commitment form. With `witness_split=1` the prover computes:

```
T1 = value * Sigma1[0] + zeta1 * (gamma/delta1)*G
```

This is a standard 2-generator Pedersen commitment to `value` with a single
blinding scalar `zeta1`. The generators are fixed by the CRS:

CRS element              | Role              |
|-----------------------|--------------------------|
| `sigma_1[0]`             | Encodes the value |
| `gamma_over_delta_1_g`   | Blinding          |

## Protocol Walkthrough

### 1. Trusted Setup

```rust
let (pk, vk) = Pari::<E>::keygen(dummy_circuit, 1, &mut rng);
```

Generate the CRS for a 64-bit range proof circuit with `witness_split=1`.
The first witness variable (the value being range-proved) is committed via
`sigma_1`; the remaining 64 bit variables and outlining copies go into
`sigma_2`.

### 2. Account Creation

Each account stores a Pedersen commitment to its balance:

```rust
let alice_opening = PedersenOpening::<Fr>::rand(&mut rng);
let alice_com = pk.pedersen_commit(Fr::from(1000u64), &alice_opening);
```

The **opening** (a single random scalar `zeta_1`) is Alice's secret — like a
private key for her balance. The **commitment** is public. Nobody can learn
`1000` from seeing `alice_com`.

### 3. Transfer

Alice wants to send 300 tokens to Bob. She performs three steps:

#### 3a. Commit to the transfer amount

```rust
let delta_opening = PedersenOpening::<Fr>::rand(&mut rng);
let com_delta = pk.pedersen_commit(Fr::from(300u64), &delta_opening);
```

#### 3b. Derive the remaining-balance commitment

Because Pedersen commitments are additively homomorphic, Alice computes the
remaining-balance commitment by **group subtraction** — no field arithmetic on
the secret balance is performed in public:

```rust
let remaining_opening = &alice.opening - &delta_opening;
let com_remaining = (alice.commitment.into_group() - com_delta.into_group()).into_affine();
```

Algebraically:

```
com_alice     = 1000 * G_val + r_alice * H
com_delta     =  300 * G_val + r_delta * H
com_remaining =  700 * G_val + (r_alice - r_delta) * H
```

Nobody computed 700 explicitly in the group — it fell out of the algebra.

#### 3c–3d. Two range proofs with controlled T1

Alice calls `prove_with_pedersen_opening` for both values, passing the **same
opening** used to create each commitment. This forces the proof's T1 to exactly
match the externally computed commitment:

```rust
let proof_delta = Pari::<E>::prove_with_pedersen_opening(
    RangeProofCircuit { value: Some(300) },
    &pk,
    &delta_opening,     // T1 will equal com_delta
    &mut rng,
).unwrap();
```

Inside the prover, `zeta_1` is taken from the opening rather than sampled
randomly. The remaining blinding values are still random.

### 4. Validator Checks

The validator (e.g., a smart contract) checks three things with **no secret
knowledge**:

1. **Both range proofs verify.** Each committed value is in \[0, 2^{64}).

2. **T1 consistency.** `proof_delta.t_1 == com_delta` and
   `proof_remaining.t_1 == com_remaining`. This ties each proof to a specific
   commitment.

3. **Balance conservation.**
   `proof_delta.t_1 + proof_remaining.t_1 == com_alice`. The two committed
   values sum to Alice's old balance, preventing money creation.

```rust
let sum = (proof_delta.t_1.into_group() + proof_remaining.t_1.into_group()).into_affine();
assert_eq!(sum, alice.commitment);
```

Together these checks guarantee: Alice split her hidden balance into two
non-negative parts, one going to Bob.

### 5. Ledger Update

Balances update homomorphically:

- **Alice:** her commitment becomes `proof_remaining.t_1` (commitment to 700).
- **Bob:** his commitment becomes `old_com_bob + proof_delta.t_1`
  (commitment to 500 + 300 = 800).

Bob also updates his opening by adding the delta opening scalar, so he can
spend from the updated balance in a future transfer.

## Security Properties

| Property              | Mechanism                                                |
|-----------------------|----------------------------------------------------------|
| **Hiding**            | Pedersen commitments are perfectly hiding                 |
| **Range validity**    | ZK-Pari proves values are in \[0, 2^{64})               |
| **No wrap-around**    | Range proofs prevent transferring negative amounts        |
| **Balance conservation** | Group-level check `com_delta + com_remaining == com_sender` |
| **Zero-knowledge**    | `(eta_A, eta_B, zeta_2, s)` provide simulation entropy      |

## Griefing Attack (Caveat)

As noted in the paper, accounts are susceptible to a griefing attack: an
attacker can front-run a transfer by depositing a tiny amount to the sender's
account, changing the balance commitment and invalidating the in-flight proof.
The Zether paper suggests maintaining two separate accounts per user (one to
receive, one to send) with periodic automatic rollovers. This defense is not
implemented in the example.

## Proof Cost

On BN254 (single-threaded), each 64-bit range proof:

- **65 native SR1CS constraints** (64 boolean + 1 reconstruction)
- **~7 ms** to prove
- **~0.5 ms** to verify

A full transfer requires two range proofs plus one G1 addition for the balance
conservation check.
