# `molt_petit_keyrot` — consensus × signed key rotation (plonky2)

A pure-Rust integration that carries **signed key-rotation transitions inside
Molt Petit consensus blocks**, where the **certificate is produced by running
the consensus validator itself as a plonky2 circuit**. It reuses the consensus
protocol from the sibling [`../rust`](../rust) crate (`molt_petit`, the reference
mechanically extracted to Lean) and supplies a concrete cryptographic dictionary
plus a runnable demo.

## One validator, two backends (the key idea)

plonky2 is a circuit DSL, not a CPU — it cannot *execute* compiled Rust. So
rather than hand-writing a separate circuit (which could silently drift from the
proven logic), the validator is written **once** over a small arithmetic/boolean
[`Backend`](src/backend.rs) trait and instantiated two ways:

| Backend | `Num` / `Bool` | Effect |
|---|---|---|
| [`Native`](src/backend.rs) | `F` / `bool` | the validator **executes**, returning the validity bit (cross-checked against `molt_petit::valid_chain`) |
| [`Circuit`](src/backend.rs) | plonky2 `Target` (+ traced value) / `BoolTarget` | the **same code emits the plonky2 circuit**, recording the witness as it goes |

Because both run the identical generic [`spec::run`](src/spec.rs), the circuit
cannot diverge from the native logic — there is a single source of truth. The
demo proves a valid chain and shows the *same* validator reject a
density-violating chain and a forged-signature chain in **both** backends.

### What the validator checks (`spec::run`, faithful to `molt_petit::valid_chain`)

- `genesis_ok` — block 0 has height 0 and no parent;
- `child_ok` — `height + 1`, strictly increasing slot, `prev == parent id`
  (the last is enforced by *defining* each id as the Poseidon commitment of its
  fields including the parent id);
- **`matured_dense`** — every matured window `[u, u+n)` (base `u = 0` plus the
  anchors `u = slot_i + 1`) has at least `quorum(n)` blocks. **Window density is
  fully in the proof.**
- application layer: each rotation block's content *is* the transition digest of
  a threshold-signed (`q = 5`) `old → new` replacement, and the committed key set
  evolves; signatures use the same generic body as `pq_sig::verify_native`.

The proof's public inputs are `[ tip_slot | tip_height | tip_id(4) |
set_commitment(4) ]`, so the certificate *proves* the tip and committed state;
`cert_claim` reads them straight from the proof.

### The verified validator runs in-circuit (`molt_petit::valid_chain_be`)

The consensus validity check is also available as the **backend-generic
`valid_chain_be` in the verified `molt_petit` crate** — the SAME Rust source that
Lean proves sound (`Rust.valid_chain_be_validChain`: accepting a chain ⟹ the
model `ValidChain`). [`mp_circuit`](src/mp_circuit.rs) implements
`molt_petit::Backend` with a plonky2 circuit (interior-mutable builder), so
`molt_petit::valid_chain_be(&circuit, n, q, chain)` makes the circuit *literally
execute the proven function*. The demo proves it on a valid chain and shows the
verified validator circuit reject a density-violating one — closing the gap from
"a faithful transcription" to "the proven function is the circuit", connected by
a Lean theorem rather than a runtime cross-check.

### Structural carve-out (plainly visible, not crucial)

The proven `validate_certified_chain` calls `crypto.cert_verify(cert)` to trust a
certified *prefix*. Here the chain is validated from genesis in one circuit, so
that call is not invoked. The constant-size *recursive* variant would replace
exactly that one call with plonky2's native `verify_proof` (the recursion does
the predecessor check). Nothing else is assumed away.

## Crypto dictionary (`molt_petit::Crypto`)

| Interface | Concrete primitive |
|---|---|
| block-producer `sign`/`verify`/`key_for` | **no dedicated signature scheme**: a key is `pk = Poseidon(sk)[0]`, and a signature is a plonky2 **proof of knowledge of `sk`** bound to `(pk, msg)` ([`pok`](src/pok.rs)) |
| `cert_verify`/`cert_claim` | re-run the validator-proof verifier; the claim is derived from the proof's public inputs |
| block ids, commitments, `contents_hash` | Poseidon over Goldilocks throughout |

The threshold authorization on a rotation uses the same idea, folded directly
into the certificate: each of `q` distinct members proves knowledge of the
secret behind its public key (`assert Poseidon(sk) == member_pk`), bound to the
transition by the certificate's public inputs. One Poseidon per signer.

Signatures/proofs are wider than the consensus's 256-bit opaque `Hash` handles,
so the handle is a Poseidon commitment and the real object lives in a side table
in [`KeyRotCrypto`](src/crypto.rs).

## Running

`cargo`/`rustc` are not on `PATH` here; use the stable rustup toolchain directly
(build settings — `RUSTC_BOOTSTRAP=1`, `bfd` linker — are in
[`.cargo/config.toml`](.cargo/config.toml)):

```bash
export PATH=~/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin:$PATH
cargo run --release      # the demo (native + circuit, n=7, 3 rotations)
cargo test --release     # native-verify + recursive roundtrip tests
```

## Notes / where to extend

- Signatures are Lamport-over-Poseidon for now (isolated in
  [`pq_sig`](src/pq_sig.rs)); the in-circuit-friendly upgrade path is WOTS+ over
  Poseidon. `TREE_DEPTH = 3` (8 one-time signatures per key).
- The validator transcription's *equivalence* to the Lean-proven Rust is not
  itself machine-checked — that is the residual trust boundary plonky2 imposes.
  The `Native` instantiation is cross-checked against `molt_petit::valid_chain`
  at runtime to keep them honest.
- Constant-size recursion (one fixed-size proof for unbounded chains) is the
  natural next step: make `spec::run` an IVC step and discharge `cert_verify`
  with plonky2's native `verify_proof`.
- The plonky2 modules (`types`, `keyset`, `chain`, `pq_chain`, `pq_sig`) are
  copied from the `plonky2-playground` prototype.
