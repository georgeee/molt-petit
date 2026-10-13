# Pass 28: close the carve-outs (catalogue items A1–A4, B1, B4, B5, C1–C4, C6, C7, D1–D3)

## Why

The 18a2f42 audit and the carve-out catalogue (`work/p27/carve-outs.md`) list results where the paper and Lean agree but the proved result stops short of the deployed system.

**Shipped code**
- The rotation modes are proved only for the model.
- The fold certificate is connected to the agreement theorems only "in view".
- Recency, id formation and claim decoding are done outside verified code.

**Circuit and producer**
- The circuit's key-version witness is bound by wiring only.
- Only the soundness half of the circuit is proved.
- The Rust producer is not covered by any theorem.

**Model gaps**
- The untimed theorems share one clock reading.
- Clients that check at different times have no statement.
- The lifetime budget has no certificate form.
- The incremental density check is an argument, not a statement.
- `Spec/Reference.lean` duplicates model definitions without equality lemmas.

Out of scope, by George's decision of 10-13:
- Skipped:
  - gadget faithfulness;
  - knowledge soundness;
  - the registry-root anchor;
  - network liveness;
  - group E (real-world assumptions).
- Postponed:
  - the quiet-host benchmark;
  - the Thales hand corrections.

## The deployed client (Rust, reviewer-written, appended to `rust/src/lib.rs`)

`CryptoD: Crypto` adds four trait methods:

| Method | What it returns |
|---|---|
| `block_id(slot, height, prev, parent_sig, contents_hash, key_index)` | the deployment's id hash; the parent's signature is in the preimage, which is what makes `chain_order` true |
| `cert_tip_sig(cert)` | the signature of the certificate's tip block, which the fold certificate exposes |
| `cert_state(cert)` | the fold certificate's public claim state, `CertStateG<u64>` |
| `cert_floors_state(cert)` | mode 1's floors, `FloorsG<u64>` |
| `cert_gen(cert)` | mode 3's generation |

Verified functions:

| Function | What it does |
|---|---|
| `ids_ok parent_sig suffix` | every tail block's id is `block_id` of its other fields and its parent's signature: `cert_tip_sig` for the first block, then the previous block's signature |
| `recent_ok now delta tip` | `now ≤ tip + delta`, written without overflow |
| `claim_of_state n st` | decodes the public state into a `CertClaim`: the tip, plus the present buffer entries at or above `suffix_lo n tip_slot` as slot-only blocks. This is the verified replacement for the opaque `cert_claim` (B4). |
| `floors_of_state`, `sched_pin_ok era`, `lockstep_from n ts g` | the per-mode helpers (`lockstep_from` mirrors the model's `lockstepFrom`) |
| `validate_deployed n now delta crypto cert suffix` | `cert_verify` ∧ non-empty tail ∧ `sigs_ok` ∧ `ids_ok` ∧ `validate_suffix` against `claim_of_state` ∧ `recent_ok` |
| `validate_deployed_k` | `validate_deployed` + `floors_shape_ok` + `key_mono_from` on the certificate's floors (mode 1) |
| `validate_deployed_sched era` | `validate_deployed` + `sched_pin_ok` (mode 2) |
| `validate_deployed_lock` | `validate_deployed` + `lockstep_from` from the state's tip slot and `cert_gen` (mode 3) |
| `produce_block_deployed` | the honest producer; it computes the id with `block_id` and ships only what `validate_deployed` accepts at the new slot |

## Bridge definitions (reviewer-written, `Spec/RustBridge.lean`)

- `RustFormed I crypto B`: some Rust block `b` with `toModelBlock b = B`, and some parent signature, have `block_id` equal to `b.id`. This is `Formed`, now computed by the validator.
- `DSigned I crypto n B := RustSigned I.toCrypto crypto n B ∧ RustFormed I crypto B`. This is the per-block test every deployed theorem uses.
- `rustOps I crypto : SigOps Hash Hash Hash` and `rustRegistry I crypto : KeyRegistry Hash`. These are the Rust signature check as a model `SigOps` and versioned registry, for the mode-3 packages. They are classical: `verify pk B sig := decide (∃ b, toModelBlock b = B ∧ I.verify crypto pk b sig = ok true)`.
- `AttestsK n q G stO out bs`: every block of `bs` is `DSigned`, and `FoldKOut n q (genesisState n.val G) (initFloors n.val G.key_index) bs stO out`. The twins are `AttestsSched` and `AttestsLock`.

## Statements (reviewer-written, `Spec/Statements.lean`, section "Pass 28")

### End to end (A1–A4, B4, C1, C2)

Every theorem below quantifies over the attested histories. For any history `bs` that folds from the genesis to the certificate's public state (knowledge soundness says one exists), the full chain `toModelChain (G :: bs) ++ tail` satisfies the conclusion. No hypothesis is about the decoded claim, recency, id formation or the tail's key rule: the validator checks all of them.

1. **`thm_rust_deployed_agreement`** (Theorem 1)
   - Hypotheses: Theorem 1's timed assumptions with `Signed := DSigned`, the verifier clock `R ≤ now + δ` for both readings, and `Δ + δ ≤ φ`.
   - Both clients are accepted by `validate_deployed` at their own readings.
   - Conclusion: the two full chains agree at depth `n`.
2. **`thm_rust_deployed_k_agreement`** (mode 1, A2)
   - Same hypotheses as item 1, with `validate_deployed_k`.
   - Conclusion: agreement, and both full chains satisfy `KeyIndexMonotone`.
3. **`thm_rust_deployed_sched_agreement`** (mode 2, timed)
   - Exposure is `schedExposed n (·/era) Controlled Stolen`; the per-block test is `DSigned ∧ slot/era ≤ keyIndex`.
   - Folds use `FoldSchedOut`, and the validator is `validate_deployed_sched`.
   - Conclusion: agreement at depth `n`, and both full chains are pinned.
4. **`thm_rust_deployed_lock_agreement`** (mode 3, per-generation)
   - Hypotheses: `LockstepPackageGen` over `rustOps`/`rustRegistry` with `Formed := RustFormed I crypto`, at the reading `min now now'` (D2).
   - Folds use `FoldLockOut`; the validator is `validate_deployed_lock`.
   - Conclusion: agreement at depth `2n` in the full chains.
5. **`thm_rust_deployed_ks`**: knowledge soundness supplies a history. If `cert_verify` holds and `hFold` (the circuit's knowledge soundness, as in pass 26) holds, then some attested history exists. This keeps items 1–4 non-vacuous.

### Producer (C3)

6. **`thm_rust_produce_block_deployed_live`**
   - Hypotheses:
     - the existing suffix passes `validate_deployed`'s non-recency checks;
     - the slot is the producer's own and lies after the tip;
     - signing is correct for the producer's key at `key_index`;
     - every window the new block completes is dense, counted over the decoded claim's tail plus the new suffix (as `hDense`).
   - Conclusion: the output is `CC cert (suffix ++ [nb])`, and `validate_deployed` accepts it at `now := at_slot`.

### Circuit completeness (B5)

7. **`thm_valid_chain_be_complete`**: a chain the model accepts (`ValidChain`), with slots and heights below `2^62` and `n < 2^62`, is accepted by `valid_chain_be` on the U64 backend.
8. **`thm_cert_fold_k_complete`**, **`_sched_complete`**, **`_lock_complete`**
   - Hypotheses: a chain `G :: bs` valid under the mode's full-chain rule (`validChainK`, `validChain` + pin, `validChain` + `lockstepOk`), with the same size bounds.
   - Conclusion: the fold accepts it, so `FoldK`/`FoldSched`/`FoldLock` hold for some output.

### Model statements (C6, C7, D1–D3)

9. **`thm_validChain_snoc`** (C6). For non-empty `c` with tip `t`, `validChain n (c ++ [b]) = true` holds iff all of:
   - `validChain n c = true`;
   - `childOk t b = true`;
   - every window `u` with `t.slot + 2 ≤ u + n ≤ b.slot + 1` holds `quorum n` blocks of `c ++ [b]`.
10. **`thm_reference_eq_model`** (C7): every `Molt.*` function that duplicates a model function equals it. This is a conjunction of `funext` equalities.
11. D1 (clients at different times): no new statement. Theorem 1 already applies at the later reading when the earlier chain is still recent then; anything stronger needs an honest chain that keeps growing between the readings, which is network liveness (D4, out of scope). The paper says so.
12. **`thm_lockstepGen_recent_certified_history_agreement_two_readings`** and **`thm_sched_recent_certified_history_agreement_horizon_two_readings`** (D2): two readings `now`, `now'`, each client recent at its own, with the package at `min now now'`.
13. **`thm_exposure_certified_agreement_ever_on`** (D3): the certificate-plus-history form of `exposure_agreement_ever_on`.

## Circuit (B1, worker)

`rust-keyrot/src/fold_circuit.rs` computes the block id in-circuit as Poseidon over `(slot, height, has_prev, prev, contents_hash, key_index)`, and requires:
- the signature subproof's digest to equal that id;
- the registry leaf to be at `(slot % n, key_index)`, with the same `key_index` wire the step reads.

Tests: a block whose stated id differs from the hash, or whose step `ki` differs from the hashed `key_index`, has no proof. The native `CryptoD` implementation uses the same Poseidon id.

## Proof plan sketches (Archon)

- **Items 1–4: view invariance.**
  - `validate_suffix n cl s` depends on `cl` only through `claimView`. Its fields are the tip slot, height and id, and the tail's slots: `matured_dense` reads slots only.
  - So acceptance against `claim_of_state (stateView …)` transfers to `cl₀ := modelClaimOf n G (bs.map toModelBlock)`, which is grounded by `cert_fold_*_sound`.
  - Lemma: `claimView (toModelClaim (claim_of_state n st)) = stateView n.val st`, using `suffix_lo` = the model's `tipSlot + 2 - n`.
- **Items 1–4: history.**
  - `GroundedHistory … cl₀ (toModelChain (G :: bs))` holds by induction along the fold, the same induction as `cert_fold_*_sound`; or reuse `groundedCert*_history` plus uniqueness.
  - Then apply `exposure_certified_agreement_on` (items 1–2), the sched certified agreement (item 3), and `lockstepGen_recent_certified_history_agreement` (item 4).
  - Item 2's monotonicity: `GroundedCertK` floors equal `floorsFun out`, and `key_mono_from` gives `keyMonoFrom`. Glue the history's `keyMonoOk` (from `GroundedCertK`) with the tail's.
- **Recency.** `recent_ok now Δ tip` gives `now ≤ tip + Δ`, so `R ≤ tip + φ`.
- **Ids.** `ids_ok` gives `RustFormed` for each tail block.
- **`rustOps`.** `SignedDeclared n (rustOps …) (rustRegistry …) B ↔ RustSigned …`.
- **Item 6.** Unfold the producer: links and density by hypothesis, signature by signing correctness, id by construction, recency `at_slot ≤ at_slot + Δ`.
- **Items 7–8.** Converse of the existing soundness proofs; use the size bounds to rule out overflow.
- **Items 9–13.** Mostly corollaries:
  - D2: instantiate at `min`.
  - C6: unfold `maturedWindowsDense`.
  - C7: `rfl` or structural induction per function.
  - D3: follow `exposure_certified_agreement_on`'s proof with the `Ever` budget.

## Stages

- **A (reviewer).** Rust scaffold → extraction → bridge definitions → statements typecheck.
- **B (Archon).** Items 9–13 and 7–8. They are independent of each other.
- **C (Archon).** Items 1–6.
- **D (worker).** Circuit B1 plus tests.
- **E.** TypeScript twin (C4 via C2). `moltPetit.ts` gains `idsOk` (threading parent signatures), `recentOk` and `validateDeployed`; `SigOps.blockId` and `CertOps.tipSig` join the dictionaries (no new emitter deviation sites). Statement `thm_ts_deployed_agreement`: as `thm_ts_timed_certified_agreement` with `Formed := TSFormed sigOps`, `validateDeployed`, and clock readings, with no `hFormedS` and no `hRecent`.
- **F (reviewer).** Paper.
