# Pass 29: formedness from the genesis, signature-threaded histories (reviewer findings F1, F4, F8)

## Why

An independent review of 7ce7743 found three problems in the statements.

**F1.** `RustFormed` and `TSFormed` were "some parent signature hashes to the id": `∃ ps, block_id … ps … = id`.
- Under that reading, an attacker could sign B, and then C with B as parent and a dummy `ps`. C is then admissible before any honest signature on B exists.
- So `chain_order`, a field of `SigningExecutionOn`, was a hypothesis no real execution satisfies.
- The certificate's attested history did not thread signatures either.

**F4.** Mode 2's model validator `validSignedChainSched` still ran mode 1's monotone rule (`validChainK`, i.e. `keyMonoOk`). Its certificate, its fold and its deployed client do not.

**F8.** The mode-2 and mode-3 deployed clients had no knowledge-soundness twin of `rust_deployed_ks`.

## The new definitions (reviewer-written, pinned)

All of the following live in `Spec/RustBridge.lean` unless noted.

- **`SigOn I crypto n b s`**: `s` verifies on the Rust block `b` under the key of `b`'s slot producer at `b.key_index`. These are the same three calls `sigs_ok` makes per block.
- **`FormedFrom I crypto n G : Block → Prop`** (inductive).
  - `genesis`: `G` is formed.
  - `step`: `b` is formed if all of the following hold:
    - some formed `p` has a signature `sp` with `SigOn … p sp`;
    - `b.prev = some p.id`;
    - `block_id … b.slot b.height b.prev (some sp) b.contents_hash b.key_index = ok b.id`.
- **`RustFormed I crypto n G B`**: some Rust `b` with `toModelBlock b = B` and `FormedFrom … G b`.
- **`DSigned I crypto n G B`**: `RustSigned … B ∧ RustFormed … G B`.
- **`SigHist I crypto n ps bs ts`**: walks `bs : List (Block × Hash)`. For each pair `(b, s)`, three conditions hold, and the end signature is `ts`:
  - `SigOn … b s`;
  - `b.id` is `block_id` of `b`'s fields with `some ps`, where `ps` is the previous signature;
  - `s` becomes the next `ps`.
- **`AttestsK … G sG bs stO out ts`**: `SigHist … sG bs ts` ∧ `FoldKOut … (bs.map Prod.fst) stO out`. `AttestsSched` and `AttestsLock` are the same with their fold.
- **`fullChain G bs tl`**: `(G :: bs.map Prod.fst).map toModelBlock ++ toModelChain tl`.

Model and TypeScript (`Spec/Model.lean`):
- `TSSigOn n sigOps B sig` and `TSFormed n sigOps G` mirror `SigOn` and `FormedFrom`.
- `TSTipSigned n sigOps G cl s`: some formed `T` with the claim's tip id, slot and height, and `s` verifies on `T`.
- `validSignedChainSched` (in both Model and Reference) is now `sigsOk && validChain && schedPinned`. It has no `keyMonoOk`.

## Statement changes (`Spec/Statements.lean`)

**`thm_rust_deployed_{agreement,k_agreement,sched_agreement,lock_agreement}`**:
- `hSigG : SigOn I.CryptoInst crypto n G sG` replaces `DSigned G`.
- Histories are `bs : List (Block × Hash)`.
- `hts : I.cert_tip_sig crypto cert = ok ts`, and the primed twin.
- `Attests*` carry `sG` and `ts`.
- Admissibility is `DSigned I crypto n G` (lock: `RustFormed I crypto n G`).

**`thm_rust_deployed_ks`**:
- `hFold` also yields `ts` and `cert_tip_sig = ok ts`.
- `hval` accepts `validate_deployed` or `validate_deployed_k`.

**New:** `thm_rust_deployed_sched_ks` and `thm_rust_deployed_lock_ks`, the same shape as `thm_rust_deployed_ks`.

**`thm_sched_liveness_produce_block`**: `hFloor` is removed.

**`thm_ts_deployed_agreement`**:
- Admissibility is `TSSigned ∧ TSFormed n sigOps G`.
- `hUnf` also gives `TSTipSigned n sigOps G cl (certOps.tipSig hc)`.

## Proof plan

### The key lemma: formedness along a signature-threaded chain

Two inductions, Rust and TypeScript alike.

1. **History.** Assume:
   - `SigOn G sG`;
   - `SigHist sG bs ts`;
   - the fold's link facts: the first block's `prev` is `G.id`, and each next block's `prev` is the previous block's id.

   Then every block of `G :: bs.map Prod.fst` is `FormedFrom G`. Its last block `T` satisfies `FormedFrom G T`, `SigOn T ts`, and `T.id = stO.tip_id`, `T.slot = stO.tip_slot`, `T.height = stO.tip_height`.

   Proof: induct on `bs`, generalising the "current formed block with its signature". The step case is exactly `FormedFrom.step`.

2. **Tail.** Assume:
   - `FormedFrom G T` and `SigOn T ts`;
   - `sigs_ok sc`, `strip_sigs sc = ok tl` and `ids_ok I crypto (some ts) sc`;
   - the suffix links: the first block's `prev` is `T.id`, and consecutive blocks link.

   Then every block of `tl` is `FormedFrom G`. Proof: induct on `sc`, as `ids_ok_formed` does, carrying `(T, ts)` → `(b, s)`.

The fold's link facts come from what `cert_fold_k_sound` and its twins already prove: the fold's claim is a grounded history with `linksOk`. The suffix links come from `validate_suffix` (the Pass 28 view-transport lemma). `T.id = stO.tip_id` comes from the fold's state update (`stepState`).

Then `DSigned` for every block of `fullChain G bs tl` follows:
- `RustSigned` comes from `SigOn`, for the history and for `G`;
- for the tail it comes from `sigs_ok_signed`.

This replaces `ids_ok_formed` and `dsigned_of_sigs_ok_ids_ok`, whose old conclusion (`∃ ps`) no longer typechecks.

### Mode 2 without the monotone rule

`validSignedChainSched` lost `keyMonoOk`. Proofs that took `validChain` out of `validChainK` now get it directly. Proofs that used `keyMonoOk` for mode 2 must not need it: the mode-2 safety argument is the schedule pin. `sched_liveness_produce_block` is easier: drop the floor obligation. `reference_eq_model`'s mode-2 conjunct is again `rfl`/`simp`, because Model and Reference changed in step.

### TypeScript

`ts_deployed_agreement`:
- History blocks are admissible by `GroundedCert` (hypothesis `hUnf`).
- Tail blocks: `TSTipSigned` gives the formed, signed tip `T`. `idsOk` from `tipSig` and `sigsOk` give `TSFormed` by the same induction as item 2.
