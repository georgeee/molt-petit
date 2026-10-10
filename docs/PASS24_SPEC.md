# Pass 24: what the peer review (2026-10-09) needs from the Lean

## Why

An outside review found four places where the paper claims more than the Lean states:

1. **Mode-3 / mode-2 certified agreement is about the tail only.** The certified-suffix theorems
   (`lockstep_recent_certified_suffix_agreement`, `lockstepGen_…`, `sched_…_horizon`) conclude
   only on blocks of the presented tail. The paper reads them as agreement on the whole
   history. We want theorems that say this: two certificates have histories `c`, `c'`, and the
   full chains `c ++ tail` agree at every index at least `n` (resp. `2n`) blocks below both tips.
2. **The existence of a history behind a certificate** is used in prose but not cited.
3. **The suffix key-version checks** (`validate_suffix_k`, `validateSuffixK`) have soundness
   theorems, but the paper cites none of them. It says `validate_certified_chain` does key checks,
   which is false.
4. **`LockstepPackageTimed.notBefore`** was a field that no proof used. The reviewer removed
   it from `Spec/Model.lean` in the scaffold commit. Nothing constructs the structure, so no
   proof should need changes, but the build must confirm it.

Separately, the TypeScript validator over-rejects near the genesis (5). `lo :=
c.tipSlot + 2 - n` is an `Int` and goes negative, and `maturedDense` then counts a window
starting at a negative slot. For example, n = 7, the genesis certificate plus a one-block
suffix at slot 1 is rejected.

A second review pass (2026-10-10) adds two more:

6. **Hash injectivity over a domain a thief can fill (N1).** `LockstepPackage*.hashInj` and
   the five mode-2 horizon theorems' `hHash` were `SignedHashInjective (SignedDeclared …) G`.
   One stolen key falsifies that: sign two blocks with different contents and the same copied
   id. The timed theorems already restrict to `SignedDeclared ∧ Formed`. The scaffold now does
   the same everywhere: `Spec/Model.lean` defines `SignedFormed n ops registry Formed B :=
   SignedDeclared n ops registry B ∧ Formed B`; the three lockstep packages take a new
   explicit parameter `(Formed : Block → Prop)` right after `registry`, with
   `hashInj : SignedHashInjective (SignedFormed n ops registry Formed) G`; the 20 affected
   statements bind `{Formed : Block → Prop}`, use `SignedFormed` for every certificate/history
   `Signed` argument and every `hSigned`, and the two-chain ones gain
   `(hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)` (and `hFormed'` for `sc'`).
7. **`Spec/TS.lean` `produceBlock` shadowed `contentsHash` (N3).** The match binder captured
   the parameter, so the new block got the head block's payload commitment. `moltPetit.ts` is
   correct; the hand-mirrored Lean was not. The scaffold renames the binder `contentsHash'`
   (same fix as `keyIndex'`) and updates `vendored-deviations.patch` to match.

## Pinned goals (reviewer-written, DO NOT EDIT)

`Spec/Statements.lean` and `Spec/Model.lean` are pinned for this pass. At the end,
`git diff <scaffold commit> -- Spec/Statements.lean Spec/Model.lean` must be empty, except
for task (d), which may change `Spec/TS.lean` only as described there (keeping the task-(f) binder).

New statements in `Spec/Statements.lean`:

| statement | proof |
|---|---|
| `thm_lockstep_recent_certified_history_agreement` | new (task a) |
| `thm_lockstepGen_recent_certified_history_agreement` | new (task a) |
| `thm_sched_recent_certified_history_agreement_horizon` | new (task a) |
| `thm_groundedCert_history` | existing `MoltPetit.Model.groundedCert_history` |
| `thm_groundedCertSched_history` | existing `groundedCertSched_history` |
| `thm_groundedCertLock_history` | existing `groundedCertLock_history` |
| `thm_ts_validateSuffixK_sound` | existing `ts_validateSuffixK_sound` |
| `thm_validate_suffix_k_sound` | existing `validate_suffix_k_sound` (Rust/BridgeK.lean) |

`GroundedHistoryLock` and `keyMonoFrom` moved verbatim from the development files into
`Spec/Model.lean` (development files import `Spec.Model`, so they are still in scope).

## Tasks

**(a) The three history theorems.** Each has the hypotheses of its `_suffix_` twin, except
that the certificate premise is replaced by a *history* premise. For example,
`GroundedHistoryLock n Signed G cl g c` replaces `GroundedCertLock n Signed G cl g`; for mode 2,
`GroundedHistorySched n schedule Signed G cl c` replaces `GroundedCertSched …`. The conclusion
is agreement of `c ++ s₁ :: srest` and `c' ++ s₁' :: srest'` at any index `k` with
`k + n` (resp. `k + 2*n` for `lockstepGen`) below both lengths.

Proof plan. The existing suffix proofs (e.g. `KeyStealingLockstepCert.lean` around l.548)
already do this internally:

1. obtain a history `c` with `groundedCertLock_history` (inside `groundedCertLock_suffix_history`);
2. glue it to the suffix with `groundedCertLock_signedChain` (or its sched twin) into a full
   signed chain;
3. apply `sched_deep_block_agreement_of_length` (or the lockstep/gen twin) at index
   `c.length + i`.

Factor step 2 into a variant that takes the history `c` as a hypothesis instead of producing
it, and prove the suffix theorem through that variant. Then the history theorem is the same
proof at an arbitrary index `k` rather than `c.length + i`. Put each new theorem next to its
twin and add a `MoltPaper.xxx : thm_xxx` alias in `Paper/Proofs.lean` (alphabetical, like
the rest).

**(b) Aliases.** Add `MoltPaper` aliases in `Paper/Proofs.lean` for the five existing
theorems in the table. The Rust one is `@validate_suffix_k_sound` (check its namespace).
If a statement does not typecheck against the development theorem as written, or a task-(a) statement looks false, STOP and report
the mismatch in `docs/PASS24_PROGRESS.md`. Do not edit the statement.

**(c) `notBefore`.** Confirm the build passes after its removal. Update comments that call it a
field (`KeyStealingLockstepTimed.lean` header; nothing else should mention it).

**(d) TS clamp.** In `moltPetit.ts` (`validateSuffix`), clamp the density lower bound at 0,
for example `const lo0 = c.tipSlot + 2n - n; const lo = lo0 < 0n ? 0n : lo0;`, in a form the
thales emitter accepts. Mirror the emitted Lean exactly in
`tools/thales-reemission/MoltPetit.emitted.lean` and `Spec/TS.lean`, and update every digest
in `nix/checks.nix` that covers these files. Try `nix build .#lean-from-ts` and, if it
builds, check `cmp` against the golden file (the `checks.nix` check does this). Repair the
TS soundness proofs (`MoltPetit/TS/*`). The model density is quantified over `u : Nat` with
`(tipSlot + 2 - n : Int) ≤ u`, so clamping only removes negative `u`, which never occurs.
Add a `#guard` (a new file under `MoltPetit/TS/`, imported by the TS root) checking that at
n = 7 the genesis certificate followed by one block at slot 1 (height 1, `prev` = the
genesis id, a correct key index, and a floor snapshot that accepts it) is accepted by
`validateSuffix`. If the emitter cannot express the clamp, or `lean-from-ts` cannot be built
on this host, still make the three sources agree by hand and say so in the progress file.

**(e) N1: hash injectivity over formed blocks.** Make every proof go through with the
pinned N1 statements (item 6). The development lemmas already used by the timed route take
a generic `Signed`/`Adm` predicate, so most changes are instantiating them at
`SignedFormed n ops registry Formed` instead of `SignedDeclared n ops registry`, and
supplying `Formed` for chain blocks from `hFormed`/`hFormed'` (genesis is in the injective
domain by `B = G ∨ …`). Unforgeability fields still speak about `SignedDeclared`; get it from
`.1` of `SignedFormed`. Change the development packages (`PackageA` etc.) the same way where a
proof needs it. If a pinned N1 statement is not provable as written (e.g. a single-chain
statement whose proof needs `Formed` on its chain), STOP and report the statement and the
missing fact in `docs/PASS24_PROGRESS.md`; do not add hypotheses yourself.

**(f) N3 binder.** The `produceBlock` binder rename in `Spec/TS.lean` (item 7) is done in the
scaffold. Keep it when you mirror task (d), confirm `nix flake check`'s
`ts-vendored-deviations` still passes (or, if you cannot run it, that
`tools/thales-reemission/vendored-deviations.patch` applies to the emitted file and yields
`Spec/TS.lean`'s body), and repair any TS proof that unfolds `produceBlock`.

## Done when

- `bash tools/check.sh` prints `check: all green`;
- the pinned files are unchanged (see above);
- every new alias depends only on `propext`, `Classical.choice`, `Quot.sound` (paper-check);
- `docs/PASS24_PROGRESS.md` lists what was done per task.

Do not edit `paper/molt.tex`; the reviewer edits the paper.
