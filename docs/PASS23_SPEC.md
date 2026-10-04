# Pass 23: an execution hypothesis an exposed key cannot falsify

## Why

`SigningExecution.chain_order` asks that *every* logged block's parent id
resolve to an available block, and `id_inj` that *every* two occurring blocks
with equal ids be equal. An adversary holding any exposed key can sign a block
whose `prev` is a random value, or which copies an honest block's id. Every
bridge (`hbridge`) forces signature-valid blocks into the log, so such a block
falsifies the hypothesis and every theorem using it becomes vacuous for that
execution. That contradicts the paper's claim that exposed keys are
unconstrained.

The fix restricts both fields to *admissible* blocks: blocks a verifier
accepts. Admissibility now includes **id formation** (`Formed`): the id is the
hash of the block's preimage taken over its parent's actual signature, which
the deployment's hashing layer recomputes. For formed blocks, causal order and
collision resistance are honest cryptographic facts. A forged parent reference
or a copied id is simply not admissible.

`MoltPetit/Model/Definitions.lean` already carries the new
`SigningExecutionOn` (reviewer-written; do not change it):

```lean
chain_order : ∀ ⦃r B C⦄, B ∈ log r → Adm B → SignedEver log G C → (C = G ∨ Adm C) →
  B.prev = some C.id → AvailableAt log G C r
id_inj : ∀ ⦃B B'⦄, SignedEver log G B → SignedEver log G B' →
  (B = G ∨ Adm B) → (B' = G ∨ Adm B') → B.id = B'.id → B = B'
```

The unrestricted `SigningExecution` is unchanged.

## What to do (every statement is pinned by a guard file; make the sources match)

1. **Repair the `_on` core.** Fix the proofs of everything that consumes
   `SigningExecutionOn` (ExposureSafety.lean, ExposureCert.lean,
   SchedExposure.lean, and `SigningExecution.toOn`). The `_on` statements do not
   change. Every use of `chain_order`/`id_inj` is on blocks of `c`/`c'`, where
   `hAdm` gives admissibility, and where `hAvail` gives `SignedEver`.
   `toOn`: the old `chain_order` gives some `P` with `P.id = C.id` that is
   available; the old `id_inj` gives `P = C`.
2. **New `_ever_on` theorems** (ExposureSafety.lean):
   `exposure_agreement_ever_on`, `exposure_no_early_signing_ever_on`, pinned in
   `Molt/AxiomsPass23.lean`. Re-derive `exposure_agreement_ever` and
   `exposure_no_early_signing_ever` from them via `toOn` (their pins do not change).
3. **Headline** (`Molt/Results.lean`): `Molt.timed_light_client_safety` takes
   `SigningExecutionOn Signed` / `HonestClockOn Signed`, proved by
   `exposure_certified_agreement_on`. `Molt.no_early_signing` becomes an alias of
   `MoltPetit.Model.exposure_no_early_signing_on`. Add Molt aliases
   `exposure_agreement_ever_on` and `exposure_no_early_signing_ever_on`. Update
   both docstrings ("Transported from …").
4. **Rust bridge** (`Rust/TimedResults_rust.lean`, pin `Rust/AxiomsTimed.lean`):
   new implicit `{Formed}`. Use admissibility `RustSigned I crypto n B ∧ Formed B`
   for `hexec`/`hClock`/`hUnf`/`hc`. `hbridge` takes `Formed B`. Add
   `hFormedS`/`hFormedS'` for the suffix blocks. Route: the existing proof with
   `exposure_certified_agreement_on`; lift `hCryptoSig` and `groundedCert_mono`
   to the conjunction.
5. **TS bridge** (`MoltPetit/TS/TimedResults.lean`, pin
   `Molt/AxiomsTSTimed.lean`): the same with `TSSigned n sigOps B ∧ Formed B`.
6. **Loss theorems** `keyrot_loss_agreement`, `sched_loss_agreement`,
   `lockstep_loss_agreement` (pins `Molt/AxiomsKeyRotationLoss.lean`,
   `Molt/AxiomsRotationLoss.lean`): admissibility
   `SignedDeclared n ops registry B ∧ Formed B`. `hbridge` takes `Formed B`.
   Add `hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B` (and for `sc'`).
   Route: `exposure_agreement_on` with `hAdm` from
   `signedDeclared_of_mem_*` and `hFormed`. Note the binder reorder: `Sig sk pk
   ops registry` now come before `hexec`.
7. **Mode 2** `sched_exposure_agreement`, `sched_exposure_certified_agreement`
   (pin `Molt/AxiomsExposureOn.lean`): admissibility
   `SchedAdmissible n schedule ops registry B ∧ Formed B`. The certificate form
   grounds over `SignedDeclared … B ∧ Formed B` (`GroundedCertSched` /
   `GroundedHistorySched`). Generalise `groundedCert_of_sched` /
   `groundedHistory_of_sched` over the signature predicate if they are not
   already generic.
8. Fix any other downstream breakage. Do not weaken any statement.

## Rules

- Do not change any guard file, any pinned statement, or `SigningExecutionOn`.
- No new axioms; no `sorry`; `bash tools/check.sh` must end "check: all green".
- Helpers go in the file where they are used.
- Record progress in `docs/PASS23_PROGRESS.md`.
