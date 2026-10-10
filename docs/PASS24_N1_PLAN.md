# Pass 24 task (e): the N1 repair, step by step

This file is the whole recipe. Do not explore the repository to rediscover it.
Each turn: read this file and `docs/PASS24_PROGRESS.md`, take the FIRST
unchecked step below, do only that step, build only the module named in it,
commit, tick it in `docs/PASS24_PROGRESS.md`, stop.

Build one module (cached dependencies make this take seconds to a few minutes):

    T=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin
    env PATH="$T:$PATH" $T/lake build <Module> > /tmp/p24-build.log 2>&1; echo rc=$?; grep -A6 "error" /tmp/p24-build.log | head -60

Commit after every step, even a partial one (`git commit -am "pass24(e) WIP: <step>"`).
An uncommitted edit is lost when your turn is cut.

## What changed and why

`SignedHashInjective` used to be assumed over every declared-signed block
(`SignedDeclared n ops registry`). That is not a cryptographic assumption, so
the Spec now assumes it only over formed blocks:
`SignedFormed n ops registry Formed B := SignedDeclared n ops registry B ∧ Formed B`
(in `Spec/Model.lean`; `fun B => SignedDeclared n ops registry B ∧ Formed B` is
the same thing by `rfl`). The three lockstep packages take `(Formed : Block → Prop)`
right after `registry`. Chain theorems get
`(hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)` and the primed twin.

A finished example of this exact repair already exists: `MoltPetit/Model/KeyRotationLossSchedLock.lean:52`.

## The four patterns

**P1, two-chain theorem with `(hHash : SignedHashInjective (SignedDeclared n ops registry) G)`.**
1. Add `{Formed : Block → Prop}` right after `{G : Block}` in the binders.
2. Change the hypothesis to `(hHash : SignedHashInjective (SignedFormed n ops registry Formed) G)`.
3. Add `(hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)` and
   `(hFormed' : ∀ B ∈ stripSigs sc', B ≠ G → Formed B)` right after `hVal'`.
4. Replace the two `hSig` lines, which look like
   `fun b hb => Or.inr (signedDeclared_of_mem_XXX hVal hb)`, by
   ```
   have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedFormed n ops registry Formed b :=
     fun b hb => by
       by_cases h : b = G
       · exact Or.inl h
       · exact Or.inr ⟨signedDeclared_of_mem_XXX hVal hb, hFormed b hb h⟩
   ```
   with the same twin for `sc'` / `hVal'` / `hFormed'`.
5. Wherever the theorem calls another P1 theorem, pass `hFormed hFormed'` in the new position.

**P2, certificate theorem whose `Signed` argument is `SignedDeclared n ops registry`**
(in `GroundedCertSched …`, `GroundedCertLock …`, `hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared …`).
1. Add `{Formed : Block → Prop}` after `{G : Block}`.
2. Replace every `SignedDeclared n ops registry` in the binders (hHash, hcl, hcl', hSigned, hSigned') by `SignedFormed n ops registry Formed`.
3. In the proof, `hCov : ∀ B ∈ c ++ s₁ :: srest, SignedFormed … B` now carries both halves. Where the proof needs the declared part,
   use `(hCov B hB).1`. For example, `exists_signedChain_of_covered (Sig := Sig) fun B hB => (hCov B hB).1`.
   When calling a P1 theorem on the rebuilt chains `sc`/`sc'`, supply
   `(fun b hb _ => (hCov b (hstrip ▸ hb)).2)` for `hFormed`, and the same with `hCov'`/`hstrip'` for `hFormed'`.
   (If `hstrip ▸ hb` does not elaborate, use `by rw [hstrip] at hb; exact (hCov b hb).2`.)
   Where a local `hSig` is built from `signedDeclared_of_mem_schedCore hVal hb`, build it from `hCov` instead, as
   `MoltPetit/Model/KeyStealingCert.lean:647` does: `rw [hstrip]; exact fun b hb => Or.inr (hCov b hb)`.

**P3, development package `PackageA` / `PackageATimed`** (`KeyStealingScheduleBudget.lean:190`, `KeyStealingScheduleTimed.lean:313`).
1. Add `(Formed : Block → Prop)` right after `(registry : KeyRegistry pk)` in the structure parameters.
2. Change the field to `hashInj : SignedHashInjective (SignedFormed n ops registry Formed) G`.
3. Every use `PackageA n sched ops registry rented …` becomes `PackageA n sched ops registry Formed rented …`; theorems about it add
   `{Formed : Block → Prop}` and, where they call a P1 theorem, `hFormed hFormed'` (P1 step 3).
   Their certificate theorems follow P2.

**P4, a theorem that `Paper/Proofs.lean` cites** (`MoltPaper.X := @MoltPetit.Model.X`).
Its binder list must equal the pinned `thm_X` in `Spec/Statements.lean` exactly, in the same order.
Copy the binders from the Spec statement. Do not change the Spec.

## Steps (dependency order)

Tick each in `docs/PASS24_PROGRESS.md` under "Modules fixed" when the module builds.

1. `MoltPetit/Model/KeyStealingSchedule.lean`: `sched_deep_block_agreement` (line ~174), P1.
   Build `MoltPetit.Model.KeyStealingSchedule`.
2. `MoltPetit/Results/KeyStealingScheduleResults.lean`: `sched_deep_block_agreement_of_length` (~90),
   `sched_recent_tip_ancestor_agreement` (~144), `sched_recent_tip_ancestor_mem` (~186), P1 (forwarders: P1 steps 1–3 and 5 only).
   Build `MoltPetit.Results.KeyStealingScheduleResults`.
3. `MoltPetit/Model/KeyStealingScheduleCert.lean`: `sched_deep_block_agreement_core` (~265) P1,
   `sched_deep_block_agreement_core_of_length` (~303) P1 forwarder, `sched_recent_certified_suffix_agreement` (~546) P2.
   Build `MoltPetit.Model.KeyStealingScheduleCert`.
4. `MoltPetit/Model/KeyStealingScheduleBudget.lean`: `PackageA` and every theorem in the file, P3.
   Build `MoltPetit.Model.KeyStealingScheduleBudget`.
5. `MoltPetit/Model/KeyStealingLockstep.lean`: every theorem with `(hP : LockstepPackage n rosterGen ops registry rented …)`
   (`toPackageA` ~218 and the theorems at ~248, 423, 504, 535) gets `{Formed : Block → Prop}` after `{G : Block}` and
   `LockstepPackage n rosterGen ops registry Formed rented …`; `toPackageA` targets `PackageA … registry Formed rented …`.
   P4 for `lockstep_declares_rosterGen` and `lockstep_recent_tip_ancestor_mem`; P1 steps 3–5 where a theorem has two chains.
   Build `MoltPetit.Model.KeyStealingLockstep`.
6. `MoltPetit/Model/KeyStealingScheduleHorizon.lean`: the five theorems at ~249, 310, 367, 416, 473. P1, and P4 for the three without `_core`.
   Build `MoltPetit.Model.KeyStealingScheduleHorizon`.
7. `MoltPetit/Model/KeyStealingScheduleCertHorizon.lean`: `sched_recent_certified_suffix_agreement_horizon`, P2 + P4.
   Build `Molt.AxiomsSchedCertHorizon` (reviewer pin file; it checks this theorem against the Spec. Do not edit it.).
8. `MoltPetit/Model/KeyStealingScheduleTimed.lean`: `PackageATimed`, P3. Build `MoltPetit.Model.KeyStealingScheduleTimed`.
9. `MoltPetit/Model/KeyStealingLockstepCert.lean`. Build it, fix errors with P1–P4.
10. `MoltPetit/Model/KeyStealingLockstepGen.lean` (the `hSig` at ~496 is P1 step 4). Build it.
11. `MoltPetit/Model/KeyStealingLockstepCertGen.lean`. Build `Molt.AxiomsLockstepCertGen` (reviewer pin file; do not edit it).
12. `MoltPetit/Model/KeyStealingLockstepTimed.lean`. Build it.
13. `MoltPetit/Model/KeyStealingHorizon.lean`, `MoltPetit/Model/KeyStealingCertAnchored.lean`. Build each; most likely nothing to do.
14. `Molt/Rotation.lean`: `scheduled_client_safety` (~296) P1 + P4. Build `Molt.Rotation`.
15. `Molt/ClientRule.lean`, `Molt/CertClientRule.lean`, `Molt/MaxSync.lean`, `Molt/SyncInduction.lean`, `Molt/LockstepCert.lean`,
    `Molt/LockstepGen.lean`, `MoltPetit/Results/AxiomsLockstepGen.lean`, `MoltPetit/Results/Axioms.lean`, `Molt/Axioms.lean`:
    build each in this order and fix with P1–P4. These are mostly forwarders and `#print axioms` lines.
16. `Paper.Proofs`. Build it. Any error here is a P4 mismatch: fix the development theorem's binders, never the Spec.

Do not touch the mode-1 (`KeyStealingSigned`, `GroundedCertK`) theorems, the TS or Rust results, or anything in `Spec/`.
If a step's theorem looks unprovable in its pinned form, write it under "STOP" in `docs/PASS24_PROGRESS.md` and stop.
