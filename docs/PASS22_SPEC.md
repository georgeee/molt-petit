# Pass 22: admissibility-restricted core, and mode 2 against theft from Theorem 1

## Why

Mode 2's theft theorem (`sched_recent_tip_ancestor_agreement_horizon`) rests on
an operational surface (`SchedUnforgeable`) and an untimed horizon budget. The
timed core (Theorem 1) would give mode 2 a windowed, timed budget for free, but
its custody hypothesis `SigningExecution` is claimed for *every* logged block,
and a thief holding a retired key does sign blocks at old stamps. Those blocks
are harmless only because the mode-2 validator rejects them. So the custody
hypothesis needs to be claimed only for blocks a validator admits.

## What to prove (all statements pinned by `Molt/AxiomsExposureOn.lean`)

1. `MoltPetit.Model.exposure_no_early_signing_on`, `exposure_agreement_on`
   (ExposureSafety.lean): the same as `exposure_no_early_signing` /
   `exposure_agreement`, with `SigningExecutionOn Adm`, `HonestClockOn Adm`, and
   `hAdm : ∀ B ∈ c, B ≠ G → Adm B` (and for `c'`).
   Route: re-run the existing proofs; every use of `honest_once` / the clock is
   on a block of `c` or `c'` other than `G`, where `hAdm` supplies `Adm`. It is
   acceptable (and preferred) to prove the `_on` versions first and re-derive the
   existing unrestricted theorems as the `Adm := fun _ => True` instance, as long
   as the existing pinned statements do not change.
2. `exposure_certified_agreement_on` (ExposureCert.lean): Adm := `Signed`.
   Every block of a grounded history and of the suffix satisfies `Signed`
   (`GroundedHistory.signed`, `hSigned`), so reduce to item 1 as the existing
   proof reduces to `exposure_agreement`.
3. `sched_exposure_agreement` (SchedExposure.lean): instance of item 1 with
   Adm := `SchedAdmissible n schedule ops registry`. Every block of an accepted
   `validSignedChainSched` chain is admissible: `signedDeclared_of_mem_sched`
   for the signature, `rotated_key_dead_sched*`-style pin lemma for
   `schedule B.slot ≤ B.keyIndex`. `ValidChain` from
   `validChain_of_validSignedChainSched`; availability from `hbridge`. Mirror
   the proof of `sched_loss_agreement`.
4. `sched_exposure_certified_agreement` (SchedExposure.lean): instance of item 2
   with Signed := `SchedAdmissible …`. Needs:
   `GroundedCertSched n schedule (SignedDeclared …) G cl →
    GroundedCert n (SchedAdmissible …) G cl` (induction; the pin is a premise of
   each constructor), and the same for histories
   (`GroundedHistorySched` → `GroundedHistory` with `pinned` + `signed` giving
   admissibility of every block).

## Rules

- Do not change any pinned statement or any guard file.
- No new axioms; no `sorry`; `bash tools/check.sh` must end "check: all green".
- Helpers go in the file where they are used.
