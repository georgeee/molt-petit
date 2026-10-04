import MoltPetit.Model.ExposureCert
import MoltPetit.Model.KeyStealingSchedule
import MoltPetit.Model.KeyStealingScheduleCert
import MoltPetit.Model.KeyRotationLossSchedLock

/-!
# Mode 2 (scheduled rotation) against theft, from Theorem 1

Mode 2's validator admits a block only if it verifies under its declared key
version *and* that version meets the public schedule's floor:
`schedule B.slot ≤ B.keyIndex`. A key stolen before the schedule retires it can
therefore sign only stamps whose floor it still meets; once the schedule moves
past it, no validator admits what it signs.

So the custody claim of Theorem 1 (`SigningExecution`) only has to hold for
*admissible* blocks (`SigningExecutionOn SchedAdmissible`), and the natural
exposure is `schedExposed`: stamp `s` is exposed at real slot `r` when its
seat is controlled at `r`, or some version of that seat's key that still meets
`s`'s floor has been stolen by `r`. The budget is the same windowed, timed
`ExposureBounded` as Theorem 1's: a stolen key counts only for the stamps it
can still sign, and only while it is held.

Both theorems below are instances of the admissibility-restricted core
(`exposure_agreement_on`, `exposure_certified_agreement_on`).

THE STATEMENTS OF `sched_exposure_agreement` AND
`sched_exposure_certified_agreement` ARE FIXED. Their exact types are pinned by
`Molt/AxiomsExposureOn.lean`. Prove them; do not change them.
-/

namespace MoltPetit.Model

/-- What the mode-2 validator admits, per block: a signature verifying under
the declared registry entry, and a declared version meeting the schedule. -/
def SchedAdmissible {Sig sk pk : Type} (n : Nat) (schedule : Nat → Nat)
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (B : Block) : Prop :=
  SignedDeclared n ops registry B ∧ schedule B.slot ≤ B.keyIndex

/-- Mode-2 exposure. `Controlled p r`: seat `p` is run by the adversary at real
slot `r`. `Stolen p j r`: version `j` of seat `p`'s key is held by someone
other than its honest holder at real slot `r`. Stamp `s` is exposed at `r` iff
its producer is controlled, or a version of its key that still meets `s`'s
schedule floor is stolen. -/
def schedExposed (n : Nat) (schedule : Nat → Nat) (Controlled : Nat → Nat → Prop)
    (Stolen : Nat → Nat → Nat → Prop) : Exposure :=
  fun s r => Controlled (producerForSlot n s) r ∨
    ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j r

/-- **Mode 2 against theft: timed agreement for the mode-2 validator.** -/
theorem sched_exposure_agreement {n σ ℓ φ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn (SchedAdmissible n schedule ops registry)
      (schedExposed n schedule Controlled Stolen) log G)
    (hClock : HonestClockOn (SchedAdmissible n schedule ops registry) σ
      (schedExposed n schedule Controlled Stolen) log)
    (hBudget : ExposureBounded n ℓ φ (schedExposed n schedule Controlled Stolen))
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SchedAdmissible n schedule ops registry B →
      ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ)
    (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length) :
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h := by
  sorry

/-- **Mode 2 against theft: timed certified agreement.** The light client holds
a scheduled certificate claim (`GroundedCertSched`, every grounded block
pinned) plus a suffix of admissible blocks. -/
theorem sched_exposure_certified_agreement {n σ ℓ φ : Nat} {schedule : Nat → Nat}
    (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn (SchedAdmissible n schedule ops registry)
      (schedExposed n schedule Controlled Stolen) log G)
    (hClock : HonestClockOn (SchedAdmissible n schedule ops registry) σ
      (schedExposed n schedule Controlled Stolen) log)
    (hBudget : ExposureBounded n ℓ φ (schedExposed n schedule Controlled Stolen))
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SchedAdmissible n schedule ops registry B →
      ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl)
    (hcl' : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned : ∀ B ∈ s₁ :: srest, SchedAdmissible n schedule ops registry B)
    (hSigned' : ∀ B ∈ s₁' :: srest', SchedAdmissible n schedule ops registry B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc : GroundedHistorySched n schedule (SignedDeclared n ops registry) G cl c)
    (hc' : GroundedHistorySched n schedule (SignedDeclared n ops registry) G cl' c')
    {h : Nat}
    (hDeep : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h := by
  sorry

end MoltPetit.Model
