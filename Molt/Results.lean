import Molt.Assumptions
import MoltPetit.Results.Results
import MoltPetit.Model.ExposureCert
import MoltPetit.TS.TimedResults

/-!
# What the theorems guarantee: safety and no early signing (paper §6.1–6.2)

The two headline theorems of the timed exposure model, restated in the
paper's vocabulary and transported from the core development:

* `timed_light_client_safety` ← `MoltPetit.Model.exposure_certified_agreement`
* `no_early_signing`          ← `MoltPetit.Model.exposure_no_early_signing`

Per-implementation corollaries (`Rust.rust_timed_certified_agreement`,
`MoltPetit.Model.ts_timed_certified_agreement`) live with the pipelines they
attach to.
-/

namespace Molt

/-! ## The timed model (paper §6.2) -/

/-- What was signed at each **real** slot: `log r` is the set of blocks
whose producer signature was created at real slot `r`. -/
abbrev TimedLog := MoltPetit.Model.TimedLog

/-- `B` exists by real slot `R`: it is the genesis or was signed at some
real slot `≤ R`. -/
def AvailableAt (log : TimedLog) (G : Block) (B : Block) (R : Nat) : Prop :=
  B = G ∨ ∃ r ≤ R, B ∈ log r

/-- The adversary's slot budget (untimed model). -/
abbrev ByzantineBounded := MoltPetit.Model.ByzantineBounded

/-- Key exposure: `exposed s r` — at real slot `r` someone other than its
honest holder can sign under the key that verifies stamp `s`. -/
abbrev Exposure := MoltPetit.Model.Exposure

/-- The signing execution: per-stamp honest uniqueness while unexposed,
id formation (`chain_order`), collision resistance over occurring blocks. -/
abbrev SigningExecution := MoltPetit.Model.SigningExecution

/-- Honest clocks run at most `σ` slots ahead of real time. -/
abbrev HonestClock := MoltPetit.Model.HonestClock

/-- The exposure budget with freshness `φ`. -/
abbrev ExposureBounded := MoltPetit.Model.ExposureBounded

/-- The cumulative exposure budget: every exposure before the window's
freshness deadline counts, however early. -/
abbrev ExposureBoundedEver := MoltPetit.Model.ExposureBoundedEver

/-- Semantic grounded history of a certificate claim. -/
abbrev GroundedHistory := MoltPetit.Model.GroundedHistory

/-- The block at a given height (list indexing). -/
def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h

theorem availableAt_eq_core : AvailableAt = MoltPetit.Model.AvailableAt := rfl
theorem blockAt?_eq_core : blockAt? = MoltPetit.Model.blockAt? := rfl

/-! ## Theorem 1: light-client safety -/

/-- **Timed certified light-client safety** (paper §6.1). What a light client
actually holds is a recursive certificate claim plus a suffix of signed blocks.
Every history the certificate's grounding attests, extended by its suffix, agrees
with the other presentation's at every height that is at least `n` below both
tips. No block needs to be *exposed* in either suffix: the conclusion is about
the attested histories themselves.

Transported from `MoltPetit.Model.exposure_certified_agreement`. -/
theorem timed_light_client_safety {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + faultBudget n + σ + 1 ≤ quorum n + ℓ)
    {Signed : Block → Prop} {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl  : GroundedCert n Signed G cl)
    (hcl' : GroundedCert n Signed G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned  : ∀ B ∈ s₁ :: srest,  Signed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', Signed B)
    (hRecent  : R ≤ sTip.slot  + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc  : GroundedHistory n Signed G cl c)
    (hc' : GroundedHistory n Signed G cl' c')
    {h : Nat}
    (hDeep  : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h := by
  rw [linksOk_eq_core] at hLinks hLinks'
  exact MoltPetit.Model.exposure_certified_agreement hn hexec hClock hBudget hL hL' hbridge hcl hcl'
    hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense'
    hSigned hSigned' hRecent hRecent' hc hc' hDeep hDeep'

/-! ## Theorem 2: forged chains cannot run ahead of real time -/

/-- **No early signing** (paper Theorem 2): no block of a valid chain is
signed more than the budget's lookback `ℓ` slots before its stamp.

Transported from `MoltPetit.Model.exposure_no_early_signing`. -/
alias no_early_signing := MoltPetit.Model.exposure_no_early_signing

/-- Theorem 1, full-chain form under the cumulative budget: no clock
hypothesis (paper §6.1, third remark). -/
alias exposure_agreement_ever := MoltPetit.Model.exposure_agreement_ever

/-- No early signing under the cumulative budget (paper §6.1, third remark). -/
alias exposure_no_early_signing_ever := MoltPetit.Model.exposure_no_early_signing_ever

/-- Theorem 1 for the TypeScript validator (paper §7). -/
alias ts_timed_certified_agreement := MoltPetit.Model.ts_timed_certified_agreement

end Molt
