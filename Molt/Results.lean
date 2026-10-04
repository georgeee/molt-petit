import Molt.Assumptions
import MoltPetit.Results.Results
import MoltPetit.Model.TimedSig
import MoltPetit.Model.ExposureCert

/-!
# What the theorems guarantee: safety and forged time (paper §6.1–6.2)

The two headline theorems of the static-key protocol, restated in the
paper's vocabulary and transported from the core development:

* `light_client_safety` ← `MoltPetit.Model.recent_certified_suffix_agreement`
* `forged_time_bound`   ← `MoltPetit.Model.forged_suffix_time_bound`

Per-implementation corollaries (`rust_recent_tip_ancestor_mem`,
`ts_recent_tip_ancestor_mem`, …) live with the pipelines they attach to.
-/

namespace Molt

/-! ## The timed model (paper §6.2) -/

/-- What was signed at each **real** slot: at an honest real slot, at most
the producer's own current block; at a bad one, anything the adversary
extracts under that producer's key. -/
abbrev TimedLog := MoltPetit.Model.TimedLog

/-- `B` exists by real slot `R`: it is the genesis or was signed at some
real slot `≤ R`. -/
def AvailableAt (log : TimedLog) (G : Block) (B : Block) (R : Nat) : Prop :=
  B = G ∨ ∃ r ≤ R, B ∈ log r

/-- The timed execution model; its `chain_order` field is the formal
residue of the id-formation contract (a block can be signed only once its
parent is available, because the parent's id preimage contains the
parent's signature). -/
abbrev TimedExecution := MoltPetit.Model.TimedExecution

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

/-- The exposure budget with freshness `ρ`. -/
abbrev ExposureBounded := MoltPetit.Model.ExposureBounded

/-- Semantic grounded history of a certificate claim. -/
abbrev GroundedHistory := MoltPetit.Model.GroundedHistory

/-- The block at a given height (list indexing). -/
def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h

theorem availableAt_eq_core : AvailableAt = MoltPetit.Model.AvailableAt := rfl
theorem blockAt?_eq_core : blockAt? = MoltPetit.Model.blockAt? := rfl

/-! ## Theorem 1: light-client safety -/

/-- **Light-client safety** (paper Theorem 1). Under the fault budget,
recency-scoped signatures, hash injectivity over occurring blocks, and
certificate grounding: two certified chains whose suffixes validate
against their claims, whose blocks all carry verifying signatures, and
whose tips are recent, agree on every block at the same global height
that has `n` blocks above it within each suffix.

Transported from `MoltPetit.Model.recent_certified_suffix_agreement`. -/
theorem light_client_safety
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {signed : SigningLog}
    {Signed : Block → Prop} {G : Block} {now Δ : Nat}
    (hBudget : FaultBounded n bad)
    (hSig : SigUnforgeableRecent n bad Signed signed now Δ)
    (hHash : SignedHashInjective Signed G)
    {cl cl' : CertClaim}
    (hcl  : GroundedCert n Signed G cl)
    (hcl' : GroundedCert n Signed G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned  : ∀ B ∈ s₁ :: srest,  Signed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', Signed B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁ :: srest)   i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  rw [linksOk_eq_core] at hLinks hLinks'
  exact MoltPetit.Model.recent_certified_suffix_agreement hn hBudget hSig hHash
    hcl hcl' hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense'
    hSigned hSigned' hRecent hRecent' hB hB' hHeight hDeep hDeep'

/-- **Timed certified light-client safety** (paper §6.1). What a light client
actually holds is a recursive certificate claim plus a suffix of signed blocks.
Every history the certificate's grounding attests, extended by its suffix, agrees
with the other presentation's at every height that is at least `n` below both
tips. No block needs to be *exposed* in either suffix: the conclusion is about
the attested histories themselves.

Transported from `MoltPetit.Model.exposure_certified_agreement`. -/
theorem timed_light_client_safety {n ρ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBounded n ρ exposed)
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
    (hRecent  : R ≤ sTip.slot  + ρ)
    (hRecent' : R ≤ sTip'.slot + ρ)
    {c c' : Chain}
    (hc  : GroundedHistory n Signed G cl c)
    (hc' : GroundedHistory n Signed G cl' c')
    {h : Nat}
    (hDeep  : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h := by
  rw [linksOk_eq_core] at hLinks hLinks'
  exact MoltPetit.Model.exposure_certified_agreement hn hexec hBudget hbridge hcl hcl'
    hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense'
    hSigned hSigned' hRecent hRecent' hc hc' hDeep hDeep'

/-! ## Theorem 2: forged chains cannot run ahead of real time -/

/-- **No early signing** (paper Theorem 2): no block of a valid chain past
the first window is signed more than `n + faultBudget + σ + 1 - quorum`
slots before its stamp.

Transported from `MoltPetit.Model.exposure_no_early_signing`. -/
alias no_early_signing := MoltPetit.Model.exposure_no_early_signing

/-- **Forged suffixes take twice their span in real time** (paper
Theorem 2). If every chain block above fork point `F` (first signed at
real slot `r₀`) was only ever signed at bad real slots, and the chain is
available at real slot `R`, then

    quorum n * ((tip.slot - F.slot) / n) ≤ faultBudget n * ((rNow - r₀) / n + 1).

With `quorum ≈ 2·faultBudget`: a chain cannot be forged to slot `B + s`
before real slot `≈ B + 2s` (`forged_suffix_lag`; the from-genesis form
is `forged_chain_time_bound`).

Transported from `MoltPetit.Model.forged_suffix_time_bound`. -/
theorem forged_time_bound {n : Nat} (hn : 2 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : FaultBounded n bad)
    {c : Chain} (hValid : ValidChain n c)
    (hGprev : G.prev = none)
    {rNow : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B rNow)
    {k₀ : Nat} (hk₀ : 1 ≤ k₀) {F : Block} (hF : blockAt? c k₀ = some F)
    {r₀ : Nat} (hFr : F ∈ log r₀) (hFmin : ∀ r < r₀, F ∉ log r)
    (hForged : ∀ B ∈ c, F.slot < B.slot → ∀ r, B ∈ log r → bad r)
    {tip : Block} (hTip : c.getLast? = some tip) :
    quorum n * ((tip.slot - F.slot) / n) ≤
      faultBudget n * ((rNow - r₀) / n + 1) :=
  MoltPetit.Model.forged_suffix_time_bound hn hexec hBudget hValid hGprev
    hAvail hk₀ hF hFr hFmin hForged hTip

/-- From-genesis form of `forged_time_bound`: a fully forged chain
claiming tip slot `s` cannot exist before real slot `≈ 2s`. -/
alias forged_chain_time_bound := MoltPetit.Model.forged_chain_time_bound

/-- The lag reading of `forged_time_bound`. -/
alias forged_suffix_lag := MoltPetit.Model.forged_suffix_lag

/-- Assumption 2(c) derived in the timed model from plain EUF-CMA plus
the no-back-dating residue (paper §6.2 and the appendix). -/
alias sigUnforgeableRecent_of_timed :=
  MoltPetit.Model.sigUnforgeableRecent_of_timed

/-- No back-dating onto an honest stamp: a block whose stamp is honest
was signed at the real slot equal to its stamp (paper appendix). -/
abbrev NoBackdate := MoltPetit.Model.NoBackdate

/-- The stamped signing log read off a real-time log (paper appendix). -/
noncomputable abbrev projectSigned := MoltPetit.Model.projectSigned

/-- No-back-dating is genuinely independent of the structural timed
model: a machine-checked `n = 2` execution satisfies every
`TimedExecution` field yet violates `NoBackdate` (paper appendix). -/
alias noBackdate_independent := MoltPetit.Model.noBackdate_independent

end Molt
