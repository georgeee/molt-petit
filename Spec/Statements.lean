import Spec.Reference
import Spec.RustBridge

/-!
# The paper's results, as statements

One `def thm_xxx : Prop` per result `paper/molt.tex` cites as `\code{xxx}`;
`Paper/Proofs.lean` proves each as `theorem MoltPaper.xxx : thm_xxx`. Each
docstring names the paper label(s) at which the result is stated or cited.
Every statement is the source text of the development's theorem, so the proof
is the development's theorem itself, checked by Lean up to definitional
unfolding of `thm_xxx`.

Like every file in `Spec/`, this one holds no proof and imports nothing
but `Spec/`, Mathlib and Aeneas (checked by `tools/paper-check.sh`).
-/

set_option linter.unusedVariables false

namespace MoltPaper

/-! ## The protocol model -/

section
open MoltPetit.Model

/-- Paper: cited in sec:rotation. -/
def thm_badKeyrot_single_key_safe_not_enough : Prop :=
  ∃ (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
    (s j : Nat),
    ¬ rented s ∧ ¬ Stolen (producerForSlot n s) j ∧
    badKeyrotOn n Δconf rented Stolen ([] : Chain) s

/-- Paper: ass:rotation-honest. -/
def thm_badSched_single_key_safe_not_enough : Prop :=
  ∃ (n : Nat) (schedule : Nat → Nat) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (s j : Nat),
    ¬ rented s ∧ ¬ Stolen (producerForSlot n s) j ∧
    badSched n schedule rented Stolen s

/-- Paper: cited in sec:lc, sec:limitations. -/
def thm_exposure_agreement_ever_on : Prop :=
  ∀ {n φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B) (hAdm' : ∀ B ∈ c', B ≠ G → Adm B)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length),
    blockAt? c h = blockAt? c' h

/-- Paper: cited in sec:rotation. -/
def thm_exposure_agreement_on : Prop :=
  ∀ {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B) (hAdm' : ∀ B ∈ c', B ≠ G → Adm B)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length),
    blockAt? c h = blockAt? c' h

/-- Paper: cited in sec:rotation. -/
def thm_exposure_certified_agreement_on : Prop :=
  ∀ {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Signed exposed log G)
    (hClock : HonestClockOn Signed σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl : GroundedCert n Signed G cl)
    (hcl' : GroundedCert n Signed G cl')
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
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', Signed B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc : GroundedHistory n Signed G cl c)
    (hc' : GroundedHistory n Signed G cl' c')
    {h : Nat}
    (hDeep : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length),
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h

/-- Paper: cited in sec:lc. -/
def thm_exposure_no_early_signing_ever_on : Prop :=
  ∀ {n σ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) (hSlot : n - 1 ≤ B.slot)
    {r : Nat} (hr : B ∈ log r),
    B.slot ≤ r + (n + maxByzantine n + σ + 1 - quorum n)

/-- Paper: cited in sec:rotation. -/
def thm_exposure_no_early_signing_on : Prop :=
  ∀ {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r),
    B.slot ≤ r + ℓ

/-- Paper: thm:live. -/
def thm_global_liveness : Prop :=
  ∀ {n : Nat} {g : Block} {ss : List Nat}
    (hGen : genesisOk g = true)
    (hChain : List.IsChain (· < ·) (g.slot :: ss))
    (hBudget : ∀ u, u + n ≤ (g.slot :: ss).getLast (List.cons_ne_nil _ _) + 1 →
    (badSlotsIn (fun s => s ∉ g.slot :: ss) u n).card ≤ maxByzantine n),
    validChain n (buildChain g ss) = true ∧
    (buildChain g ss).length = ss.length + 1

/-- Paper: cited in sec:rotation. -/
def thm_groundedCertLock_gen_of_tail : Prop :=
  ∀ {n : Nat} (hn2 : 2 ≤ n) {Signed : Block → Prop}
    {G : Block} {cl : CertClaim} {g : Nat}
    (h : GroundedCertLock n Signed G cl g),
    ∃ t ∈ cl.tail, t.slot = cl.tipSlot ∧ t.keyIndex = g

/-- Paper: cited in sec:rotation. -/
def thm_groundedCertLock_gen_unique : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {Signed : Block → Prop}
    {G : Block} {cl : CertClaim} {g : Nat}
    (h : GroundedCertLock n Signed G cl g)
    {t : Block} (ht : t ∈ cl.tail) (hslot : t.slot = cl.tipSlot),
    t.keyIndex = g

/-- Paper: thm:keyloss. -/
def thm_keyrot_loss_agreement : Prop :=
  ∀ {n Δconf σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B)
    exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)
    (hFormed' : ∀ B ∈ stripSigs sc', B ≠ G → Formed B)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ)
    (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length),
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h

/-- Paper: cited in sec:opmodel, sec:rotation. -/
def thm_liveness_produce_blockK : Prop :=
  ∀ {n Δconf me slot newId : Nat} {contentsHash keyIndex : Nat}
    {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValidK   : validChainK n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
    HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n)
    (hFloor    : keyFloor n c me ≤ keyIndex),
    produceBlock? n me slot newId contentsHash keyIndex c
    = some (nextBlock slot newId contentsHash keyIndex tip) ∧
    validChainK' n Δconf (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = true

/-- Paper: cited in sec:opmodel, sec:rules, sec:rotation. -/
def thm_lockstepGen_recent_certified_suffix_agreement : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {cl cl' : CertClaim} {g g' : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    (hcl' : GroundedCertLock n (SignedDeclared n ops registry) G cl' g')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
    s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hLockS' : lockstepFrom n cl'.tipSlot g' (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + 2 * n < (s₁ :: srest).length)
    (hDeep' : i' + 2 * n < (s₁' :: srest').length),
    B = B'

/-- Paper: cited in sec:rotation. -/
def thm_lockstep_cert_gen_pinned : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {cl : CertClaim} {g : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    {s₁ : Block} {srest : Chain} {sTip : Block} (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ)
    (hMat : ∃ D ∈ s₁ :: srest, (cl.tipSlot / n) * n + n ≤ D.slot + 1),
    g = rosterGen (cl.tipSlot / n)

/-- Paper: cited in sec:rotation. -/
def thm_lockstep_declares_rosterGen : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ),
    ∀ W, ∀ B ∈ stripSigs sc, B.slot / n = W →
    (∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1) →
    B.keyIndex = rosterGen W

/-- Paper: cited in sec:opmodel, sec:rotation. -/
def thm_lockstep_loss_agreement : Prop :=
  ∀ {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)
    (hFormed' : ∀ B ∈ stripSigs sc', B ≠ G → Formed B)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ)
    (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length),
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h

/-- Paper: cited in sec:opmodel, sec:rotation. -/
def thm_lockstep_recent_certified_suffix_agreement : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {cl cl' : CertClaim} {g g' : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    (hcl' : GroundedCertLock n (SignedDeclared n ops registry) G cl' g')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
    s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hLockS' : lockstepFrom n cl'.tipSlot g' (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length),
    B = B'

/-- Paper: thm:lock. -/
def thm_lockstep_recent_tip_ancestor_mem : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B),
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B

/-- Paper: thm:forge. -/
def thm_no_early_signing : Prop :=
  ∀ {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r),
    B.slot ≤ r + ℓ

/-- Paper: thm:live. -/
def thm_production_liveness : Prop :=
  ∀ {n me slot newId : Nat} {contentsHash keyIndex : Nat}
    {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValid    : validChain n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
    HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n),
    produceBlock? n me slot newId contentsHash keyIndex c
    = some (nextBlock slot newId contentsHash keyIndex tip)

/-- Paper: cited in sec:rotation. -/
def thm_same_block_same_prefix : Prop :=
  ∀ {record : SlotRecord} (hId : IdInjective record)
    {c c' : Chain}
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hP : ParentLinked c) (hP' : ParentLinked c'),
    ∀ {m : Nat} {B : Block},
    blockAt? c m = some B →
    blockAt? c' m = some B →
    ∀ {k : Nat}, k ≤ m →
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P

/-- Paper: thm:sched. -/
def thm_sched_exposure_agreement : Prop :=
  ∀ {n σ ℓ φ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : TimedLog} {G : Block} {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B)
    (schedExposed n schedule Controlled Stolen) log G)
    (hClock : HonestClockOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B) σ
    (schedExposed n schedule Controlled Stolen) log)
    (hBudget : ExposureBounded n ℓ φ (schedExposed n schedule Controlled Stolen))
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SchedAdmissible n schedule ops registry B → Formed B →
    ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)
    (hFormed' : ∀ B ∈ stripSigs sc', B ≠ G → Formed B)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ)
    (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length),
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h

/-- Paper: thm:sched. -/
def thm_sched_exposure_certified_agreement : Prop :=
  ∀ {n σ ℓ φ : Nat} {schedule : Nat → Nat}
    (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : TimedLog} {G : Block} {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B)
    (schedExposed n schedule Controlled Stolen) log G)
    (hClock : HonestClockOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B) σ
    (schedExposed n schedule Controlled Stolen) log)
    (hBudget : ExposureBounded n ℓ φ (schedExposed n schedule Controlled Stolen))
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SchedAdmissible n schedule ops registry B → Formed B →
    ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl : GroundedCertSched n schedule (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl)
    (hcl' : GroundedCertSched n schedule
    (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl')
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
    (hSigned : ∀ B ∈ s₁ :: srest, SchedAdmissible n schedule ops registry B ∧ Formed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', SchedAdmissible n schedule ops registry B ∧ Formed B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc : GroundedHistorySched n schedule
    (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl c)
    (hc' : GroundedHistorySched n schedule
    (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl' c')
    {h : Nat}
    (hDeep : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length),
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h

/-- Paper: cited in sec:opmodel, sec:rotation. -/
def thm_sched_loss_agreement : Prop :=
  ∀ {n σ ℓ φ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)
    (hFormed' : ∀ B ∈ stripSigs sc', B ≠ G → Formed B)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ)
    (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length),
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h

/-- Paper: cited in sec:rotation. -/
def thm_sched_oldkey_fork_stale : Prop :=
  ∀ {σ sk pk : Type} {n : Nat} {schedule : Nat → Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    {J now Δ : Nat}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
    (hEraOver : ∀ s, schedule s ≤ J → s + Δ < now)
    {t : Block} (hTip : (stripSigs sc).getLast? = some t)
    (hJt : t.keyIndex ≤ J),
    ¬ now ≤ t.slot + Δ

/-- Paper: cited in sec:rotation. -/
def thm_sched_recent_certified_suffix_agreement_horizon : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    {cl cl' : CertClaim}
    (hcl  : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl)
    (hcl' : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest ).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
    s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
    s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hPinS' : schedPinned schedule (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁  :: srest ) i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁  :: srest ).length)
    (hDeep' : i' + n < (s₁' :: srest').length),
    B = B'

/-- Paper: cited in sec:rotation. -/
def thm_sched_recent_genesis_agreement_horizon : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1),
    ∃ P : Block, blockAt? (stripSigs sc ) 0 = some P ∧
    blockAt? (stripSigs sc') 0 = some P

/-- Paper: cited in sec:rotation. -/
def thm_sched_recent_tip_ancestor_agreement_horizon : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B'),
    B = B'

/-- Paper: cited in sec:rotation. -/
def thm_sched_recent_tip_ancestor_mem_horizon : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B),
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B

/-- Paper: cited in sec:intro, sec:results, sec:impl. -/
def thm_ts_timed_certified_agreement : Prop :=
  ∀ {σ ℓ φ : Nat}
    {n : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block} {R : Nat}
    {sigOps : MoltPetit.SigOps} {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => TSSigned n sigOps B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => TSSigned n sigOps B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    (hbridge : ∀ ⦃B : Block⦄, TSSigned n sigOps B → Formed B → ∃ r ≤ R, B ∈ log r)
    {certOps certOps' : MoltPetit.CertOps}
    (hUnf : ∀ hc : MoltPetit.RawCertificate, certOps.verify hc = true →
    ∃ cl : CertClaim, certOps.claim hc = toTSClaim cl ∧
    GroundedCert n (fun B => TSSigned n sigOps B ∧ Formed B) G cl)
    (hUnf' : ∀ hc : MoltPetit.RawCertificate, certOps'.verify hc = true →
    ∃ cl : CertClaim, certOps'.claim hc = toTSClaim cl ∧
    GroundedCert n (fun B => TSSigned n sigOps B ∧ Formed B) G cl)
    {h h' : MoltPetit.RawCertificate} {sc sc' : SignedChain MoltPetit.RawSignature}
    (hval : MoltPetit.validateCertifiedChain n sigOps certOps
    (.cc h (toTSSigned sc)) = true)
    (hval' : MoltPetit.validateCertifiedChain n sigOps certOps'
    (.cc h' (toTSSigned sc')) = true)
    {s₁ s₁' : Block} {srest srest' : Chain}
    (hsc : stripSigs sc = s₁ :: srest)
    (hsc' : stripSigs sc' = s₁' :: srest')
    {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hFormedS : ∀ B ∈ s₁ :: srest, Formed B)
    (hFormedS' : ∀ B ∈ s₁' :: srest', Formed B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {cl cl' : CertClaim}
    (hcl : certOps.claim h = toTSClaim cl)
    (hcl' : certOps'.claim h' = toTSClaim cl')
    {c c' : Chain}
    (hc : GroundedHistory n (fun B => TSSigned n sigOps B ∧ Formed B) G cl c)
    (hc' : GroundedHistory n (fun B => TSSigned n sigOps B ∧ Formed B) G cl' c')
    {k : Nat}
    (hDeep : k + n < (c ++ s₁ :: srest).length)
    (hDeep' : k + n < (c' ++ s₁' :: srest').length),
    blockAt? (c ++ s₁ :: srest) k = blockAt? (c' ++ s₁' :: srest') k

/-- Paper: cited in sec:rotation. -/
def thm_window_shared_prefix : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord} {u : Nat}
    (hHonest : HonestSlotsUniqueOn u n bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {tip tip' : Block} (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hMat : u + n ≤ tip.slot + 1) (hMat' : u + n ≤ tip'.slot + 1)
    (hBudgetU : (badSlotsIn bad u n).card ≤ maxByzantine n)
    {k : Nat} {B : Block} (hB : blockAt? c k = some B) (hBu : B.slot < u),
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P

end

section
open MoltPetit.Model Classical

/-- Paper: cited in sec:rotation. -/
def LockstepPackage.thm_toGen : Prop :=
  ∀ {n : Nat} {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat} (hn : 0 < n)
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    (hSurj : ∀ j, ∃ W, rosterGen W = j),
    LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T

/-- Paper: cited in sec:rotation. -/
def thm_genBound_of_preRetirementBound : Prop :=
  ∀ {n : Nat} {rosterGen : Nat → Nat}
    {stolenAt : Nat → Nat → Nat → Prop} {T : Nat}
    (hEr : ErasureTimedLock n rosterGen stolenAt)
    (hLive : ∀ j, (preRetirementTheftProducers n rosterGen stolenAt j).card ≤ T),
    ∀ j : Nat, ((Finset.range n).filter (fun i => stolenOf stolenAt i j)).card ≤ T

/-- Paper: thm:lock-gen. -/
def thm_lockstepGen_recent_genesis_agreement : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : 2 * n < (stripSigs sc).length) (hLong' : 2 * n < (stripSigs sc').length),
    ∃ P : Block, blockAt? (stripSigs sc) 0 = some P ∧ blockAt? (stripSigs sc') 0 = some P

/-- Paper: thm:lock-gen. -/
def thm_lockstepGen_recent_tip_ancestor_mem : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : 2 * n < (stripSigs sc).length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block} (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - 2 * n) = some B),
    ∃ i', i' + 2 * n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B

/-- Paper: cited in sec:rotation. -/
def thm_lockstepGen_shared_prefix_sharp : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hle : sTip.slot ≤ sTip'.slot)
    {k : Nat} {B : Block} (hB : blockAt? (stripSigs sc) k = some B)
    (hDeep : k + n + (sTip.slot + 1) % n < (stripSigs sc).length),
    ∃ P : Block, blockAt? (stripSigs sc) k = some P ∧ blockAt? (stripSigs sc') k = some P

/-- Paper: cited in sec:rotation. -/
def thm_lockstep_window_declares_rosterGen : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig} (hVal : validSignedChainLock n ops registry sc = true)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ)
    (W : Nat) (hMat : ∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1)
    {B : Block} (hB : B ∈ stripSigs sc) (hBW : B.slot / n = W),
    B.keyIndex = rosterGen W

end

section
open MoltPetit.Model MoltPetit.Model.ProverTiming

/-- Paper: cited in sec:liveness. -/
def thm_slot_time_necessary : Prop :=
  ∀ {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hpb0 : 0 ≤ perBlock) (hpb : perBlock < τ)
    (hτ : τ < recommendedSlot n baseline perBlock)
    {u : ℚ} (hsteady : nextBacklog baseline perBlock τ u = u),
    n < peakSuffix baseline perBlock τ u

/-- Paper: cited in sec:liveness. -/
def thm_slot_time_sufficient : Prop :=
  ∀ {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hb : 0 ≤ baseline) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    (hτ : recommendedSlot n baseline perBlock ≤ τ)
    {u₀ : ℚ} (hu₀ : 0 ≤ u₀) (hub₀ : u₀ ≤ n / 2),
    ∀ j, backlog baseline perBlock τ u₀ j ≤ n / 2 ∧
    peakSuffix baseline perBlock τ (backlog baseline perBlock τ u₀ j) ≤ n

end

/-! ## The reference verifier -/

section
open Molt

/-- Paper: cited in sec:rotation. -/
def thm_badKeyrot_lossOnly : Prop :=
  ∀ (n Δconf : Nat) (rented : ByzantineSlots)
    (c₀ : Chain),
    badKeyrot n Δconf rented (fun _ _ => False) c₀ = rented

/-- Paper: cited in sec:rotation. -/
def thm_badSched_lossOnly : Prop :=
  ∀ (n : Nat) (schedule : Nat → Nat)
    (rented : ByzantineSlots),
    badSched n schedule rented (fun _ _ => False) = rented

/-- Paper: thm:lock. -/
def thm_lockstep_client_safety : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen
    honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
    ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
    ((stripSigs sc').length - 1 - n) = some B'),
    B = B'

/-- Paper: thm:lock-gen. -/
def thm_lockstep_client_safety_gen : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen
    honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : 2 * n < (stripSigs sc ).length)
    (hLong' : 2 * n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
    ((stripSigs sc ).length - 1 - 2 * n) = some B)
    (hB' : blockAt? (stripSigs sc')
    ((stripSigs sc').length - 1 - 2 * n) = some B'),
    B = B'

/-- Paper: cited in sec:rotation. -/
def thm_lockstep_client_safety_timed : Prop :=
  ∀ {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageTimed n rosterGen ops registry rented stolenAt
    honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : 2 * n < (stripSigs sc ).length)
    (hLong' : 2 * n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
    ((stripSigs sc ).length - 1 - 2 * n) = some B)
    (hB' : blockAt? (stripSigs sc')
    ((stripSigs sc').length - 1 - 2 * n) = some B'),
    B = B'

/-- Paper: thm:lc. -/
def thm_timed_light_client_safety : Prop :=
  ∀ {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Signed exposed log G)
    (hClock : HonestClockOn Signed σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + faultBudget n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
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
    (hDeep' : h + n < (c' ++ s₁' :: srest').length),
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h

end

/-! ## The Rust implementation -/

section
open Aeneas Std Result Rust

/-- Paper: cited in sec:intro, sec:opmodel, sec:results, sec:impl. -/
def thm_rust_timed_certified_agreement : Prop :=
  ∀ {σ ℓ φ : Nat}
    {n : Std.U64} (hn : 1 ≤ n.val)
    {C} (I : molt_petit.Crypto C) (crypto crypto' : C)
    {exposed : MoltPetit.Model.Exposure} {log : MoltPetit.Model.TimedLog}
    {G : MoltPetit.Model.Block} {R : Nat}
    {Formed : MoltPetit.Model.Block → Prop}
    (hexec : MoltPetit.Model.SigningExecutionOn (fun B => RustSigned I crypto n B ∧ Formed B) exposed log G)
    (hClock : MoltPetit.Model.HonestClockOn (fun B => RustSigned I crypto n B ∧ Formed B) σ exposed log)
    (hBudget : MoltPetit.Model.ExposureBounded n.val ℓ φ exposed)
    (hL : n.val ≤ ℓ + 1) (hL' : n.val + MoltPetit.Model.maxByzantine n.val + σ + 1 ≤ MoltPetit.Model.quorum n.val + ℓ)
    (hbridge : ∀ ⦃B : MoltPetit.Model.Block⦄, RustSigned I crypto n B → Formed B → ∃ r ≤ R, B ∈ log r)
    (hCryptoSig : ∀ b, RustSigned I crypto' n b → RustSigned I crypto n b)
    (hUnf : ∀ cert : molt_petit.Hash, I.cert_verify crypto cert = ok true →
    ∃ cl, I.cert_claim crypto cert = ok cl ∧
    MoltPetit.Model.GroundedCert n.val (fun B => RustSigned I crypto n B ∧ Formed B) G (toModelClaim cl))
    (hUnf' : ∀ cert : molt_petit.Hash, I.cert_verify crypto' cert = ok true →
    ∃ cl, I.cert_claim crypto' cert = ok cl ∧
    MoltPetit.Model.GroundedCert n.val
    (fun B => RustSigned I crypto' n B ∧ Formed B) G (toModelClaim cl))
    {cert cert' : molt_petit.Hash} {suffix suffix' : molt_petit.SignedChain}
    (hval  : molt_petit.validate_certified_chain I n crypto (.CC cert suffix) = ok true)
    (hval' : molt_petit.validate_certified_chain I n crypto' (.CC cert' suffix') = ok true)
    {sr1 sr1' : molt_petit.Block} {srtl srtl' : molt_petit.Chain}
    (hstr  : molt_petit.strip_sigs suffix  = ok (.Cons sr1 srtl))
    (hstr' : molt_petit.strip_sigs suffix' = ok (.Cons sr1' srtl'))
    {sTip sTip' : MoltPetit.Model.Block}
    (hTipS  : (toModelBlock sr1  :: toModelChain srtl).getLast?  = some sTip)
    (hTipS' : (toModelBlock sr1' :: toModelChain srtl').getLast? = some sTip')
    (hFormedS  : ∀ B ∈ toModelBlock sr1  :: toModelChain srtl,  Formed B)
    (hFormedS' : ∀ B ∈ toModelBlock sr1' :: toModelChain srtl', Formed B)
    (hRecent  : R ≤ sTip.slot  + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {cl cl' : molt_petit.CertClaim}
    (hcl  : I.cert_claim crypto  cert  = ok cl)
    (hcl' : I.cert_claim crypto' cert' = ok cl')
    {c c' : MoltPetit.Model.Chain}
    (hc  : MoltPetit.Model.GroundedHistory n.val (fun B => RustSigned I crypto n B ∧ Formed B) G (toModelClaim cl) c)
    (hc' : MoltPetit.Model.GroundedHistory n.val
    (fun B => RustSigned I crypto' n B ∧ Formed B) G
    (toModelClaim cl') c')
    {h : Nat}
    (hDeep  : h + n.val < (c  ++ toModelBlock sr1  :: toModelChain srtl).length)
    (hDeep' : h + n.val < (c' ++ toModelBlock sr1' :: toModelChain srtl').length),
    MoltPetit.Model.blockAt? (c ++ toModelBlock sr1 :: toModelChain srtl) h =
    MoltPetit.Model.blockAt? (c' ++ toModelBlock sr1' :: toModelChain srtl') h

/-- Paper: cited in sec:impl. -/
def thm_rust_valid_chain_k_sound : Prop :=
  ∀ {n : Std.U64} {c : molt_petit.Chain}
    (hn : 0 < n.val)
    (h : molt_petit.valid_chain_k n c = ok true),
    MoltPetit.Model.ValidChain n.val (toModelChain c) ∧
    MoltPetit.Model.KeyIndexMonotone n.val (toModelChain c)

/-- Paper: cited in sec:impl. -/
def thm_rust_valid_chain_sound : Prop :=
  ∀ {n : Std.U64} {c : molt_petit.Chain}
    (h : molt_petit.valid_chain n c = ok true),
    MoltPetit.Model.ValidChain n.val (toModelChain c)

end

section
open Aeneas Std Result Rust molt_petit

/-- Paper: cited in sec:impl, sec:limitations. -/
def thm_valid_chain_be_validChain : Prop :=
  ∀ {n q : U64} {c : Chain}
    (hq : quorum n = ok q)
    (h : valid_chain_be UB () n q (toChainG c) = ok true),
    MoltPetit.Model.ValidChain n.val (toModelChain c)

end

end MoltPaper
