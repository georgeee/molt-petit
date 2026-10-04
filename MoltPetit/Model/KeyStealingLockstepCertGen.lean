import MoltPetit.Model.KeyStealingLockstepCert
import MoltPetit.Model.KeyStealingLockstepGen

/-!
# Mode 3 certificates under the per-generation census

THE STATEMENT OF `lockstepGen_recent_certified_suffix_agreement` IS FIXED. Its
exact type is pinned by `Molt/AxiomsLockstepCertGen.lean`; prove it, do not
change it. It is `lockstep_recent_certified_suffix_agreement` with the
cumulative package `LockstepPackage` replaced by the per-generation
`LockstepPackageGen`, at confirmation depth `2n` as in
`lockstepGen_recent_tip_ancestor_agreement`.
-/

namespace MoltPetit.Model

/-- **Certificate-level mode-3 safety under the per-generation census.** -/
theorem lockstepGen_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
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
    (hDeep' : i' + 2 * n < (s₁' :: srest').length) :
    B = B' := by
  obtain ⟨c, sc, hstrip, hValL, hHead, hfullTip, hLen, _, _⟩ :=
    groundedCertLock_signedChain hn hcl hTipS hLink hLinks hDense hLockS hSigned
  obtain ⟨c', sc', hstrip', hValL', hHead', hfullTip', hLen', _, _⟩ :=
    groundedCertLock_signedChain hn hcl' hTipS' hLink' hLinks' hDense' hLockS' hSigned'
  have hBfull : blockAt? (stripSigs sc) (c.length + i) = some B := by
    rw [hstrip]
    unfold blockAt? at hB ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? (stripSigs sc') (c'.length + i') = some B' := by
    rw [hstrip']
    unfold blockAt? at hB' ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB'
  have hkEq : c'.length + i' = c.length + i := by omega
  rw [hkEq] at hB'full
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := lockstepGen_shared_prefix_deep hn hP hValL hValL' hfullTip hfullTip'
      hRecent hRecent' hle hBfull (k := c.length + i)
      (by rw [hstrip, List.length_append]; omega)
    rw [hBfull] at hPc
    rw [hB'full] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · obtain ⟨P, hPc', hPc⟩ := lockstepGen_shared_prefix_deep hn hP hValL' hValL hfullTip' hfullTip
      hRecent' hRecent hle hB'full (k := c.length + i)
      (by rw [hstrip', List.length_append]; omega)
    rw [hBfull] at hPc
    rw [hB'full] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

end MoltPetit.Model
