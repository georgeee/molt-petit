import MoltPetit.Model.KeyStealingLockstepCertGen

/-!
# Pinned statement and axiom audit for per-generation mode-3 certificates

Owned by the reviewer. Do not edit.
-/

open MoltPetit.Model in
example
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
    B = B' :=
  lockstepGen_recent_certified_suffix_agreement hn hP hcl hcl' hTipS hTipS' hLink hLinks hDense hLockS hSigned hLink' hLinks' hDense' hLockS' hSigned' hRecent hRecent' hB hB' hHeight hDeep hDeep'

/-- info: 'MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement
