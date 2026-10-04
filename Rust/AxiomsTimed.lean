import Rust.TimedResults_rust

/-!
# Pinned statement and axiom audit for the Rust timed certified theorem

Owned by the reviewer. Do not edit. The `example` fixes the exact type of
`Rust.rust_timed_certified_agreement`; the guard fails the build if the proof
is incomplete or uses any non-classical axiom.
-/

open Aeneas Std Result Rust in
example {σ ℓ φ : Nat}
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
    (hDeep' : h + n.val < (c' ++ toModelBlock sr1' :: toModelChain srtl').length) :
    MoltPetit.Model.blockAt? (c ++ toModelBlock sr1 :: toModelChain srtl) h =
      MoltPetit.Model.blockAt? (c' ++ toModelBlock sr1' :: toModelChain srtl') h :=
  rust_timed_certified_agreement hn I crypto crypto' hexec hClock hBudget hL hL' hbridge hCryptoSig hUnf hUnf' hval hval' hstr hstr' hTipS hTipS' hFormedS hFormedS' hRecent hRecent' hcl hcl' hc hc' hDeep hDeep'

/-- info: 'Rust.rust_timed_certified_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_timed_certified_agreement
