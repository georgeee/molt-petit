import Rust.Results_rust
import MoltPetit.Model.ExposureCert

/-!
# Timed certified light-client safety for the shipped Rust validator

The Rust form of `MoltPetit.Model.exposure_certified_agreement`: two certified
chains the Rust `validate_certified_chain` accepts, checked by a verifier at
real slot `R` within `n` real slots of both tips, agree at every height that
is at least `n` below both tips, over every history the two certificates'
groundings attest. No exposure hypothesis, no `SigUnforgeableRecent` residue:
the signature assumption is the timed bridge `hbridge` (EUF-CMA plus
causality) over the Rust signature predicate.

THE STATEMENT OF `rust_timed_certified_agreement` IS FIXED. Its exact type is
pinned by `Rust/AxiomsTimed.lean`. Prove it; do not change it.
-/

open Aeneas Std Result

namespace Rust

/-- `GroundedHistory` is monotone in its signature predicate. -/
theorem groundedHistory_mono {n : Nat} {S₁ S₂ : MoltPetit.Model.Block → Prop}
    {G : MoltPetit.Model.Block} (hmono : ∀ b, S₁ b → S₂ b)
    {cl : MoltPetit.Model.CertClaim} {c : MoltPetit.Model.Chain}
    (hc : MoltPetit.Model.GroundedHistory n S₁ G cl c) :
    MoltPetit.Model.GroundedHistory n S₂ G cl c :=
  ⟨hc.valid, hc.head, hc.tip, hc.tail_eq, hc.len_eq,
   fun B hB => match hc.signed B hB with
     | Or.inl hG => Or.inl hG
     | Or.inr hS => Or.inr (hmono B hS)⟩

/-- **Timed certified light-client safety, Rust validator.** -/
theorem rust_timed_certified_agreement {σ ℓ φ : Nat}
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
      MoltPetit.Model.blockAt? (c' ++ toModelBlock sr1' :: toModelChain srtl') h := by
  obtain ⟨cl0, stripped, hcl0, hstrip, hcv, hsg, hsfx⟩ :=
    validate_certified_chain_sound hval
  obtain ⟨cl0', stripped', hcl0', hstrip', hcv', hsg', hsfx'⟩ :=
    validate_certified_chain_sound hval'
  rw [hstr] at hstrip; injection hstrip with hstrip; subst hstrip
  rw [hstr'] at hstrip'; injection hstrip' with hstrip'; subst hstrip'
  rw [hcl] at hcl0; injection hcl0 with hcl0; subst hcl0
  rw [hcl'] at hcl0'; injection hcl0' with hcl0'; subst hcl0'
  obtain ⟨clm, hclEq, hG⟩ := hUnf cert hcv
  obtain ⟨clm', hclEq', hG'0⟩ := hUnf' cert' hcv'
  rw [hcl] at hclEq; injection hclEq with hclEq; subst hclEq
  rw [hcl'] at hclEq'; injection hclEq' with hclEq'; subst hclEq'
  have hCryptoSigConj : ∀ b, (RustSigned I crypto' n b ∧ Formed b) → (RustSigned I crypto n b ∧ Formed b) :=
    fun b hb => ⟨hCryptoSig b hb.1, hb.2⟩
  have hG' := groundedCert_mono hCryptoSigConj hG'0
  have hSigned0 := sigs_ok_signed suffix hsg hstr
  have hSigned0' := sigs_ok_signed suffix' hsg' hstr'
  rw [toModelChain_cons] at hSigned0 hSigned0'
  have hSigned : ∀ B ∈ toModelBlock sr1 :: toModelChain srtl,
      RustSigned I crypto n B ∧ Formed B :=
    fun B hB => ⟨hSigned0 B hB, hFormedS B hB⟩
  have hSigned' : ∀ B ∈ toModelBlock sr1' :: toModelChain srtl',
      RustSigned I crypto n B ∧ Formed B :=
    fun B hB => ⟨hCryptoSig B (hSigned0' B hB), hFormedS' B hB⟩
  obtain ⟨hLink, hLinks, hDense⟩ := validate_suffix_sound hTipS hsfx
  obtain ⟨hLink', hLinks', hDense'⟩ := validate_suffix_sound hTipS' hsfx'
  have hc'' := groundedHistory_mono hCryptoSigConj hc'
  exact MoltPetit.Model.exposure_certified_agreement_on hn hexec hClock hBudget hL hL'
    (fun B ⟨h1, h2⟩ => hbridge h1 h2) hG hG'
    hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned'
    hRecent hRecent' hc hc'' hDeep hDeep'

end Rust
