import Rust.Results_rust
import MoltPetit.Model.TimedSafetyCert

/-!
# Timed certified light-client safety for the shipped Rust validator

The Rust form of `MoltPetit.Model.timed_certified_agreement`: two certified
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

/-- **Timed certified light-client safety, Rust validator.** -/
theorem rust_timed_certified_agreement
    {n : Std.U64} (hn : 1 ≤ n.val)
    {C} (I : molt_petit.Crypto C) (crypto crypto' : C)
    {bad : MoltPetit.Model.ByzantineSlots} {log : MoltPetit.Model.TimedLog}
    {G : MoltPetit.Model.Block} {R : Nat}
    (hexec : MoltPetit.Model.TimedExecution n.val bad log G)
    (hBudget : MoltPetit.Model.ByzantineBounded n.val bad)
    (hbridge : ∀ ⦃B : MoltPetit.Model.Block⦄, RustSigned I crypto n B → ∃ r ≤ R, B ∈ log r)
    (hCryptoSig : ∀ b, RustSigned I crypto' n b → RustSigned I crypto n b)
    (hUnf : ∀ cert : molt_petit.Hash, I.cert_verify crypto cert = ok true →
      ∃ cl, I.cert_claim crypto cert = ok cl ∧
        MoltPetit.Model.GroundedCert n.val (RustSigned I crypto n) G (toModelClaim cl))
    (hUnf' : ∀ cert : molt_petit.Hash, I.cert_verify crypto' cert = ok true →
      ∃ cl, I.cert_claim crypto' cert = ok cl ∧
        MoltPetit.Model.GroundedCert n.val (RustSigned I crypto' n) G (toModelClaim cl))
    {cert cert' : molt_petit.Hash} {suffix suffix' : molt_petit.SignedChain}
    (hval  : molt_petit.validate_certified_chain I n crypto (.CC cert suffix) = ok true)
    (hval' : molt_petit.validate_certified_chain I n crypto' (.CC cert' suffix') = ok true)
    {sr1 sr1' : molt_petit.Block} {srtl srtl' : molt_petit.Chain}
    (hstr  : molt_petit.strip_sigs suffix  = ok (.Cons sr1 srtl))
    (hstr' : molt_petit.strip_sigs suffix' = ok (.Cons sr1' srtl'))
    {sTip sTip' : MoltPetit.Model.Block}
    (hTipS  : (toModelBlock sr1  :: toModelChain srtl).getLast?  = some sTip)
    (hTipS' : (toModelBlock sr1' :: toModelChain srtl').getLast? = some sTip')
    (hRecent  : R ≤ sTip.slot  + n.val)
    (hRecent' : R ≤ sTip'.slot + n.val)
    {cl cl' : molt_petit.CertClaim}
    (hcl  : I.cert_claim crypto  cert  = ok cl)
    (hcl' : I.cert_claim crypto' cert' = ok cl')
    {c c' : MoltPetit.Model.Chain}
    (hc  : MoltPetit.Model.GroundedHistory n.val (RustSigned I crypto n) G (toModelClaim cl) c)
    (hc' : MoltPetit.Model.GroundedHistory n.val (RustSigned I crypto' n) G
      (toModelClaim cl') c')
    {h : Nat}
    (hDeep  : h + n.val < (c  ++ toModelBlock sr1  :: toModelChain srtl).length)
    (hDeep' : h + n.val < (c' ++ toModelBlock sr1' :: toModelChain srtl').length) :
    MoltPetit.Model.blockAt? (c ++ toModelBlock sr1 :: toModelChain srtl) h =
      MoltPetit.Model.blockAt? (c' ++ toModelBlock sr1' :: toModelChain srtl') h := by
  sorry

end Rust
