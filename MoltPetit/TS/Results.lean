import MoltPetit.Model.Grounded
import MoltPetit.Results.Results

/-!
# MoltPetit — corollaries for the TypeScript implementation

The light-client safety guarantees specialized to the **Thales-emitted
TypeScript** validator (`Miniconsensus`/`MoltPetit.validateCertifiedChain`),
obtained from the Lean model by the soundness bridge (`TSBridge`, `Grounded`).

These are *corollaries* of the model-level results in `Results.lean`: the
bridge shows the emitted validator accepts only data the semantic model
accepts, and the safety/agreement theorems then apply. The Rust analogue is
`Results_rust.lean`.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- The light-client theorem: recent tips share their n-deep ancestor
-- ---------------------------------------------------------------------------

/--
**The light-client theorem.** A verifier whose clock reads `now` holds
two certified chains, both accepted by the TypeScript
`validateCertifiedChain` (certificate verification + suffix signature
checks + structural suffix validation), both with suffixes longer than
`n`, and both passing the **tight recency rule**: tip within `n` slots
of `now`. If the tips sit at the same height, the ancestor `n` blocks
below each tip is **the same block**.

The signature assumption is only the recency-scoped
`SigUnforgeableRecent` — honest-slot uniqueness is promised *only for
chains meeting the recency bar*, which is exactly what the timed model
proves survives a coercing adversary (`Model/Timed.lean`,
`forged_suffix_time_bound`: a fork forged above a block first signed at
`r₀` cannot reach stamp `r₀ + s` before real slot `≈ r₀ + 2s`, so a
recency-passing fork carries at most `≈ 2·maxByzantine < n + 1`
harvested blocks — too few to fake an `n`-deep ancestor). Stale chains
get no promise; the rule "valid ∧ tip within `n` of now ∧ `n`-deep" is
the trustworthy predicate.

The equal-tip-height hypothesis is what "the" ancestor means: two
recent chains may legitimately differ in height by a few blocks, and
then their respective `n`-back ancestors sit at different heights; the
common-height form is `ts_recent_certified_suffix_agreement`.
-/
theorem ts_recent_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {signed : SigningLog}
    {sigOps : MoltPetit.SigOps} {G : Block} {now : Nat}
    (hBudget : ByzantineBounded n bad)
    (hSig : SigUnforgeableRecent n bad (TSSigned n sigOps) signed now n)
    (hHash : SignedHashInjective (TSSigned n sigOps) G)
    {certOps certOps' : MoltPetit.CertOps}
    (hUnf : ∀ hc : MoltPetit.RawCertificate, certOps.verify hc = true →
      ∃ cl : CertClaim, certOps.claim hc = toTSClaim cl ∧ GroundedCert n (TSSigned n sigOps) G cl)
    (hUnf' : ∀ hc : MoltPetit.RawCertificate, certOps'.verify hc = true →
      ∃ cl : CertClaim, certOps'.claim hc = toTSClaim cl ∧ GroundedCert n (TSSigned n sigOps) G cl)
    {h h' : MoltPetit.RawCertificate} {sc sc' : SignedChain MoltPetit.RawSignature}
    (hval : MoltPetit.validateCertifiedChain n sigOps certOps
              (.cc h (toTSSigned sc)) = true)
    (hval' : MoltPetit.validateCertifiedChain n sigOps certOps'
              (.cc h' (toTSSigned sc')) = true)
    {s₁ s₁' : Block} {srest srest' : Chain}
    (hsc  : stripSigs sc  = s₁  :: srest)
    (hsc' : stripSigs sc' = s₁' :: srest')
    (hLong  : n < (s₁  :: srest).length)
    (hLong' : n < (s₁' :: srest').length)
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    -- the tight recency rule: both tips within n slots of the clock
    (hRecent  : now ≤ sTip.slot  + n)
    (hRecent' : now ≤ sTip'.slot + n)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (s₁  :: srest)  ((s₁  :: srest).length  - 1 - n) = some B)
    (hB' : blockAt? (s₁' :: srest') ((s₁' :: srest').length - 1 - n) = some B') :
    B = B' := by
  obtain ⟨hcv,  hsg,  hsfx⟩  := ts_validateCertifiedChain_sound hval
  obtain ⟨hcv', hsg', hsfx'⟩ := ts_validateCertifiedChain_sound hval'
  rw [hsc]  at hsfx
  rw [hsc'] at hsfx'
  obtain ⟨cl,  hclEq,  hG⟩  := hUnf  h  hcv
  obtain ⟨cl', hclEq', hG'⟩ := hUnf' h' hcv'
  rw [hclEq]  at hsfx
  rw [hclEq'] at hsfx'
  -- suffix signatures, from the sigsOk component of validation
  have hSigned : ∀ B ∈ s₁ :: srest, TSSigned n sigOps B := by
    have hs := ts_sigsOk_signed hsg
    rw [hsc] at hs
    exact hs
  have hSigned' : ∀ B ∈ s₁' :: srest', TSSigned n sigOps B := by
    have hs := ts_sigsOk_signed hsg'
    rw [hsc'] at hs
    exact hs
  -- heights: tips and the n-back ancestors, read off the link structure
  obtain ⟨hLink,  hLinks,  -⟩ := ts_validateSuffix_sound hTipS  hsfx
  obtain ⟨hLink', hLinks', -⟩ := ts_validateSuffix_sound hTipS' hsfx'
  obtain ⟨hL1,  -, -⟩ := hLink
  obtain ⟨hL1', -, -⟩ := hLink'
  have hTipAt  : blockAt? (s₁  :: srest)  ((s₁  :: srest).length  - 1) = some sTip :=
    blockAt_getLast hTipS
  have hTipAt' : blockAt? (s₁' :: srest') ((s₁' :: srest').length - 1) = some sTip' :=
    blockAt_getLast hTipS'
  have hT  := linksOk_height_at hLinks  hTipAt
  have hT' := linksOk_height_at hLinks' hTipAt'
  have hBh  := linksOk_height_at hLinks  hB
  have hBh' := linksOk_height_at hLinks' hB'
  exact ts_recent_certified_suffix_agreement hn hBudget hSig hHash hG hG'
    hsfx hsfx' hSigned hSigned' hTipS hTipS' hRecent hRecent'
    hB hB' (by omega) (by omega) (by omega)

/--
**Light-client theorem, production side.** Node 1 *produced* its
certified chain with `produceBlockCert` (sign → compact against the
certificate store → validate → ship), starting from a verifying stored
certificate and a stored suffix held as a model signed chain. Any
verifier holding a `validateCertifiedChain`-accepted chain whose tip —
like the produced chain's — passes the tight recency rule agrees with
the producer on the ancestor `n` below the tip.
-/
theorem ts_recent_produced_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {signed : SigningLog}
    {sigOps : MoltPetit.SigOps} {G : Block} {now : Nat}
    (hBudget : ByzantineBounded n bad)
    (hSig : SigUnforgeableRecent n bad (TSSigned n sigOps) signed now n)
    (hHash : SignedHashInjective (TSSigned n sigOps) G)
    {certOps certOps' : MoltPetit.CertOps}
    (hUnf : ∀ hc : MoltPetit.RawCertificate, certOps.verify hc = true →
      ∃ cl : CertClaim, certOps.claim hc = toTSClaim cl ∧ GroundedCert n (TSSigned n sigOps) G cl)
    (hUnf' : ∀ hc : MoltPetit.RawCertificate, certOps'.verify hc = true →
      ∃ cl : CertClaim, certOps'.claim hc = toTSClaim cl ∧ GroundedCert n (TSSigned n sigOps) G cl)
    -- node 1 produced its chain from a verifying stored certificate
    {me slot newId : Nat} {contentsHash keyIndex : Nat}
    {sk : MoltPetit.RawSecretKey}
    {cert : MoltPetit.RawCertificate}
    {msc : SignedChain MoltPetit.RawSignature}
    (hcv : certOps.verify cert = true)
    {h : MoltPetit.RawCertificate} {sfx : MoltPetit.SignedChain}
    (hp : MoltPetit.produceBlockCert n me slot newId contentsHash keyIndex sk sigOps certOps
            cert (toTSSigned msc) = .cc h sfx)
    -- node 2 validated its chain
    {h' : MoltPetit.RawCertificate} {sc' : SignedChain MoltPetit.RawSignature}
    (hval' : MoltPetit.validateCertifiedChain n sigOps certOps'
              (.cc h' (toTSSigned sc')) = true) :
    producerForSlot n slot = me ∧
    ∃ msfx : SignedChain MoltPetit.RawSignature,
      sfx = toTSSigned msfx ∧
      ∀ {s₁ s₁' : Block} {srest srest' : Chain},
        stripSigs msfx = s₁ :: srest →
        stripSigs sc'  = s₁' :: srest' →
        n < (s₁ :: srest).length →
        n < (s₁' :: srest').length →
        ∀ {sTip sTip' : Block},
          (s₁ :: srest).getLast? = some sTip →
          (s₁' :: srest').getLast? = some sTip' →
          now ≤ sTip.slot + n →
          now ≤ sTip'.slot + n →
          sTip.height = sTip'.height →
          ∀ {B B' : Block},
            blockAt? (s₁ :: srest) ((s₁ :: srest).length - 1 - n) = some B →
            blockAt? (s₁' :: srest') ((s₁' :: srest').length - 1 - n) = some B' →
            B = B' := by
  obtain ⟨mcl, hclEq, -⟩ := hUnf cert hcv
  obtain ⟨msfx, rfl⟩ := ts_produceBlockCert_image hclEq hp
  obtain ⟨hMine, hval⟩ := ts_produceBlockCert_sound hp
  refine ⟨hMine, msfx, rfl, ?_⟩
  intro s₁ s₁' srest srest' hs hs' hL hL' sTip sTip' hT hT' hR hR' hTH B B' hB hB'
  exact ts_recent_tip_ancestor_agreement hn hBudget hSig hHash hUnf hUnf'
    hval hval' hs hs' hL hL' hT hT' hR hR' hTH hB hB'

/--
**Consistency form of the light-client theorem: the `n`-deep ancestor of
a recent chain lies on every recent chain.**

Pointwise equality of `n`-deep ancestors across recent chains is false
for a benign reason: two recent valid chains may differ in tip height
(the same chain observed one block apart already does), and then their
respective ancestors sit at different heights — parent and child, not
equals. What *is* true, and what this theorem states: the `n`-deep
ancestor `B` of the chain with the lower-or-equal tip is **a block of
the other chain as well**, at least `n` deep there too. All recent
chains agree on their common prefix up to `n` below the lower tip.

`hReach` (**the second suffix starts at least `n` below the first
tip**, `s₁'.height + n ≤ sTip.height`) is a technicality of how the
statement is built, not an operational constraint. The
certificate/suffix boundary is a *presentation* of the chain, not a
property of it: none of the protocol's guarantees depend on suffix
length beyond the certificate, and the same chain state is equally a
`cert + n`-block suffix and an earlier `cert' + 2n`-block one — the
grounding derivation attests a claim at every fold, so certificates
exist at every depth, and `produceBlockCert`'s compaction merely picks
the shortest presentation its registry currently supports. A holder
that retains the dropped blocks can re-present the same chain at any
lower compaction level. `hReach` records only which presentation this
statement talks about, since a suffix cannot exhibit a block packaged
inside its certificate.
-/
theorem ts_recent_tip_ancestor_mem
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {signed : SigningLog}
    {sigOps : MoltPetit.SigOps} {G : Block} {now : Nat}
    (hBudget : ByzantineBounded n bad)
    (hSig : SigUnforgeableRecent n bad (TSSigned n sigOps) signed now n)
    (hHash : SignedHashInjective (TSSigned n sigOps) G)
    {certOps certOps' : MoltPetit.CertOps}
    (hUnf : ∀ hc : MoltPetit.RawCertificate, certOps.verify hc = true →
      ∃ cl : CertClaim, certOps.claim hc = toTSClaim cl ∧ GroundedCert n (TSSigned n sigOps) G cl)
    (hUnf' : ∀ hc : MoltPetit.RawCertificate, certOps'.verify hc = true →
      ∃ cl : CertClaim, certOps'.claim hc = toTSClaim cl ∧ GroundedCert n (TSSigned n sigOps) G cl)
    {h h' : MoltPetit.RawCertificate} {sc sc' : SignedChain MoltPetit.RawSignature}
    (hval : MoltPetit.validateCertifiedChain n sigOps certOps
              (.cc h (toTSSigned sc)) = true)
    (hval' : MoltPetit.validateCertifiedChain n sigOps certOps'
              (.cc h' (toTSSigned sc')) = true)
    {s₁ s₁' : Block} {srest srest' : Chain}
    (hsc  : stripSigs sc  = s₁  :: srest)
    (hsc' : stripSigs sc' = s₁' :: srest')
    (hLong  : n < (s₁  :: srest).length)
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    -- the tight recency rule: both tips within n slots of the clock
    (hRecent  : now ≤ sTip.slot  + n)
    (hRecent' : now ≤ sTip'.slot + n)
    -- chain 1 has the lower (or equal) tip …
    (hLe : sTip.height ≤ sTip'.height)
    -- … and chain 2's suffix starts at least n below chain 1's tip
    (hReach : s₁'.height + n ≤ sTip.height)
    {B : Block}
    (hB : blockAt? (s₁ :: srest) ((s₁ :: srest).length - 1 - n) = some B) :
    ∃ i', i' + n < (s₁' :: srest').length ∧
      blockAt? (s₁' :: srest') i' = some B := by
  obtain ⟨hcv,  hsg,  hsfx⟩  := ts_validateCertifiedChain_sound hval
  obtain ⟨hcv', hsg', hsfx'⟩ := ts_validateCertifiedChain_sound hval'
  rw [hsc]  at hsfx
  rw [hsc'] at hsfx'
  obtain ⟨cl,  hclEq,  hG⟩  := hUnf  h  hcv
  obtain ⟨cl', hclEq', hG'⟩ := hUnf' h' hcv'
  rw [hclEq]  at hsfx
  rw [hclEq'] at hsfx'
  have hSigned : ∀ B ∈ s₁ :: srest, TSSigned n sigOps B := by
    have hs := ts_sigsOk_signed hsg
    rw [hsc] at hs
    exact hs
  have hSigned' : ∀ B ∈ s₁' :: srest', TSSigned n sigOps B := by
    have hs := ts_sigsOk_signed hsg'
    rw [hsc'] at hs
    exact hs
  obtain ⟨hLink,  hLinks,  -⟩ := ts_validateSuffix_sound hTipS  hsfx
  obtain ⟨hLink', hLinks', -⟩ := ts_validateSuffix_sound hTipS' hsfx'
  obtain ⟨hL1,  -, -⟩ := hLink
  obtain ⟨hL1', -, -⟩ := hLink'
  have hTipAt  : blockAt? (s₁  :: srest)  ((s₁  :: srest).length  - 1) = some sTip :=
    blockAt_getLast hTipS
  have hTipAt' : blockAt? (s₁' :: srest') ((s₁' :: srest').length - 1) = some sTip' :=
    blockAt_getLast hTipS'
  have hT  := linksOk_height_at hLinks  hTipAt
  have hT' := linksOk_height_at hLinks' hTipAt'
  have hBh := linksOk_height_at hLinks hB
  -- chain 2's block at the ancestor's height
  set i' : Nat := sTip.height - n - s₁'.height with hi'
  have hi'lt : i' < (s₁' :: srest').length := by omega
  obtain ⟨X, hX⟩ : ∃ X, blockAt? (s₁' :: srest') i' = some X := by
    unfold blockAt?
    exact ⟨(s₁' :: srest')[i']'hi'lt, List.getElem?_eq_getElem hi'lt⟩
  have hXh := linksOk_height_at hLinks' hX
  have hBX : B = X :=
    ts_recent_certified_suffix_agreement hn hBudget hSig hHash hG hG'
      hsfx hsfx' hSigned hSigned' hTipS hTipS' hRecent hRecent'
      hB hX (by omega) (by omega) (by omega)
  exact ⟨i', by omega, hBX ▸ hX⟩



end MoltPetit.Model
