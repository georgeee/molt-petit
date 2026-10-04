import Rust.Bridge
import MoltPetit.Model.Grounded
import MoltPetit.Results.Results

/-!
# Corollaries for the Rust implementation

Guarantees specialized to the **Charon + Aeneas-extracted Rust** code
(`molt_petit.*` in `Rust/Extracted.lean`), obtained from the Lean model by the
equivalence bridge (`Rust/Bridge.lean`). The Rust analogue of
`MoltPetit/TS/Results.lean`.

Two kinds appear here:
* *transferred model results* — a fact proved once for the model (in
  `MoltPetit/Results/Results.lean`, `Safety.lean`, `Liveness.lean`) and carried to
  the Rust functions through the `*_corr` equivalence lemmas;
* *implementation guarantees* about the extracted code itself.

All depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

open Aeneas Std Result

namespace Rust

/-- **`GroundedCert` is monotone in its signature predicate.** Weakening
`Signed` (e.g. transporting one `Crypto` dictionary's signatures to another's,
when the two agree on signature verification) preserves groundedness. This lets
the two-dictionary safety corollaries below compare a chain grounded under one
dictionary with a chain grounded under another. -/
theorem groundedCert_mono {n : Nat} {S₁ S₂ : MoltPetit.Model.Block → Prop}
    {G : MoltPetit.Model.Block} (hmono : ∀ b, S₁ b → S₂ b) :
    ∀ {cl : MoltPetit.Model.CertClaim}, MoltPetit.Model.GroundedCert n S₁ G cl →
      MoltPetit.Model.GroundedCert n S₂ G cl := by
  intro cl h
  induction h with
  | genesis hgo hs0 => exact MoltPetit.Model.GroundedCert.genesis hgo hs0
  | extend cl b _ hH hSlt hPrev hSig hDense ih =>
      exact MoltPetit.Model.GroundedCert.extend cl b ih hH hSlt hPrev (hmono b hSig) hDense

/-- **Leader range (transferred).** The Rust `producer_for_slot` computes the
model leader `slot mod n`. -/
theorem rust_producer_for_slot (n slot : U64) (hn : 0 < n.val) :
    ∃ r, molt_petit.producer_for_slot n slot = ok r ∧
         r.val = MoltPetit.Model.producerForSlot n.val slot.val :=
  molt_petit.spec_ok_exists (producer_for_slot_corr n slot hn)

/-- **Window-count equivalence (chain-level, transferred).** The Rust
`window_count` computes the model `windowCount` over the projected chain --- the
first recursive correspondence of the chain bridge (`Rust/Bridge.lean`), on the
way to a full `valid_chain` soundness corollary. -/
theorem rust_window_count (c : molt_petit.Chain) (u len : Std.U64) {w : Std.U64}
    (h : molt_petit.window_count c u len = ok w) :
    w.val = MoltPetit.Model.windowCount (toModelChain c) u.val len.val :=
  window_count_corr c u len h

/-- **Quorum/Byzantine bound (transferred from the model).** Derived from the
*model* theorem `MoltPetit.Model.quorum_plus_byzantine_le` through the `quorum`/
`max_byzantine` equivalence — every window has at least `quorum` honest slots,
now as a statement about the Rust functions. -/
theorem rust_quorum_plus_byzantine_le
    (n : U64) (hn : 1 ≤ n.val) (h : 2 * n.val + 2 ≤ U64.max) :
    ∃ q f, molt_petit.quorum n = ok q ∧ molt_petit.max_byzantine n = ok f ∧
           q.val + f.val ≤ n.val := by
  obtain ⟨q, hq, hqv⟩ := molt_petit.spec_ok_exists (quorum_corr n h)
  obtain ⟨f, hf, hfv⟩ := molt_petit.spec_ok_exists (max_byzantine_corr n hn)
  refine ⟨q, f, hq, hf, ?_⟩
  rw [hqv, hfv]
  exact MoltPetit.Model.quorum_plus_byzantine_le n.val

/-- **Verifier soundness (chain-level, transferred).** A chain the Rust
`valid_chain` accepts projects to a semantically `ValidChain` in the model. -/
theorem rust_valid_chain_sound {n : Std.U64} {c : molt_petit.Chain}
    (h : molt_petit.valid_chain n c = ok true) :
    MoltPetit.Model.ValidChain n.val (toModelChain c) :=
  MoltPetit.Model.validChain_sound (valid_chain_sound h)

/-- **Indexed-validator soundness (implementation guarantee).** A chain the
Rust `valid_chain_k` accepts projects to a semantically valid, key-index
monotone chain — the Rust analogue of `ts_validChainK_sound`; on a full chain
the `≤` in-force pin follows (`inForcePinned_of_validChainK`), so this is the
full-chain enforcement of the key-rotation validator `validChainK'` on the
Rust path. -/
theorem rust_valid_chain_k_sound {n : Std.U64} {c : molt_petit.Chain}
    (hn : 0 < n.val)
    (h : molt_petit.valid_chain_k n c = ok true) :
    MoltPetit.Model.ValidChain n.val (toModelChain c) ∧
    MoltPetit.Model.KeyIndexMonotone n.val (toModelChain c) :=
  MoltPetit.Model.validChainK_sound (valid_chain_k_sound hn h)

/-- **Safety: deep blocks agree (transferred from the model).** Two chains the
Rust `valid_chain` accepts, recorded under a Byzantine-bounded honest schedule,
agree on every block that is `n`-deep on both — the Rust analogue of the model
`deep_block_agreement`, the same headline safety the TS path enjoys. -/
theorem rust_deep_block_agreement
    {n : Std.U64} (hn : 1 ≤ n.val)
    {bad : MoltPetit.Model.ByzantineSlots} {record : MoltPetit.Model.SlotRecord}
    (hBudget : MoltPetit.Model.ByzantineBounded n.val bad)
    (hHonest : MoltPetit.Model.HonestSlotsUnique bad record)
    (hId : MoltPetit.Model.IdInjective record)
    {c c' : molt_petit.Chain}
    (hv : molt_petit.valid_chain n c = ok true)
    (hv' : molt_petit.valid_chain n c' = ok true)
    (hRec : MoltPetit.Model.ChainInRecord record (toModelChain c))
    (hRec' : MoltPetit.Model.ChainInRecord record (toModelChain c'))
    (hGenesis : MoltPetit.Model.CommonPrefixUpTo (toModelChain c) (toModelChain c') 0)
    {k m m' : Nat} {B B' D D' : MoltPetit.Model.Block}
    (hB : MoltPetit.Model.blockAt? (toModelChain c) k = some B)
    (hB' : MoltPetit.Model.blockAt? (toModelChain c') k = some B')
    (hD : MoltPetit.Model.blockAt? (toModelChain c) m = some D)
    (hD' : MoltPetit.Model.blockAt? (toModelChain c') m' = some D')
    (hDeep : B.slot + n.val ≤ D.slot) (hDeep' : B.slot + n.val ≤ D'.slot) :
    B = B' :=
  MoltPetit.Model.deep_block_agreement hn hBudget hHonest hId
    (rust_valid_chain_sound hv) (rust_valid_chain_sound hv')
    hRec hRec' hGenesis hB hB' hD hD' hDeep hDeep'

/-- **Certified light-client safety for Rust (equal-tip form).** The Rust
analogue of `ts_recent_tip_ancestor_agreement`: two certified chains the Rust
validator accepts under the tight recency rule, with equal tip heights, agree
exactly on the block `n` below each tip. -/
theorem rust_recent_tip_ancestor_agreement
    {n : Std.U64} (hn : 1 ≤ n.val)
    {C} (I : molt_petit.Crypto C) (crypto crypto' : C)
    {bad : MoltPetit.Model.ByzantineSlots} {signed : MoltPetit.Model.SigningLog}
    {G : MoltPetit.Model.Block} {now : Nat}
    (hBudget : MoltPetit.Model.ByzantineBounded n.val bad)
    (hSig : MoltPetit.Model.SigUnforgeableRecent n.val bad (RustSigned I crypto n) signed now n.val)
    (hHash : MoltPetit.Model.SignedHashInjective (RustSigned I crypto n) G)
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
    (hLong  : n.val < (toModelBlock sr1 :: toModelChain srtl).length)
    (hLong' : n.val < (toModelBlock sr1' :: toModelChain srtl').length)
    {sTip sTip' : MoltPetit.Model.Block}
    (hTipS  : (toModelBlock sr1  :: toModelChain srtl).getLast?  = some sTip)
    (hTipS' : (toModelBlock sr1' :: toModelChain srtl').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + n.val)
    (hRecent' : now ≤ sTip'.slot + n.val)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : MoltPetit.Model.Block}
    (hB  : MoltPetit.Model.blockAt? (toModelBlock sr1 :: toModelChain srtl)
            ((toModelBlock sr1 :: toModelChain srtl).length - 1 - n.val) = some B)
    (hB' : MoltPetit.Model.blockAt? (toModelBlock sr1' :: toModelChain srtl')
            ((toModelBlock sr1' :: toModelChain srtl').length - 1 - n.val) = some B') :
    B = B' := by
  obtain ⟨cl, stripped, hcl, hstrip, hcv, hsg, hsfx⟩ := validate_certified_chain_sound hval
  obtain ⟨cl', stripped', hcl', hstrip', hcv', hsg', hsfx'⟩ := validate_certified_chain_sound hval'
  rw [hstr] at hstrip; injection hstrip with hstrip; subst hstrip
  rw [hstr'] at hstrip'; injection hstrip' with hstrip'; subst hstrip'
  obtain ⟨clm, hclEq, hG⟩ := hUnf cert hcv
  obtain ⟨clm', hclEq', hG'0⟩ := hUnf' cert' hcv'
  rw [hcl] at hclEq; injection hclEq with hclEq; subst hclEq
  rw [hcl'] at hclEq'; injection hclEq' with hclEq'; subst hclEq'
  have hG' := groundedCert_mono hCryptoSig hG'0
  have hSigned := sigs_ok_signed suffix hsg hstr
  have hSigned' := sigs_ok_signed suffix' hsg' hstr'
  rw [toModelChain_cons] at hSigned hSigned'
  replace hSigned' := fun b hb => hCryptoSig b (hSigned' b hb)
  obtain ⟨hLink, hLinks, hDense⟩ := validate_suffix_sound hTipS hsfx
  obtain ⟨hLink', hLinks', hDense'⟩ := validate_suffix_sound hTipS' hsfx'
  have hTipAt  := MoltPetit.Model.blockAt_getLast hTipS
  have hTipAt' := MoltPetit.Model.blockAt_getLast hTipS'
  have hT  := MoltPetit.Model.linksOk_height_at hLinks  hTipAt
  have hT' := MoltPetit.Model.linksOk_height_at hLinks' hTipAt'
  have hBh  := MoltPetit.Model.linksOk_height_at hLinks  hB
  have hBh' := MoltPetit.Model.linksOk_height_at hLinks' hB'
  exact MoltPetit.Model.recent_certified_suffix_agreement hn hBudget hSig hHash hG hG'
    hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned'
    hRecent hRecent' hB hB' (by omega) (by omega) (by omega)

/-- **Certified light-client safety for Rust (membership form).** The Rust
analogue of `ts_recent_tip_ancestor_mem`: two certified chains the Rust
`validate_certified_chain` accepts under the tight recency rule agree on their
`n`-deep ancestor. Built by decomposing the Rust validator, projecting to the
Lean model, and invoking the shared `recent_certified_suffix_agreement`. -/
theorem rust_recent_tip_ancestor_mem
    {n : Std.U64} (hn : 1 ≤ n.val)
    {C} (I : molt_petit.Crypto C) (crypto crypto' : C)
    {bad : MoltPetit.Model.ByzantineSlots} {signed : MoltPetit.Model.SigningLog}
    {G : MoltPetit.Model.Block} {now : Nat}
    (hBudget : MoltPetit.Model.ByzantineBounded n.val bad)
    (hSig : MoltPetit.Model.SigUnforgeableRecent n.val bad (RustSigned I crypto n) signed now n.val)
    (hHash : MoltPetit.Model.SignedHashInjective (RustSigned I crypto n) G)
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
    (hRecent  : now ≤ sTip.slot  + n.val)
    (hRecent' : now ≤ sTip'.slot + n.val)
    (hLong  : n.val < (toModelBlock sr1 :: toModelChain srtl).length)
    (hLe : sTip.height ≤ sTip'.height)
    (hReach : (toModelBlock sr1').height + n.val ≤ sTip.height)
    {B : MoltPetit.Model.Block}
    (hB : MoltPetit.Model.blockAt? (toModelBlock sr1 :: toModelChain srtl)
            ((toModelBlock sr1 :: toModelChain srtl).length - 1 - n.val) = some B) :
    ∃ i', i' + n.val < (toModelBlock sr1' :: toModelChain srtl').length ∧
      MoltPetit.Model.blockAt? (toModelBlock sr1' :: toModelChain srtl') i' = some B := by
  obtain ⟨cl, stripped, hcl, hstrip, hcv, hsg, hsfx⟩ := validate_certified_chain_sound hval
  obtain ⟨cl', stripped', hcl', hstrip', hcv', hsg', hsfx'⟩ := validate_certified_chain_sound hval'
  rw [hstr] at hstrip; injection hstrip with hstrip; subst hstrip
  rw [hstr'] at hstrip'; injection hstrip' with hstrip'; subst hstrip'
  obtain ⟨clm, hclEq, hG⟩ := hUnf cert hcv
  obtain ⟨clm', hclEq', hG'0⟩ := hUnf' cert' hcv'
  rw [hcl] at hclEq; injection hclEq with hclEq; subst hclEq
  rw [hcl'] at hclEq'; injection hclEq' with hclEq'; subst hclEq'
  have hG' := groundedCert_mono hCryptoSig hG'0
  have hSigned := sigs_ok_signed suffix hsg hstr
  have hSigned' := sigs_ok_signed suffix' hsg' hstr'
  rw [toModelChain_cons] at hSigned hSigned'
  replace hSigned' := fun b hb => hCryptoSig b (hSigned' b hb)
  obtain ⟨hLink, hLinks, hDense⟩ := validate_suffix_sound hTipS hsfx
  obtain ⟨hLink', hLinks', hDense'⟩ := validate_suffix_sound hTipS' hsfx'
  have hL1 := hLink.1
  have hL1' := hLink'.1
  have hTipAt  : MoltPetit.Model.blockAt? (toModelBlock sr1 :: toModelChain srtl)
      ((toModelBlock sr1 :: toModelChain srtl).length - 1) = some sTip :=
    MoltPetit.Model.blockAt_getLast hTipS
  have hTipAt' : MoltPetit.Model.blockAt? (toModelBlock sr1' :: toModelChain srtl')
      ((toModelBlock sr1' :: toModelChain srtl').length - 1) = some sTip' :=
    MoltPetit.Model.blockAt_getLast hTipS'
  have hT  := MoltPetit.Model.linksOk_height_at hLinks  hTipAt
  have hT' := MoltPetit.Model.linksOk_height_at hLinks' hTipAt'
  have hBh := MoltPetit.Model.linksOk_height_at hLinks hB
  set i' : Nat := sTip.height - n.val - (toModelBlock sr1').height with hi'
  have hi'lt : i' < (toModelBlock sr1' :: toModelChain srtl').length := by omega
  obtain ⟨X, hX⟩ : ∃ X, MoltPetit.Model.blockAt? (toModelBlock sr1' :: toModelChain srtl') i' = some X := by
    unfold MoltPetit.Model.blockAt?
    exact ⟨(toModelBlock sr1' :: toModelChain srtl')[i']'hi'lt, List.getElem?_eq_getElem hi'lt⟩
  have hXh := MoltPetit.Model.linksOk_height_at hLinks' hX
  have hBX : B = X :=
    MoltPetit.Model.recent_certified_suffix_agreement hn hBudget hSig hHash hG hG'
      hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned'
      hRecent hRecent' hB hX (by omega) (by omega) (by omega)
  exact ⟨i', by omega, hBX ▸ hX⟩

/-- **Production soundness (implementation guarantee).** `produce_block_cert`
only ever ships a certified chain that passes the same validator every node
runs — re-surfaced from `Rust/Properties.lean`. -/
theorem rust_produce_block_cert_sound {C} (I : molt_petit.Crypto C)
    (n me at_slot : U64) (new_id contents_hash : molt_petit.Hash)
    (key_index : U64) (sk : molt_petit.Hash)
    (crypto : C) (cert : molt_petit.Hash) (suffix : molt_petit.SignedChain)
    (cc : molt_petit.CertifiedChain)
    (h : molt_petit.produce_block_cert I n me at_slot new_id contents_hash key_index sk
          crypto cert suffix = ok cc) :
    cc = molt_petit.CertifiedChain.Invalid ∨
      molt_petit.validate_certified_chain I n crypto cc = ok true :=
  molt_petit.produce_block_cert_sound I n me at_slot new_id contents_hash key_index sk
    crypto cert suffix cc h

/-- **Certified light-client safety for Rust (production side).** The Rust
analogue of `ts_recent_produced_tip_ancestor_agreement`: a chain *produced* by
`produce_block_cert` (which ships only validator-accepted chains) agrees, on the
`n`-deep ancestor, with any chain a recency-checking verifier accepts. -/
theorem rust_recent_produced_tip_ancestor_agreement
    {n : Std.U64} (hn : 1 ≤ n.val)
    {C} (I : molt_petit.Crypto C) (crypto crypto' : C)
    {bad : MoltPetit.Model.ByzantineSlots} {signed : MoltPetit.Model.SigningLog}
    {G : MoltPetit.Model.Block} {now : Nat}
    (hBudget : MoltPetit.Model.ByzantineBounded n.val bad)
    (hSig : MoltPetit.Model.SigUnforgeableRecent n.val bad (RustSigned I crypto n) signed now n.val)
    (hHash : MoltPetit.Model.SignedHashInjective (RustSigned I crypto n) G)
    (hCryptoSig : ∀ b, RustSigned I crypto' n b → RustSigned I crypto n b)
    (hUnf : ∀ cert : molt_petit.Hash, I.cert_verify crypto cert = ok true →
      ∃ cl, I.cert_claim crypto cert = ok cl ∧
        MoltPetit.Model.GroundedCert n.val (RustSigned I crypto n) G (toModelClaim cl))
    (hUnf' : ∀ cert : molt_petit.Hash, I.cert_verify crypto' cert = ok true →
      ∃ cl, I.cert_claim crypto' cert = ok cl ∧
        MoltPetit.Model.GroundedCert n.val (RustSigned I crypto' n) G (toModelClaim cl))
    {newId contentsHash sk : molt_petit.Hash} {keyIndex atSlot meId : Std.U64}
    {cert0 : molt_petit.Hash} {suffix0 : molt_petit.SignedChain}
    {hcrt : molt_petit.Hash} {sfx : molt_petit.SignedChain}
    (hp : molt_petit.produce_block_cert I n meId atSlot newId contentsHash keyIndex sk
            crypto cert0 suffix0 = ok (.CC hcrt sfx))
    {cert' : molt_petit.Hash} {suffix' : molt_petit.SignedChain}
    (hval' : molt_petit.validate_certified_chain I n crypto' (.CC cert' suffix') = ok true)
    {sr1 sr1' : molt_petit.Block} {srtl srtl' : molt_petit.Chain}
    (hstr  : molt_petit.strip_sigs sfx     = ok (.Cons sr1 srtl))
    (hstr' : molt_petit.strip_sigs suffix' = ok (.Cons sr1' srtl'))
    (hLong  : n.val < (toModelBlock sr1 :: toModelChain srtl).length)
    (hLong' : n.val < (toModelBlock sr1' :: toModelChain srtl').length)
    {sTip sTip' : MoltPetit.Model.Block}
    (hTipS  : (toModelBlock sr1  :: toModelChain srtl).getLast?  = some sTip)
    (hTipS' : (toModelBlock sr1' :: toModelChain srtl').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + n.val)
    (hRecent' : now ≤ sTip'.slot + n.val)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : MoltPetit.Model.Block}
    (hB  : MoltPetit.Model.blockAt? (toModelBlock sr1 :: toModelChain srtl)
            ((toModelBlock sr1 :: toModelChain srtl).length - 1 - n.val) = some B)
    (hB' : MoltPetit.Model.blockAt? (toModelBlock sr1' :: toModelChain srtl')
            ((toModelBlock sr1' :: toModelChain srtl').length - 1 - n.val) = some B') :
    B = B' := by
  have hval : molt_petit.validate_certified_chain I n crypto (.CC hcrt sfx) = ok true := by
    rcases rust_produce_block_cert_sound I n meId atSlot newId contentsHash keyIndex sk
        crypto cert0 suffix0 (.CC hcrt sfx) hp with hInv | hv
    · exact absurd hInv (by simp)
    · exact hv
  exact rust_recent_tip_ancestor_agreement hn I crypto crypto' hBudget hSig hHash hCryptoSig
    hUnf hUnf' hval hval'
    hstr hstr' hLong hLong' hTipS hTipS' hRecent hRecent' hTipHeight hB hB'

end Rust
