import Rust.Bridge
import MoltPetit.TS.BridgeK

/-!
# Rust bridge for the certificate-boundary floor check

`rust/src/lib.rs` now ships the certificate-boundary key-index machinery
(`FloorList`, `floor_lookup`, `floor_bump`, `floors_shape_ok`,
`key_mono_from`, `validate_suffix_k`) — the Rust analogue of the
`moltPetit.ts` wire snapshot and suffix check. This module pins the
Aeneas-extracted functions to the model, mirroring `MoltPetit/TS/BridgeK`:

* `toTSFloors` projects the extracted snapshot to the TS wire `FloorList`
  (`U64 → Int` by `.val`); `floor_lookup_corr` / `floor_bump_corr` show the
  extracted accessors compute the (pure, already-verified) TS wire functions
  on the projection whenever they succeed (`floor_lookup_total` witnesses
  that the lookup always does), and `floors_shape_from_corr` /
  `key_mono_from_corr` show the extracted Boolean checks are
  acceptance-sound for their TS counterparts (ok-true implies TS-true; no
  completeness converse is proven, and none is needed downstream) —
  one-directional implementation parity, by theorem.
* `validate_suffix_k_sound` — a suffix accepted by the Rust
  `validate_suffix_k` against a claim and a floor snapshot yields exactly the
  suffix hypotheses of the certificate-level theorem
  `keyrot_recent_certified_suffix_agreement`: the link/structure/density
  facts (via `validate_suffix_sound`) **and** the model `keyMonoFrom` at any
  floor function `g` the snapshot denotes (`floor_lookup` agreement below
  `n`) — in particular the certificate-attested floor, by the same wire
  contract as on the TS side (see `ts_validateSuffixK_sound`).

Soundness direction only, as everywhere in this bridge: success of the Rust
computation witnesses that no machine-integer overflow occurred.
-/

open Aeneas Std Result

namespace Rust

/-- Project the extracted Rust floor snapshot to the TS wire `FloorList`
(`U64 → Int` by `.val`). The two reference implementations share the wire
meaning of the snapshot, so the TS bridge lemmas (`MoltPetit/TS/BridgeK`)
apply to the projection. -/
def toTSFloors : molt_petit.FloorList → MoltPetit.FloorList
  | .FNil => .fnil
  | .FCons p f tl => .fcons (p.val : Int) (f.val : Int) (toTSFloors tl)

/-- `clone_floors` always succeeds and is the identity. -/
theorem clone_floors_eq : ∀ fl : molt_petit.FloorList,
    molt_petit.clone_floors fl = ok fl
  | .FNil => by rw [molt_petit.clone_floors]
  | .FCons p f tl => by
    rw [molt_petit.clone_floors, clone_floors_eq tl]
    rfl

/-- `floor_lookup` always succeeds — so the `hden` hypothesis of
`validate_suffix_k_sound` is realizable for every snapshot (non-vacuity):
every `fl` denotes at least the floor function given by its own lookups,
making the Rust-side denotation hypothesis visibly equivalent to the TS
bridge's total-function equation. -/
theorem floor_lookup_total : ∀ (fl : molt_petit.FloorList) (i : U64),
    ∃ f, molt_petit.floor_lookup fl i = ok f
  | .FNil, _ => ⟨0#u64, by rw [molt_petit.floor_lookup]⟩
  | .FCons p f tl, i => by
    rw [molt_petit.floor_lookup]
    by_cases hp : p = i
    · exact ⟨f, by rw [if_pos hp]⟩
    · rw [if_neg hp]
      exact floor_lookup_total tl i

/-- `floor_lookup` computes the TS `floorLookup` on the projection. -/
theorem floor_lookup_corr : ∀ (fl : molt_petit.FloorList) (i : U64) {f : U64},
    molt_petit.floor_lookup fl i = ok f →
    (f.val : Int) = MoltPetit.floorLookup (toTSFloors fl) (i.val : Int)
  | .FNil, i, f, h => by
    rw [molt_petit.floor_lookup] at h
    injection h with h
    simp [← h, toTSFloors, MoltPetit.floorLookup]
  | .FCons p fv tl, i, f, h => by
    rw [molt_petit.floor_lookup] at h
    by_cases hp : p = i
    · rw [if_pos hp] at h
      injection h with h
      subst hp
      simp [← h, toTSFloors, MoltPetit.floorLookup]
    · rw [if_neg hp] at h
      have hrec := floor_lookup_corr tl i h
      have hpi : ¬ (p.val : Int) = (i.val : Int) := by
        intro hc
        exact hp (UScalar.eq_of_val_eq (by exact_mod_cast hc))
      simp [toTSFloors, MoltPetit.floorLookup, hrec, hpi]

/-- `floor_bump` computes the TS `floorBump` on the projection. -/
theorem floor_bump_corr : ∀ (fl : molt_petit.FloorList) (i v : U64)
    {fl' : molt_petit.FloorList},
    molt_petit.floor_bump fl i v = ok fl' →
    toTSFloors fl' = MoltPetit.floorBump (toTSFloors fl) (i.val : Int) (v.val : Int)
  | .FNil, i, v, fl', h => by
    rw [molt_petit.floor_bump] at h
    injection h with h
    simp [← h, toTSFloors, MoltPetit.floorBump]
  | .FCons p fv tl, i, v, fl', h => by
    rw [molt_petit.floor_bump] at h
    obtain ⟨nf, hnf, h⟩ := molt_petit.bind_inv h
    obtain ⟨rest, hrest, h⟩ := molt_petit.bind_inv h
    injection h with h
    subst h
    by_cases hp : p = i
    · rw [if_pos hp] at hnf hrest
      rw [clone_floors_eq tl] at hrest
      injection hrest with hrest
      subst hrest
      subst hp
      by_cases hfv : fv < v
      · rw [if_pos hfv] at hnf
        injection hnf with hnf
        subst hnf
        have hlt : (fv.val : Int) < (v.val : Int) := by
          have : fv.val < v.val := by scalar_tac
          exact_mod_cast this
        simp [toTSFloors, MoltPetit.floorBump, hlt]
      · rw [if_neg hfv] at hnf
        injection hnf with hnf
        subst hnf
        have hge : ¬ (fv.val : Int) < (v.val : Int) := by
          have : ¬ fv.val < v.val := by scalar_tac
          exact_mod_cast this
        simp [toTSFloors, MoltPetit.floorBump, hge]
    · rw [if_neg hp] at hnf hrest
      injection hnf with hnf
      subst hnf
      have hrec := floor_bump_corr tl i v hrest
      have hpi : ¬ (p.val : Int) = (i.val : Int) := by
        intro hc
        exact hp (UScalar.eq_of_val_eq (by exact_mod_cast hc))
      simp [toTSFloors, MoltPetit.floorBump, hrec, hpi]

/-- `floors_shape_from` soundness: Rust acceptance gives the TS canonical
shape on the projection. (The Rust source adds an `i < n` overflow gate the
TS check does not have; it only shrinks the accepted set, so the soundness
direction is unaffected.) -/
theorem floors_shape_from_corr : ∀ (fl : molt_petit.FloorList) (i n : U64),
    molt_petit.floors_shape_from i n fl = ok true →
    MoltPetit.floorsShapeFrom (i.val : Int) (n.val : Int) (toTSFloors fl) = true
  | .FNil, i, n, h => by
    rw [molt_petit.floors_shape_from] at h
    injection h with h
    have hin : i = n := by simpa using h
    subst hin
    simp [toTSFloors, MoltPetit.floorsShapeFrom]
  | .FCons p fv tl, i, n, h => by
    rw [molt_petit.floors_shape_from] at h
    split at h
    · rename_i hp
      split at h
      · obtain ⟨i1, hi1, h⟩ := molt_petit.bind_inv h
        have hi1v : i1.val = i.val + 1 := by
          have := UScalar.add_equiv i 1#u64
          simp only [hi1] at this
          simpa using this.2.1
        have hrec := floors_shape_from_corr tl i1 n h
        rw [hi1v] at hrec
        subst hp
        push_cast at hrec
        simp only [toTSFloors]
        rw [MoltPetit.floorsShapeFrom]
        simp [hrec]
      · simp at h
    · simp at h

/-- `key_mono_from` soundness: Rust acceptance gives the TS `keyMonoFromTs`
on the projections. -/
theorem key_mono_from_corr {n : U64} (hn : 0 < n.val) :
    ∀ (c : molt_petit.Chain) (fl : molt_petit.FloorList),
      molt_petit.key_mono_from n fl c = ok true →
      MoltPetit.keyMonoFromTs (n.val : Int) (toTSFloors fl)
        (MoltPetit.Model.toTSChain (toModelChain c)) = true
  | .Nil, fl, h => by
    simp [toModelChain, MoltPetit.Model.toTSChain, MoltPetit.keyMonoFromTs]
  | .Cons b tl, fl, h => by
    rw [molt_petit.key_mono_from] at h
    obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
    obtain ⟨i1, hi1, h⟩ := molt_petit.bind_inv h
    obtain ⟨bumped, hbump, h⟩ := molt_petit.bind_inv h
    have hgate : i1 ≤ b.key_index ∧ molt_petit.key_mono_from n bumped tl = ok true := by
      split at h
      · exact ⟨‹_›, h⟩
      · simp at h
    obtain ⟨hle, htl⟩ := hgate
    have hiv : i.val = MoltPetit.Model.producerForSlot n.val b.slot.val := by
      have hc := producer_for_slot_corr n b.slot hn
      rw [hi] at hc
      simpa using hc
    rw [toModelChain_cons]
    rw [show MoltPetit.Model.toTSChain (toModelBlock b :: toModelChain tl) =
      .cons (toModelBlock b).slot (toModelBlock b).height
        ((toModelBlock b).prev.map Int.ofNat) (toModelBlock b).id
        (toModelBlock b).contentsHash (toModelBlock b).keyIndex
        (MoltPetit.Model.toTSChain (toModelChain tl)) from rfl]
    rw [MoltPetit.keyMonoFromTs]
    have hslot : ((toModelBlock b).slot : Int) = (b.slot.val : Int) := rfl
    have hki : ((toModelBlock b).keyIndex : Int) = (b.key_index.val : Int) := rfl
    rw [hslot, hki, MoltPetit.Model.ts_producerForSlot, ← hiv]
    rw [Bool.and_eq_true]
    constructor
    · rw [decide_eq_true_eq, ← floor_lookup_corr fl i hi1]
      have : i1.val ≤ b.key_index.val := by scalar_tac
      exact_mod_cast this
    · rw [← floor_bump_corr fl i b.key_index hbump]
      exact key_mono_from_corr hn tl bumped htl

/-- **Suffix-K validator soundness** (Rust analogue of
`ts_validateSuffixK_sound`): a nonempty suffix accepted by the Rust
`validate_suffix_k` against a claim and a floor snapshot yields exactly the
suffix hypotheses of the certificate-level key-stealing theorem — the
link/structure/density facts, and the model `keyMonoFrom` at any floor
function `g` the snapshot denotes (in particular the certificate-attested
floor, by the wire contract). -/
theorem validate_suffix_k_sound {n : U64} (hn : 1 ≤ n.val)
    {cl : molt_petit.CertClaim} {fl : molt_petit.FloorList} {g : Nat → Nat}
    {s1 : molt_petit.Block} {tl : molt_petit.Chain} {sTip : MoltPetit.Model.Block}
    (hTipS : (toModelBlock s1 :: toModelChain tl).getLast? = some sTip)
    (hden : ∀ j : U64, j.val < n.val →
      ∃ f, molt_petit.floor_lookup fl j = ok f ∧ f.val = g j.val)
    (h : molt_petit.validate_suffix_k n cl fl (.Cons s1 tl) = ok true) :
    (((toModelBlock s1).height = (toModelClaim cl).tipHeight + 1 ∧
      (toModelClaim cl).tipSlot < (toModelBlock s1).slot ∧
      (toModelBlock s1).prev = some (toModelClaim cl).tipId) ∧
     MoltPetit.Model.linksOk (toModelBlock s1 :: toModelChain tl) = true ∧
     (∀ u : Nat, ((toModelClaim cl).tipSlot : Int) + 2 - n.val ≤ (u : Int) →
        u + n.val ≤ sTip.slot + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
          ((toModelClaim cl).tail ++ toModelBlock s1 :: toModelChain tl) u n.val)) ∧
    MoltPetit.Model.keyMonoFrom n.val g (toModelBlock s1 :: toModelChain tl) = true := by
  rw [molt_petit.validate_suffix_k] at h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbt
    rw [hbt] at hb
    obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i hb1t
      rw [hb1t] at hb1
      rw [molt_petit.floors_shape_ok] at hb1
      -- TS-level canonical shape, hence full producer coverage of the snapshot
      have hshapeTS : MoltPetit.floorsShapeFrom 0 (n.val : Int) (toTSFloors fl) = true := by
        have := floors_shape_from_corr fl 0#u64 n hb1
        simpa using this
      have hhas : ∀ j : Nat, j < n.val → MoltPetit.Model.FloorHas (toTSFloors fl) j :=
        fun j hj => MoltPetit.Model.floorHas_of_shapeFrom (toTSFloors fl) 0 hshapeTS j
          (Int.natCast_nonneg j) (by exact_mod_cast hj)
      -- transfer the Rust-level floor denotation to the TS wire snapshot
      have hdenTS : ∀ j : Nat, j < n.val →
          MoltPetit.floorLookup (toTSFloors fl) (j : Int) = ((g j : Nat) : Int) := by
        intro j hj
        have hj64 : j < 2 ^ 64 := by scalar_tac
        have hJv : (UScalar.ofNatCore j hj64 : U64).val = j := rfl
        obtain ⟨f, hf, hfv⟩ := hden (UScalar.ofNatCore j hj64) (by rw [hJv]; exact hj)
        have hcorr := floor_lookup_corr fl (UScalar.ofNatCore j hj64) hf
        rw [hJv] at hcorr hfv
        rw [← hcorr, hfv]
      have hts := key_mono_from_corr (by omega) (.Cons s1 tl) fl h
      rw [toModelChain_cons] at hts
      exact ⟨validate_suffix_sound hTipS hb,
        (MoltPetit.Model.ts_keyMonoFromTs hn (toModelBlock s1 :: toModelChain tl)
          (toTSFloors fl) g hhas hdenTS).mp hts⟩
    · simp at h
  · simp at h

end Rust
