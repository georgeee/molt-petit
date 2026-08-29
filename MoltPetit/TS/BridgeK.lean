import MoltPetit.TS.Bridge
import MoltPetit.Model.KeyStealingCert

/-!
# MoltPetit — TS bridge for the certificate-boundary floor check

`moltPetit.ts` now ships the certificate-boundary key-index machinery: a wire
`FloorList` (the per-producer floor snapshot the certificate attests alongside
its claim), the canonical-shape check `floorsShapeOk` (producers `0..n-1`
exactly once, in order, nonnegative floors — so the fail-open defaults of
`floorLookup` are never consulted), and the suffix monotone check
`keyMonoFromTs` folding the snapshot through the suffix. This module pins them
to the model:

* `ts_keyMonoFromTs` — the TS suffix check agrees with the model `keyMonoFrom`
  under any floor function the wire snapshot denotes (`floorLookup` agreement
  below `n`).
* `ts_validateSuffixK_sound` — a suffix accepted by `validateSuffixK` against
  a claim and a wire floor snapshot yields exactly the suffix hypotheses of
  the certificate-level theorem `keyrot_recent_certified_suffix_agreement`:
  the structural/link/density facts (via `ts_validateSuffix_sound`) **and**
  the model `keyMonoFrom` at the attested floor.

The remaining glue for a fully TS-level corollary is the certificate
attestation shape: unforgeability must attest the **pair** — `∃ cl fl,
claim hc = toTSClaim cl ∧ (∀ i < n, floorLookup (floors hc) i = fl i) ∧
GroundedCertK n Signed G cl fl` — see the wire-contract note on
`keyrot_recent_certified_suffix_agreement`.
-/

namespace MoltPetit.Model

/-- Membership of a producer in a wire floor list (bridge-side, proof-only). -/
def FloorHas : MoltPetit.FloorList → Int → Prop
  | .fnil, _ => False
  | .fcons producer _ tail, p => producer = p ∨ FloorHas tail p

/-- The canonical shape contains every producer of `[i0, n)`. -/
theorem floorHas_of_shapeFrom {n : Int} :
    ∀ (fl : MoltPetit.FloorList) (i0 : Int),
      MoltPetit.floorsShapeFrom i0 n fl = true →
      ∀ p : Int, i0 ≤ p → p < n → FloorHas fl p
  | .fnil, i0, h, p, hlo, hhi => by
    rw [MoltPetit.floorsShapeFrom, beq_iff_eq] at h
    omega
  | .fcons producer floor tail, i0, h, p, hlo, hhi => by
    rw [MoltPetit.floorsShapeFrom, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hprod, -⟩, htail⟩ := h
    rcases eq_or_lt_of_le hlo with rfl | hgt
    · exact Or.inl hprod
    · exact Or.inr (floorHas_of_shapeFrom tail (i0 + 1) htail p (by omega) hhi)

/-- Bumping preserves producer membership. -/
theorem floorHas_floorBump {p v q : Int} :
    ∀ fl : MoltPetit.FloorList, FloorHas fl q → FloorHas (MoltPetit.floorBump fl p v) q
  | .fnil, h => h.elim
  | .fcons producer floor tail, h => by
    rw [MoltPetit.floorBump]
    by_cases hp : (producer == p) = true
    · rw [if_pos hp, if_pos hp]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rw [if_neg hp, if_neg hp]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (floorHas_floorBump tail h)

/-- Lookup after bump, for producers the list contains: the bumped producer
reads the max, others are untouched. (First-occurrence discipline: `floorBump`
raises the first `p`-node and `floorLookup` reads the first match, so the two
stay consistent without any uniqueness requirement.) -/
theorem floorLookup_floorBump {p v : Int} :
    ∀ fl : MoltPetit.FloorList, FloorHas fl p → ∀ j : Int,
      MoltPetit.floorLookup (MoltPetit.floorBump fl p v) j =
        if p = j then
          (if MoltPetit.floorLookup fl p < v then v else MoltPetit.floorLookup fl p)
        else MoltPetit.floorLookup fl j
  | .fnil, h => h.elim
  | .fcons producer floor tail, h => by
    intro j
    by_cases hpp : producer = p
    · subst hpp
      by_cases hpj : producer = j
      · subst hpj
        simp [MoltPetit.floorBump, MoltPetit.floorLookup]
      · simp [MoltPetit.floorBump, MoltPetit.floorLookup, hpj, Ne.symm hpj]
    · have htail : FloorHas tail p := by
        rcases h with h | h
        · exact absurd h hpp
        · exact h
      have hbump := floorLookup_floorBump (p := p) (v := v) tail htail j
      by_cases hpj : producer = j
      · subst hpj
        simp [MoltPetit.floorBump, MoltPetit.floorLookup, hpp, Ne.symm hpp]
      · simp [MoltPetit.floorBump, MoltPetit.floorLookup, hpp, hpj, hbump]

/-- **The TS suffix monotone check agrees with the model `keyMonoFrom`** under
any floor function the wire snapshot denotes below `n`. -/
theorem ts_keyMonoFromTs {n : Nat} (hn : 1 ≤ n) :
    ∀ (c : Chain) (fl : MoltPetit.FloorList) (g : Nat → Nat),
      (∀ j : Nat, j < n → FloorHas fl j) →
      (∀ j : Nat, j < n → MoltPetit.floorLookup fl j = (g j : Int)) →
      (MoltPetit.keyMonoFromTs n fl (toTSChain c) = true ↔ keyMonoFrom n g c = true)
  | [], fl, g, _, _ => by
    simp [toTSChain, MoltPetit.keyMonoFromTs, keyMonoFrom]
  | b :: rest, fl, g, hhas, hden => by
    have hp : producerForSlot n b.slot < n := by
      unfold producerForSlot
      exact Nat.mod_lt _ hn
    set p : Nat := producerForSlot n b.slot with hpdef
    rw [show toTSChain (b :: rest) =
      .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex
        (toTSChain rest) from rfl]
    rw [MoltPetit.keyMonoFromTs, keyMonoFrom, Bool.and_eq_true, Bool.and_eq_true,
      ts_producerForSlot, ← hpdef]
    have hgate : (decide ((MoltPetit.floorLookup fl p) ≤ (b.keyIndex : Int))) = true ↔
        g p ≤ b.keyIndex := by
      rw [decide_eq_true_eq, hden p hp]
      exact_mod_cast Iff.rfl
    have hrest := ts_keyMonoFromTs hn rest
      (MoltPetit.floorBump fl p b.keyIndex)
      (fun i => if p = i then max (g i) b.keyIndex else g i)
      (fun j hj => floorHas_floorBump _ (hhas j hj))
      (fun j hj => by
        rw [floorLookup_floorBump _ (hhas p hp) j]
        by_cases hpj : p = j
        · rw [if_pos (by exact_mod_cast hpj)]
          show _ = ((if p = j then max (g j) b.keyIndex else g j : Nat) : Int)
          rw [if_pos hpj, hden p hp, hpj]
          rcases Nat.lt_or_ge (g j) b.keyIndex with hlt | hge
          · rw [if_pos (by exact_mod_cast hlt), Nat.max_eq_right (le_of_lt hlt)]
          · rw [if_neg (by exact_mod_cast Nat.not_lt.mpr hge), Nat.max_eq_left hge]
        · rw [if_neg (by exact_mod_cast hpj)]
          show _ = ((if p = j then max (g j) b.keyIndex else g j : Nat) : Int)
          rw [if_neg hpj]
          exact hden j hj)
    constructor
    · rintro ⟨hok, hmono⟩
      exact ⟨by rw [decide_eq_true_eq]; exact hgate.mp hok, hrest.mp hmono⟩
    · rintro ⟨hok, hmono⟩
      rw [decide_eq_true_eq] at hok
      exact ⟨hgate.mpr hok, hrest.mpr hmono⟩

/-- **TS suffix-K validation soundness.** A nonempty suffix accepted by the
TypeScript `validateSuffixK` against a claim and a wire floor snapshot yields
exactly the suffix hypotheses of the certificate-level key-stealing theorem:
the link/structure/density facts, and the model `keyMonoFrom` at any floor
function `g` the wire snapshot denotes (in particular the certificate-attested
floor, by the wire contract). -/
theorem ts_validateSuffixK_sound {n : Nat} (hn : 1 ≤ n) {cl : CertClaim}
    {fl : MoltPetit.FloorList} {g : Nat → Nat}
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTip : (s₁ :: srest).getLast? = some sTip)
    (hden : ∀ j : Nat, j < n → MoltPetit.floorLookup fl j = (g j : Int))
    (h : MoltPetit.validateSuffixK n (toTSClaim cl) fl (toTSChain (s₁ :: srest)) = true) :
    ((s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId) ∧
     linksOk (s₁ :: srest) = true ∧
     (∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
       quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)) ∧
    keyMonoFrom n g (s₁ :: srest) = true := by
  rw [MoltPetit.validateSuffixK, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsfx, hshape⟩, hmono⟩ := h
  have hhas : ∀ j : Nat, j < n → FloorHas fl j := fun j hj =>
    floorHas_of_shapeFrom fl 0 hshape j (by omega) (by exact_mod_cast hj)
  exact ⟨ts_validateSuffix_sound hTip hsfx,
    (ts_keyMonoFromTs hn (s₁ :: srest) fl g hhas hden).mp hmono⟩

end MoltPetit.Model
