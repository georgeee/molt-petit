import MoltPetit.Model.Timed

/-!
# Deriving recency-scoped unforgeability from the timed model

`SigUnforgeableRecent` (the recency-scoped honest-slot uniqueness consumed by the
light-client safety theorem) is stated over an abstract *stamped* signing log
`SigningLog := producer → slot → Option Block`. This module shows it is **not a
primitive**: it is a theorem about the real-time signing model
(`TimedExecution`), once the stamped log is read off the timed log and one extra
ingredient — **no back-dating onto an honest stamp** — is supplied.

## What the timed model alone does *not* give

`TimedExecution` carries plain per-real-slot uniqueness (`honest_once`: one block
per honest real slot) but it deliberately lets a *bad* real slot `r` sign a block
with any stamp in that producer's residue class (`key_match`: `B.slot % n = r % n`).
So a block stamped at an **honest** slot `s` can be first-signed at a *different*,
*bad* real slot `r ≡ s (mod n)` — the honest slot `s` is never even exercised.
`honest_stamp` does not forbid this (it constrains only honest real slots), and
neither recency nor the forged-time bound rules it out for a *single* block (the
forged-time bound caps the *aggregate* count of coerced blocks per window — it
secures `n`-deep agreement, not per-slot uniqueness). `noBackdate_independent`
below exhibits exactly such an execution. Hence the per-block pinning that
`SigUnforgeableRecent` asserts does **not** follow from recency alone — contrary
to a tempting reading.

## The residue that does suffice

`NoBackdate` is the missing content: a block whose stamp is honest was signed at
the real slot equal to its stamp. Operationally this is honest key custody
re-anchored to the *stamp* — an honest producer's slot-`s` signature can only be
its genuine slot-`s` call, never a coerced bad-slot mint. It is guaranteed by
*forward-secure / key-evolving* signatures (the per-period key cannot sign for a
different period — exactly the upgrade the limitations section recommends), or by
a signing oracle that stamps its own real slot. With it,
`sigUnforgeableRecent_of_timed` derives `SigUnforgeableRecent` for the projected
log, with no recency or chain hypotheses left over — the scoping in
`SigUnforgeableRecent` is then slack, which matches the operational reading that
forward-secure custody removes the long-range residual entirely.
-/

namespace MoltPetit.Model

open Classical in
/--
The **stamped** signing log read off a real-time `log`: participant `p`'s entry
for stamped slot `s` is the block stamped `s` that was signed *at real slot `s`*
(its own slot), if any. At an honest real slot this is single-valued
(`TimedExecution.honest_once`), so the choice is canonical there — which is the
only regime `SigUnforgeableRecent` quantifies over.
-/
noncomputable def projectSigned (n : Nat) (log : TimedLog) : SigningLog :=
  fun p s =>
    if h : p = producerForSlot n s ∧ ∃ B, B ∈ log s ∧ B.slot = s
    then some h.2.choose else none

/--
**No back-dating onto an honest stamp.** A block whose stamp is honest was signed
at the real slot equal to its stamp. This is the forward-secure / stamp-bound
custody residue: it is exactly what the structural timed-model fields do *not*
supply (see `noBackdate_independent`), and exactly what turns the recency-scoped
unforgeability assumption into a theorem.
-/
def NoBackdate (bad : ByzantineSlots) (log : TimedLog) : Prop :=
  ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → ¬ bad B.slot → B.slot = r

/--
**Recency-scoped unforgeability is a theorem of the timed model + no-back-dating.**
Given a timed execution, an EUF-CMA bridge (`Signed B → B` was signed at some real
slot), and `NoBackdate`, the recency-scoped uniqueness assumption
`SigUnforgeableRecent` holds for the projected stamped log — at *any* recency
window `Δ` (the recency hypothesis is not even used; no-back-dating already pins
each honest-stamp block). This is the formal replacement for the conjecture that
the assumption "follows from the recency bound itself": the per-block pinning
comes from no-back-dating, while recency separately buys the *forged-time* bound
(`forged_suffix_time_bound`).
-/
theorem sigUnforgeableRecent_of_timed {n : Nat} {bad : ByzantineSlots}
    {log : TimedLog} {G : Block} {Signed : Block → Prop} {now Δ : Nat}
    (hexec : TimedExecution n bad log G)
    (hNB : NoBackdate bad log)
    (hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r, B ∈ log r) :
    SigUnforgeableRecent n bad Signed (projectSigned n log) now Δ := by
  constructor
  intro B c _hVC _hBc _hrec hbadB hSB
  -- the verifying signature was produced at some real slot, and no-back-dating
  -- pins that slot to the (honest) stamp
  obtain ⟨r, hBr⟩ := hbridge hSB
  have hrEq : B.slot = r := hNB hBr hbadB
  have hBlog : B ∈ log B.slot := hrEq ▸ hBr
  -- the projection's guard fires, with B itself as a witness
  have hcond : producerForSlot n B.slot = producerForSlot n B.slot ∧
      ∃ B', B' ∈ log B.slot ∧ B'.slot = B.slot := ⟨rfl, B, hBlog, rfl⟩
  change projectSigned n log (producerForSlot n B.slot) B.slot = some B
  unfold projectSigned
  rw [dif_pos hcond]
  -- the chosen block sits in the same honest real slot as B, so honest_once
  -- forces it to be B
  have hspec := hcond.2.choose_spec
  have hchoose : hcond.2.choose = B := hexec.honest_once hbadB hspec.1 hBlog
  rw [hchoose]

/--
**`NoBackdate` is independent of the structural timed model.** There is a timed
execution (all five `TimedExecution` fields hold) in which a block stamped at an
*honest* slot was nevertheless first-signed at a *bad* real slot — so `NoBackdate`
fails. Concretely (`n = 2`): genesis `G` at slot 0, and `A` stamped at the honest
slot 1 but signed only at the bad real slot 3 (`1 ≡ 3 mod 2`, so `key_match`
holds; the honest slot 1 is never exercised, so `honest_stamp`/`honest_once` are
vacuous; `A`'s parent is `G`, available as genesis). So the per-block pinning that
`sigUnforgeableRecent_of_timed` delivers genuinely requires `NoBackdate`: it does
not follow from `key_match`/`honest_stamp`/`honest_once`/`chain_order`/`id_inj`,
nor from recency. (The forged block could moreover sit at an arbitrarily recent
tip — an operational remark, not part of this statement, which asserts only the
`TimedExecution` ∧ ¬`NoBackdate` witness.) This is the back-dating attack the
forward-secure custody residue rules out.
-/
theorem noBackdate_independent :
    ∃ (bad : ByzantineSlots) (log : TimedLog) (G : Block),
      TimedExecution 2 bad log G ∧ ¬ NoBackdate bad log := by
  classical
  refine ⟨fun r => r = 3,
          fun r => if r = 3 then {(⟨1, 1, some 100, 101, 0, 0⟩ : Block)} else ∅,
          ⟨0, 0, none, 100, 0, 0⟩, ?_, ?_⟩
  · -- every field of TimedExecution holds; the only nonempty log is the bad slot 3
    have hlog : ∀ (r : Nat) (B : Block),
        B ∈ (if r = 3 then {(⟨1, 1, some 100, 101, 0, 0⟩ : Block)} else (∅ : Finset Block))
          ↔ (r = 3 ∧ B = ⟨1, 1, some 100, 101, 0, 0⟩) := by
      intro r B
      by_cases hr : r = 3 <;> simp [hr]
    refine { key_match := ?_, honest_stamp := ?_, honest_once := ?_,
             chain_order := ?_, id_inj := ?_ }
    · intro r B hB
      obtain ⟨rfl, rfl⟩ := (hlog r B).mp hB; rfl
    · intro r hr B hB
      obtain ⟨rfl, rfl⟩ := (hlog r B).mp hB; exact absurd rfl hr
    · intro r hr B B' hB hB'
      obtain ⟨rfl, rfl⟩ := (hlog r B).mp hB; exact absurd rfl hr
    · intro r B hB i hi
      obtain ⟨rfl, rfl⟩ := (hlog r B).mp hB
      refine ⟨⟨0, 0, none, 100, 0, 0⟩, ?_, Or.inl rfl⟩
      simpa using hi
    · intro B B' hB hB' hid
      have key : ∀ X : Block,
          SignedEver (fun r => if r = 3 then {(⟨1,1,some 100,101,0,0⟩ : Block)} else ∅)
            ⟨0,0,none,100,0,0⟩ X → X = ⟨0,0,none,100,0,0⟩ ∨ X = ⟨1,1,some 100,101,0,0⟩ := by
        intro X hX
        rcases hX with rfl | ⟨r, hr⟩
        · exact Or.inl rfl
        · exact Or.inr ((hlog r X).mp hr).2
      rcases key B hB with rfl | rfl <;> rcases key B' hB' with rfl | rfl <;>
        first | rfl | (simp at hid)
  · -- NoBackdate fails on A: it is stamped at the honest slot 1 but lives in log 3
    intro hNB
    have hmem : (⟨1, 1, some 100, 101, 0, 0⟩ : Block) ∈
        (fun r => if r = 3 then ({(⟨1, 1, some 100, 101, 0, 0⟩ : Block)} : Finset Block)
          else ∅) 3 := by simp
    have hbad : ¬ ((⟨1, 1, some 100, 101, 0, 0⟩ : Block).slot = 3) := by decide
    exact absurd (hNB (r := 3) hmem hbad) hbad

end MoltPetit.Model
