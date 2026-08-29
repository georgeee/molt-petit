import MoltPetit.Model.KeyStealingCert

/-!
# MoltPetit — old-key forks are long-range (increment I4, the provable core)

`H-ANCHOR` — the light client trusts only recent-tipped chains anchored after
the rotations it relies on — is a *named assumption* (weak subjectivity) and
stays one: nothing can refute a fork built entirely in the past. What **is**
provable, and what this module proves, is the design note's §4B claim that was
previously only asserted: **a fork that carries a rotated-out-key block past
the rotation's confirmation cannot contain the announcement — it must branch
strictly before it.** So old-key forks are not merely conjectured to be
long-range; the validator's `≤`-pin *forces* them to be. What remains for
`H-ANCHOR` is exactly (and only) ruling out forks that branch before the
anchor — the irreducible weak-subjectivity residue.

* `oldkey_dead_after_confirmed_announcement` — on any single accepted chain, a
  block of producer `i` at least `Δconf` past an `i`-announcement declares at
  least the announced version (the announcement is in its confirmed prefix, so
  the in-force floor has risen and the `≤`-pin lifts it).
* `recent_oldkey_fork_is_longrange` — cross-chain: an accepted fork sharing
  the canonical prefix up to (at least) the announcement's height obeys the
  announced version at all `Δconf`-later same-producer blocks. Contrapositive:
  a fork carrying an *older* version there shares **no** prefix reaching the
  announcement — it branched strictly below it. Long-range, as claimed.
-/

namespace MoltPetit.Model

/-- **Single-chain form.** On a `validChainK'`-accepted chain, once an
announcement by producer `i` is `Δconf` deep (relative to a later `i`-block's
slot), that later block declares at least the announced version: the
announcement sits in the later block's confirmed prefix, so the in-force floor
is at least the announced index, and the `≤`-pin lifts it to the declaration. -/
theorem oldkey_dead_after_confirmed_announcement {n Δconf : Nat} {c : Chain}
    (hK' : validChainK' n Δconf c = true)
    {A b : Block} (hA : A ∈ c) (hb : b ∈ c)
    (hprod : producerForSlot n A.slot = producerForSlot n b.slot)
    (hconf : A.slot + Δconf ≤ b.slot) :
    A.keyIndex ≤ b.keyIndex := by
  have hpin := validChainK'_pinned hK' b hb
  -- the announcement is in b's confirmed prefix …
  have hAconf : A ∈ confirmedPrefix Δconf c b.slot := by
    unfold confirmedPrefix
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨hA, hconf⟩
  -- … so the in-force floor at b.slot is at least the announced version
  have hfloor : A.keyIndex ≤ inForce n Δconf c (producerForSlot n b.slot) b.slot := by
    unfold inForce
    rw [← hprod]
    exact mem_keyIndex_le_floor n hAconf
  exact le_trans hfloor hpin

/-- **Cross-chain form (I4's provable core).** An accepted fork `c'` that
shares the canonical chain's prefix up to at least the announcement's height
obeys the announced version at every same-producer block `Δconf` past the
announcement. **Contrapositive — the long-range statement**: an accepted fork
that carries a block of the announcement's producer, `Δconf` past the
announcement's slot, declaring a version *below* the announced one, shares
**no** common prefix reaching the announcement — it branched strictly before
it. Rotated-out stolen keys can only power forks rooted below the rotation;
excluding those is precisely the `H-ANCHOR` recency-anchor assumption, which
this lemma reduces to its irreducible weak-subjectivity content. -/
theorem recent_oldkey_fork_is_longrange {n Δconf : Nat} {c c' : Chain}
    (hK' : validChainK' n Δconf c' = true)
    {hA : Nat} {A : Block} (hAat : blockAt? c hA = some A)
    {k : Nat} (hshared : CommonPrefixUpTo c c' k) (hAk : hA ≤ k)
    {b : Block} (hb : b ∈ c')
    (hprod : producerForSlot n A.slot = producerForSlot n b.slot)
    (hconf : A.slot + Δconf ≤ b.slot) :
    A.keyIndex ≤ b.keyIndex := by
  obtain ⟨X, hXc, hXc'⟩ := hshared hA hAk
  rw [hAat] at hXc
  have hXA : A = X := Option.some.inj hXc
  subst hXA
  have hAmem : A ∈ c' := by
    unfold blockAt? at hXc'
    exact List.mem_of_getElem? hXc'
  exact oldkey_dead_after_confirmed_announcement hK' hAmem hb hprod hconf

end MoltPetit.Model
