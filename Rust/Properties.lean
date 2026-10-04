import Spec.Rust

/-!
# Proofs about the Rust-extracted Molt Petit core

These theorems are about the **Aeneas-emitted** definitions in
`Spec/Rust.lean` (the Rust crate `rust/src/lib.rs` compiled to Lean by
Charon + Aeneas), exactly as the Thales-path theorems are about the
Thales-emitted TS definitions. Functions are `Result`-monadic over machine
integers, so specs are Hoare-style: `f x ⦃ r => P r ⦄` says the call
succeeds and its result satisfies `P` (`WP.spec`, which is `False` on
`fail`/`div`).
-/

open Aeneas Std Result

namespace molt_petit

/-- Extract the success value and postcondition from a Hoare triple. -/
theorem spec_ok_exists {α} {x : Result α} {p : α → Prop} (h : x ⦃ r => p r ⦄) :
    ∃ a, x = ok a ∧ p a := by
  cases hx : x with
  | ok a => rw [hx] at h; exact ⟨a, rfl, by simpa using h⟩
  | fail e => rw [hx] at h; simp at h
  | div => rw [hx] at h; simp at h

/-- The round-robin leader is always a valid participant index `< n`. -/
theorem producer_for_slot_spec (n slot : U64) (hn : 0 < n.val) :
    producer_for_slot n slot ⦃ r => r.val < n.val ⦄ := by
  unfold producer_for_slot
  step with UScalar.rem_spec as ⟨ r, hr ⟩
  scalar_tac

/-- `quorum n` succeeds (no overflow) and computes `⌈2n/3⌉ = ⌊(2n+2)/3⌋`. -/
theorem quorum_spec (n : U64) (h : 2 * n.val + 2 ≤ U64.max) :
    quorum n ⦃ q => q.val = (2 * n.val + 2) / 3 ⦄ := by
  unfold quorum
  step*

/-- `max_byzantine n` succeeds for `n ≥ 1` and computes `⌊(n-1)/3⌋`. -/
theorem max_byzantine_spec (n : U64) (hn : 1 ≤ n.val) :
    max_byzantine n ⦃ f => f.val = (n.val - 1) / 3 ⦄ := by
  unfold max_byzantine
  step*

/-- Pure arithmetic core of the BFT bound. -/
theorem quorum_add_max_byzantine_le (n : Nat) :
    (2 * n + 2) / 3 + (n - 1) / 3 ≤ n := by omega

/-- **Quorum/Byzantine bound on the extracted functions.** For `1 ≤ n` and no
overflow, both succeed and `quorum n + max_byzantine n ≤ n` — the Rust
analogue of `MoltPetit.Model.quorum_plus_byzantine_le`. -/
theorem quorum_plus_byzantine_le
    (n : U64) (hn : 1 ≤ n.val) (h : 2 * n.val + 2 ≤ U64.max) :
    ∃ q f, quorum n = ok q ∧ max_byzantine n = ok f ∧ q.val + f.val ≤ n.val := by
  obtain ⟨q, hq, hqv⟩ := spec_ok_exists (quorum_spec n h)
  obtain ⟨f, hf, hfv⟩ := spec_ok_exists (max_byzantine_spec n hn)
  exact ⟨q, f, hq, hf, by rw [hqv, hfv]; exact quorum_add_max_byzantine_le n.val⟩

-- Structural facts about the recursive extracted functions.

@[simp] theorem window_count_nil (u len : U64) :
    window_count Chain.Nil u len = ok 0#u64 := by unfold window_count; rfl

@[simp] theorem links_ok_nil : links_ok Chain.Nil = ok true := by unfold links_ok; rfl

@[simp] theorem valid_chain_nil (n : U64) : valid_chain n Chain.Nil = ok true := by
  unfold valid_chain; rfl

/-- The validator rejects the failure result. -/
@[simp] theorem validate_certified_invalid {C} (I : Crypto C) (n : U64) (crypto : C) :
    validate_certified_chain I n crypto CertifiedChain.Invalid = ok false := by
  unfold validate_certified_chain; rfl

/-- Invert one monadic bind: if `m >>= f` succeeds, `m` succeeded and so did
the continuation. -/
theorem bind_inv {α β} {m : Result α} {f : α → Result β} {c : β}
    (h : (do let a ← m; f a) = ok c) : ∃ a, m = ok a ∧ f a = ok c := by
  cases m with
  | ok a => exact ⟨a, rfl, by simpa using h⟩
  | fail e => simp at h
  | div => simp at h

/-- **Production soundness (validate-before-ship).** `produce_block_cert` either
returns `Invalid` or returns a certified chain that passes the very same
`validate_certified_chain` every node runs — so nothing about how the block is
built needs to be trusted for soundness. The Rust analogue of the TS final-gate
argument. -/
theorem produce_block_cert_sound {C} (I : Crypto C)
    (n me at_slot : U64) (new_id contents_hash : Hash) (key_index : U64) (sk : Hash)
    (crypto : C) (cert : Hash) (suffix : SignedChain) (cc : CertifiedChain)
    (h : produce_block_cert I n me at_slot new_id contents_hash key_index sk crypto cert
          suffix = ok cc) :
    cc = CertifiedChain.Invalid ∨ validate_certified_chain I n crypto cc = ok true := by
  unfold produce_block_cert at h
  obtain ⟨i, _, h⟩ := bind_inv h
  split at h
  · -- not the leader: ships Invalid
    injection h with heq; left; exact heq.symm
  · -- own slot: peel the construction, then split on the final validator gate
    obtain ⟨cl, _, h⟩ := bind_inv h
    obtain ⟨tipH, _, h⟩ := bind_inv h
    obtain ⟨tipI, _, h⟩ := bind_inv h
    obtain ⟨i1, _, h⟩ := bind_inv h
    obtain ⟨sig, _, h⟩ := bind_inv h
    obtain ⟨ns, _, h⟩ := bind_inv h
    obtain ⟨b, hb, h⟩ := bind_inv h
    split at h
    · -- validator accepted: the shipped chain is exactly the validated one
      rename_i hbtrue
      injection h with heq
      right; rw [← heq, hb, hbtrue]
    · -- validator rejected: ships Invalid
      injection h with heq; left; exact heq.symm

end molt_petit
