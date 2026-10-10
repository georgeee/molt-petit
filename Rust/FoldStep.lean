import Rust.Equiv
import MoltPetit.TS.Bridge
import Spec.Model

open Aeneas Std Result
namespace Rust
open molt_petit

/-- `BackendK.select` reduces to the conditional on `U64`. -/
theorem ubk_select (c : Bool) (a b : U64) :
    ∃ z : U64, UBK.select () c a b = ok z ∧ z.val = (if c then a.val else b.val) := by
  cases c
  · exact ⟨b, rfl, rfl⟩
  · exact ⟨a, rfl, rfl⟩

theorem ubk_select_val {c : Bool} {a b z : U64} (h : UBK.select () c a b = ok z) :
    z.val = (if c then a.val else b.val) := by
  cases c
  · injection h with h; subst h; rfl
  · injection h with h; subst h; rfl

/-- `BackendK.div` reduces to Nat division when the divisor is nonzero. -/
theorem ubk_div (a d : U64) (hd : d.val ≠ 0) :
    ∃ z : U64, UBK.div () a d = ok z ∧ z.val = a.val / d.val := by
  have ⟨z, hz, hzv⟩ := UScalar.div_spec a hd
  exact ⟨z, hz, hzv⟩

theorem ubk_div_val {a d z : U64} (hd : d.val ≠ 0) (h : UBK.div () a d = ok z) :
    z.val = a.val / d.val := by
  obtain ⟨z', hz', hzv⟩ := ubk_div a d hd
  rw [hz'] at h
  injection h with h
  subst h
  exact hzv

/-- `BackendK.rem` reduces to Nat remainder when the divisor is nonzero. -/
theorem ubk_rem (a d : U64) (hd : d.val ≠ 0) :
    ∃ z : U64, UBK.rem () a d = ok z ∧ z.val = a.val % d.val := by
  have hrem := UScalar.rem_spec a hd
  cases hres : a % d with
  | ok z =>
    rw [hres] at hrem
    exact ⟨z, hres, hrem⟩
  | fail e =>
    rw [hres] at hrem
    contradiction
  | div =>
    rw [hres] at hrem
    contradiction

theorem ubk_rem_val {a d z : U64} (hd : d.val ≠ 0) (h : UBK.rem () a d = ok z) :
    z.val = a.val % d.val := by
  obtain ⟨z', hz', hzv⟩ := ubk_rem a d hd
  rw [hz'] at h
  injection h with h
  subst h
  exact hzv

/-- `BackendK.monus` gives `a.val - b.val` in Nat. -/
theorem ubk_monus (a b : U64) :
    ∃ z : U64, UBK.monus () a b = ok z ∧ z.val = a.val - b.val := by
  change ∃ z : U64, (if a < b then ok 0#u64 else a - b) = ok z ∧ z.val = a.val - b.val
  split_ifs with hlt
  · refine ⟨0#u64, rfl, ?_⟩
    have : a.val < b.val := by simpa using hlt
    have : (0#u64).val = 0 := rfl
    omega
  · have hge : ¬ a.val < b.val := by
      intro h
      have : a < b := by simpa using h
      contradiction
    have hsub := UScalar.sub_equiv a b
    cases hs : a - b with
    | ok z =>
      rw [hs] at hsub
      refine ⟨z, rfl, ?_⟩
      omega
    | fail e =>
      rw [hs] at hsub
      contradiction
    | div =>
      rw [hs] at hsub
      exact False.elim hsub

theorem ubk_monus_val {a b z : U64} (h : UBK.monus () a b = ok z) :
    z.val = a.val - b.val := by
  obtain ⟨z', hz', hzv⟩ := ubk_monus a b
  rw [hz'] at h
  injection h with h
  subst h
  exact hzv

end Rust
