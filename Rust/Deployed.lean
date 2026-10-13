import Rust.Equiv
import Rust.FoldStep
import MoltPetit.Model.Soundness
import MoltPetit.Model.Pass28
import Spec.Statements

open Aeneas Std Result

namespace Rust

open molt_petit

theorem u64_add_ok {x y : U64} (h : x.val + y.val < 2 ^ 64) :
    ∃ z : U64, x + y = ok z ∧ z.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  split at hadd
  · rename_i z hz
    exact ⟨z, hz, hadd.2.1⟩
  · rename_i e he
    exfalso
    exact hadd (by simp only [UScalar.inBounds]; omega)

theorem hashToNat_inj {x y : molt_petit.Hash} (h : hashToNat x = hashToNat y) : x = y := by
  obtain ⟨xa, xb, xc, xd⟩ := x
  obtain ⟨ya, yb, yc, yd⟩ := y
  have hxa := xa.val_lt
  have hxb := xb.val_lt
  have hxc := xc.val_lt
  have hxd := xd.val_lt
  have hya := ya.val_lt
  have hyb := yb.val_lt
  have hyc := yc.val_lt
  have hyd := yd.val_lt
  dsimp [hashToNat] at h
  have ha : xa = ya := UScalar.eq_of_val_eq (by omega)
  have hb : xb = yb := UScalar.eq_of_val_eq (by omega)
  have hc : xc = yc := UScalar.eq_of_val_eq (by omega)
  have hd : xd = yd := UScalar.eq_of_val_eq (by omega)
  rw [ha, hb, hc, hd]

end Rust
