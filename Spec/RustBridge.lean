import Spec.Rust
import Spec.Model

/-!
# The maps from the Rust implementation's types to the model's.

Definitions only: no theorem, no proof. The development imports this file.
-/

/-! ### From `Rust.Bridge` -/

open Aeneas Std Result
namespace Rust

/-- Project a 256-bit hash to the model's `Nat` id by the standard
little-endian limb-packing `a + b·2^64 + c·2^128 + d·2^192`. This is
\emph{injective} on the four `u64` limbs, so the model-level id-injectivity
assumption (`SignedHashInjective`) is collision resistance of the full 256-bit
hash, not of a 64-bit projection. -/
def hashToNat (h : molt_petit.Hash) : Nat :=
  h.a.val + h.b.val * 2 ^ 64 + h.c.val * 2 ^ 128 + h.d.val * 2 ^ 192

/-- Project a Rust block to a model block. -/
def toModelBlock (b : molt_petit.Block) : MoltPetit.Model.Block :=
  { slot := b.slot.val, height := b.height.val,
    prev := b.prev.map hashToNat, id := hashToNat b.id,
    contentsHash := hashToNat b.contents_hash,
    keyIndex := b.key_index.val }

/-- Project a Rust chain to a model chain. -/
def toModelChain : molt_petit.Chain → MoltPetit.Model.Chain
  | .Nil => []
  | .Cons b tl => toModelBlock b :: toModelChain tl

/-- Project a Rust certificate claim to a model claim. -/
def toModelClaim (cl : molt_petit.CertClaim) : MoltPetit.Model.CertClaim :=
  { tipId := hashToNat cl.tip_id, tipSlot := cl.tip_slot.val
  , tipHeight := cl.tip_height.val, tail := toModelChain cl.tail }

/-- A model block is **Rust-signed** (for crypto dictionary `crypto`) when it
is the projection of a Rust block carrying a signature that verifies under its
slot producer's key. The `Signed` predicate the certified safety is
instantiated with. -/
def RustSigned {C} (I : molt_petit.Crypto C) (crypto : C) (n : Std.U64)
    (B : MoltPetit.Model.Block) : Prop :=
  ∃ (b : molt_petit.Block) (i : Std.U64) (key sig : molt_petit.Hash),
    toModelBlock b = B ∧ molt_petit.producer_for_slot n b.slot = ok i ∧
    I.key_for crypto i b.key_index = ok key ∧ I.verify crypto key b sig = ok true
end Rust

/-! ### From `Rust.Equiv` -/

open Aeneas Std Result
namespace Rust
open molt_petit

def toHashG (h : Hash) : HashG U64 := ⟨h.a, h.b, h.c, h.d⟩

def toBlockG (b : Block) : BlockG U64 :=
  { slot := b.slot
    height := b.height
    has_prev := b.prev.isSome
    prev := match b.prev with
            | some p => toHashG p
            | none => ⟨0#u64, 0#u64, 0#u64, 0#u64⟩
    id := toHashG b.id }

def toChainG : Chain → ChainG U64
  | Chain.Nil => ChainG.NilG
  | Chain.Cons b tl => ChainG.ConsG (toBlockG b) (toChainG tl)

abbrev UB : Backend U64Backend U64 Bool := U64Backend.Insts.Molt_petitBackendU64Bool
end Rust
