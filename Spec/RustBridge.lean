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

/-! ### Certificate fold (Pass 26: review items N2, N5)

The fold circuit's state and its driver: the Rust step functions
(`cert_step_*_be`, `cert_next_*_be`) applied one block at a time from the
genesis state. `Signed` is not here; the circuit checks it with its signature
gadget, and the statements take it as a hypothesis per block. -/

open Aeneas Std Result
namespace Rust
open molt_petit

abbrev UBK : BackendK U64Backend U64 Bool := U64Backend.Insts.Molt_petitBackendKU64Bool

/-- `k` padding entries `(0, 0)` in front of a buffer. -/
def padTail : Nat → TailG U64 → TailG U64
  | 0, t => t
  | k + 1, t => .TCons 0#u64 0#u64 (padTail k t)

/-- The genesis buffer, length `n - 1`: padding, then the genesis slot
(empty for `n ≤ 1`). -/
def initTail (n : Nat) (gslot : U64) : TailG U64 :=
  if n < 2 then .TNil else padTail (n - 2) (.TCons 1#u64 gslot .TNil)

/-- `k` zero floors. -/
def zeroFloors : Nat → FloorsG U64
  | 0 => .FNil
  | k + 1 => .FCons 0#u64 (zeroFloors k)

/-- The genesis floors, length `n`: the genesis key index for producer 0
(the genesis slot is 0), zero for the rest. -/
def initFloors (n : Nat) (gki : U64) : FloorsG U64 :=
  match n with
  | 0 => .FNil
  | k + 1 => .FCons gki (zeroFloors k)

/-- The floors as a function of the producer (0 past the list). -/
def floorsFun : FloorsG U64 → Nat → Nat
  | .FNil, _ => 0
  | .FCons f _, 0 => f.val
  | .FCons _ tl, i + 1 => floorsFun tl i

/-- The state after the genesis. -/
def genesisState (n : Nat) (G : Block) : CertStateG U64 :=
  { tip_id := toHashG G.id, tip_slot := G.slot, tip_height := G.height
  , tail := initTail n G.slot }

/-- The state after folding in `b`, with the updated buffer `t'`. -/
def stepState (b : Block) (t' : TailG U64) : CertStateG U64 :=
  { tip_id := toHashG b.id, tip_slot := b.slot, tip_height := b.height, tail := t' }

/-- Mode 1: every step of `bs` is accepted, threading the floors; `out` is
the final floors (what the certificate exposes). -/
def FoldK (n q : U64) : CertStateG U64 → FloorsG U64 → List Block → FloorsG U64 → Prop
  | _, fl, [], out => out = fl
  | st, fl, b :: bs, out =>
      cert_step_k_be UBK () n q st fl (toBlockG b) b.key_index = ok true ∧
      ∃ t' fl', cert_next_tail_be UB () st.tail b.slot = ok t' ∧
        cert_next_floors_be UBK () n fl (toBlockG b) b.key_index = ok fl' ∧
        FoldK n q (stepState b t') fl' bs out

/-- Mode 2: every step of `bs` is accepted under the schedule `slot / era`. -/
def FoldSched (n q era : U64) : CertStateG U64 → List Block → Prop
  | _, [] => True
  | st, b :: bs =>
      cert_step_sched_be UBK () n q era st (toBlockG b) b.key_index = ok true ∧
      ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' ∧
        FoldSched n q era (stepState b t') bs

/-- Mode 3: every step of `bs` is accepted, threading the generation `g`
(the previous block's key index). -/
def FoldLock (n q : U64) : CertStateG U64 → U64 → List Block → Prop
  | _, _, [] => True
  | st, g, b :: bs =>
      cert_step_lock_be UBK () n q st g (toBlockG b) b.key_index = ok true ∧
      ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' ∧
        FoldLock n q (stepState b t') b.key_index bs

/-- The model claim of the history `G :: bs`: its tip, and the blocks at or
above the tip's density bound `tipSlot + 2 - n`. -/
def modelClaimOf (n : Nat) (G : MoltPetit.Model.Block) (bs : List MoltPetit.Model.Block) :
    MoltPetit.Model.CertClaim :=
  let t := (G :: bs).getLast (List.cons_ne_nil _ _)
  { tipId := t.id, tipSlot := t.slot, tipHeight := t.height
  , tail := (G :: bs).filter fun x => decide (t.slot + 2 - n ≤ x.slot) }

/-! ### The certificate's public state (Pass 26, stage C)

The fold circuit exposes the final state; these drivers name it. -/

/-- A 4-limb hash as a number (`hashToNat` through `toHashG`). -/
def hashGToNat (h : HashG U64) : Nat :=
  h.a.val + h.b.val * 2 ^ 64 + h.c.val * 2 ^ 128 + h.d.val * 2 ^ 192

/-- The slots of the buffer's present entries (flag `1`), oldest first. -/
def tailSlots : TailG U64 → List Nat
  | .TNil => []
  | .TCons f s tl => if f.val = 1 then s.val :: tailSlots tl else tailSlots tl

/-- What a client reads off the certificate's public state. The buffer is a
superset of the claim's tail (it can hold slots below every window still to
be checked), so the view keeps the slots the claim's tail keeps:
`tipSlot + 2 - n ≤ s`. -/
def stateView (n : Nat) (st : CertStateG U64) : Nat × Nat × Nat × List Nat :=
  (hashGToNat st.tip_id, st.tip_slot.val, st.tip_height.val,
   (tailSlots st.tail).filter fun s => decide (st.tip_slot.val + 2 - n ≤ s))

/-- `FoldK`, also naming the final state `stO` (the circuit's public state). -/
def FoldKOut (n q : U64) :
    CertStateG U64 → FloorsG U64 → List Block → CertStateG U64 → FloorsG U64 → Prop
  | st, fl, [], stO, out => stO = st ∧ out = fl
  | st, fl, b :: bs, stO, out =>
      cert_step_k_be UBK () n q st fl (toBlockG b) b.key_index = ok true ∧
      ∃ t' fl', cert_next_tail_be UB () st.tail b.slot = ok t' ∧
        cert_next_floors_be UBK () n fl (toBlockG b) b.key_index = ok fl' ∧
        FoldKOut n q (stepState b t') fl' bs stO out

/-- `FoldSched`, also naming the final state. -/
def FoldSchedOut (n q era : U64) : CertStateG U64 → List Block → CertStateG U64 → Prop
  | st, [], stO => stO = st
  | st, b :: bs, stO =>
      cert_step_sched_be UBK () n q era st (toBlockG b) b.key_index = ok true ∧
      ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' ∧
        FoldSchedOut n q era (stepState b t') bs stO

/-- `FoldLock`, also naming the final state and generation. -/
def FoldLockOut (n q : U64) : CertStateG U64 → U64 → List Block → CertStateG U64 → U64 → Prop
  | st, g, [], stO, gO => stO = st ∧ gO = g
  | st, g, b :: bs, stO, gO =>
      cert_step_lock_be UBK () n q st g (toBlockG b) b.key_index = ok true ∧
      ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' ∧
        FoldLockOut n q (stepState b t') b.key_index bs stO gO
end Rust
