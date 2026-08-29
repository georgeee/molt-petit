import MoltPetit.Model.KeyRotation

/-!
# MoltPetit — executable regression tests for the key-rotation validator

These `#guard`s encode the *intended operational model* of in-band key rotation
and make the build fail if the validator ever stops expressing it:

1. **Rotation is possible.** A producer announces a rotation by signing a block
   under a *higher* index; the index-pinned validator `validChainK'` must
   **accept** such a chain. (A previous version of the pin — an *equality* pin
   `keyIndex = inForce` — silently made every rotation invalid: the in-force
   floor can only rise through a block carrying a higher index, which the
   equality pin itself forbade, freezing every producer at its initial index
   forever and making "a rotated-out key is dead" vacuous. `rot_accepted` is
   the regression test against that failure mode.)

2. **The rotation takes effect.** Once the announcement is `Δconf` deep, the
   in-force index has risen (`inforce_rises`).

3. **The rotated-out key is dead.** After the rotation confirms, a block
   declaring the *old* index is rejected (`old_key_dead`) — this is the
   validator-side half of the theft story: a stolen key stops working once the
   emergency rotation is `Δconf` deep.

Scenario: `n = 1` (single producer `0`, every slot is theirs), `Δconf = 2`.
The producer starts at index `0`, announces index `1` at slot 3, and the
announcement is confirmed from slot 5 onwards.
-/

set_option linter.hashCommand false

namespace MoltPetit.Model.KeyRotationTests

open MoltPetit.Model

private def G  : Block := { slot := 0, height := 0, prev := none,     id := 100, contentsHash := 0, keyIndex := 0 }
private def B1 : Block := { slot := 1, height := 1, prev := some 100, id := 101, contentsHash := 0, keyIndex := 0 }
private def B2 : Block := { slot := 2, height := 2, prev := some 101, id := 102, contentsHash := 0, keyIndex := 0 }
/-- The rotation announcement: producer 0 signs under the new index 1. -/
private def B3 : Block := { slot := 3, height := 3, prev := some 102, id := 103, contentsHash := 0, keyIndex := 1 }
private def B4 : Block := { slot := 4, height := 4, prev := some 103, id := 104, contentsHash := 0, keyIndex := 1 }
private def B5 : Block := { slot := 5, height := 5, prev := some 104, id := 105, contentsHash := 0, keyIndex := 1 }
/-- A block declaring the rotated-out index 0 after the rotation confirmed. -/
private def Bold : Block := { slot := 6, height := 6, prev := some 105, id := 106, contentsHash := 0, keyIndex := 0 }
/-- The honest continuation at the new index. -/
private def B6 : Block := { slot := 6, height := 6, prev := some 105, id := 107, contentsHash := 0, keyIndex := 1 }

/-- A chain that performs an in-band rotation (0 → 1 announced at slot 3). -/
private def rotChain : Chain := [G, B1, B2, B3, B4, B5, B6]

/-- The same chain, except the last block signs under the rotated-out index. -/
private def oldKeyChain : Chain := [G, B1, B2, B3, B4, B5, Bold]

-- (1) rotation is legal under the monotone validator …
#guard validChainK 1 rotChain = true
-- … and — the regression — under the index-pinned validator too
#guard validChainK' 1 2 rotChain = true

-- (2) the rotation takes effect: before the announcement confirms the in-force
-- index is still 0; once it is Δconf deep the in-force index has risen to 1
#guard inForce 1 2 rotChain 0 4 = 0   -- confirmed prefix at slot 4 = slots ≤ 2
#guard inForce 1 2 rotChain 0 5 = 1   -- slot 3 announcement now Δconf(=2) deep
#guard inForce 1 2 rotChain 0 6 = 1

-- (3) the rotated-out key is dead: declaring index 0 at slot 6 (where the
-- in-force index is 1) fails the pin — and the monotone rule — so the
-- index-pinned validator rejects the chain
#guard inForcePinned 1 2 oldKeyChain = false
#guard validChainK' 1 2 oldKeyChain = false

-- (4) division of labour between the pin and the monotone rule: between the
-- announcement and its confirmation only `keyMonoOk` forbids reverting to the
-- old index (the in-force floor has not yet risen, so the ≤-pin still passes)
private def revertEarly : Chain :=
  [G, B1, B2, B3, { slot := 4, height := 4, prev := some 103, id := 108, contentsHash := 0, keyIndex := 0 }]
#guard inForcePinned 1 2 revertEarly = true    -- pin alone does not catch it …
#guard keyMonoOk 1 revertEarly = false         -- … the monotone rule does
#guard validChainK' 1 2 revertEarly = false

-- (5) index jumps by more than one are legal (announce 5 directly). This
-- documents the index-inflation griefing surface: safety-irrelevant (the floor
-- only rises, rejecting more), but a liveness consideration for bounded key
-- trees — see the `validChainK'_sound` docstring.
private def jumpChain : Chain :=
  [G, B1, B2, { slot := 3, height := 3, prev := some 102, id := 109, contentsHash := 0, keyIndex := 5 }]
#guard validChainK' 1 2 jumpChain = true

-- (6) producer isolation (n = 2): producer 0's rotation does not raise
-- producer 1's floor. Slots alternate 0,1,0,1,…; producer 0 announces index 1
-- at slot 4; producer 1 keeps signing at index 0 afterwards — accepted.
private def G2  : Block := { slot := 0, height := 0, prev := none,     id := 200, contentsHash := 0, keyIndex := 0 }
private def C1  : Block := { slot := 1, height := 1, prev := some 200, id := 201, contentsHash := 0, keyIndex := 0 }
private def C2  : Block := { slot := 2, height := 2, prev := some 201, id := 202, contentsHash := 0, keyIndex := 0 }
private def C3  : Block := { slot := 3, height := 3, prev := some 202, id := 203, contentsHash := 0, keyIndex := 0 }
private def C4  : Block := { slot := 4, height := 4, prev := some 203, id := 204, contentsHash := 0, keyIndex := 1 }
private def C5  : Block := { slot := 5, height := 5, prev := some 204, id := 205, contentsHash := 0, keyIndex := 0 }
private def C6  : Block := { slot := 6, height := 6, prev := some 205, id := 206, contentsHash := 0, keyIndex := 1 }
private def C7  : Block := { slot := 7, height := 7, prev := some 206, id := 207, contentsHash := 0, keyIndex := 0 }
private def twoProd : Chain := [G2, C1, C2, C3, C4, C5, C6, C7]
#guard validChainK 2 twoProd = true
#guard validChainK' 2 4 twoProd = true
-- producer 0's in-force index rises once C4 confirms; producer 1's never does
#guard inForce 2 4 twoProd 0 8 = 1
#guard inForce 2 4 twoProd 1 8 = 0

end MoltPetit.Model.KeyRotationTests
