import Molt.ClientRule

/-!
# The induction over syncs, machine-checked (paper §6.3, mode 1)

The paper's own account of a continuously-syncing mode-1 client argues, on
paper, that a client's successive anchors stay on "the honest chain" by an
induction over syncs — and says so explicitly ("argued on paper, not itself
machine-checked"). This file gives that induction two layers:

* `SyncInductionData` — an ABSTRACT engine: an anchor sequence `a`, a
  reference-chain sequence `R`, a base case, a prefix-growth hypothesis on
  `R`, and a one-step membership-preservation hypothesis (`hStep`). Its
  invariant theorem is `Nat.rec` in two lines and needs no crypto, no
  protocol names, and (measured) depends on no axioms at all. Because
  `hStep` is the *only* field a different presentation needs to discharge
  differently, a future certificate-level induction (mode 1's certificate
  presentation, once a certificate-level "mem"-shaped per-sync lemma
  exists) reuses `.invariant` verbatim and only supplies a new `hStep`.
* `sync_induction_full_chain` — the CONCRETE full-chain instantiation:
  each step is exactly one application of `Molt.sync_rule_mem`
  (`Molt/ClientRule.lean:284`). The reference chain `R` is not a fixed,
  privileged "honest chain" object — it is an arbitrary witness family the
  client never learns is honest; the theorem is conditional on `R` having
  three properties, matching the paper's own scoping (existence of such an
  `R` is liveness territory, outside the safety hypotheses):
  1. `hRLe` — the reference tip is at least as tall as the accepted one, at
     every sync (feeds `sync_rule_mem`'s `hLe`);
  2. `hRVal`/`hRRecent`/`hRLong` — the reference chain is itself valid,
     recent (at the same clock as the accepted chain), and longer than `n`
     blocks, at every sync;
  3. `hRPrefix` — the reference chains are prefix-ordered over time, used
     to promote the previous sync's invariant fact across `R`'s own growth
     (`List.IsPrefix.mem`) before feeding it to `sync_rule_mem` as `hA'`.

  The paper's density remark ("density keeps a recent taller fork's `n`-deep
  block below its divergence, hence on the honest chain — an informal
  argument") is not needed under these hypotheses: `hRLe` assumes directly
  what the informal argument was for, and no `MaturedWindowsDense`-flavoured
  reasoning appears anywhere in this file beyond what `sync_rule_mem` (via
  `deep_block_span`) already consults internally. The base case (`hBase`) is
  taken as raw data — "`a 0` = the join checkpoint" — matching the paper's
  own framing of the checkpoint as "the op-model's fresh trust event ...
  outside the formal development"; deriving it from `client_refresh_rule` is
  a separate, additive follow-up (see `docs/rollout/ROLLOUT_NOTES.md`, row W4), not
  attempted here. `Δ` is fixed to `n` throughout, matching `sync_rule_mem`'s
  own `KeyStealingEUFCMA n n` instantiation.
-/

namespace Molt

/-- A positional membership fact converted to a plain `List.Mem` fact. -/
theorem mem_of_blockAt? {c : Chain} {h : Nat} {B : Block}
    (hAt : blockAt? c h = some B) : B ∈ c := by
  unfold blockAt? at hAt
  exact List.mem_of_getElem? hAt

/-- The abstract engine behind the induction over syncs: deliberately
crypto- and protocol-free, so it is reusable at any client presentation. -/
structure SyncInductionData (n : Nat) where
  /-- The client's anchor at each sync. -/
  a : Nat → Block
  /-- The reference ("honest") chain as of each sync — an arbitrary witness
  family, never assumed unique or privileged. -/
  R : Nat → Chain
  /-- The reference chains grow monotonically (are prefix-ordered) over
  time. -/
  hPrefix : ∀ k, R k <+: R (k + 1)
  /-- The base case: the join checkpoint, taken as data. -/
  hBase : a 0 ∈ R 0
  /-- The abstracted per-sync agreement property: given the previous anchor
  already promoted onto the current reference chain, the next anchor lands
  on it too. The one field a different presentation supplies differently. -/
  hStep : ∀ k, a k ∈ R (k + 1) → a (k + 1) ∈ R (k + 1)

/-- **The induction over syncs, abstract form.** Every anchor lies on the
reference chain of its own sync. -/
theorem SyncInductionData.invariant {n : Nat} (d : SyncInductionData n) :
    ∀ k, d.a k ∈ d.R k := by
  intro k
  induction k with
  | zero => exact d.hBase
  | succ k ih => exact d.hStep k ((d.hPrefix k).mem ih)

/-- **The induction over syncs, full-chain instantiation.** A continuously
re-syncing mode-1 client's anchor lies on an (arbitrary, unknown-to-be-honest)
reference chain `R` at every sync, given that `R` is itself always valid,
recent, longer than `n` blocks, at least as tall as the accepted chain, and
grows monotonically over time. Supersedes the paper's informal induction
argument (`paper/molt.tex` §6.3, "argued on paper, not itself
machine-checked"); the density remark there is not needed here (see the
module docstring). -/
theorem sync_induction_full_chain
    {n : Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {G : Block}
    (now : Nat → Nat)
    (c R : Nat → SignedChain Sig)
    (hEUF : ∀ k, KeyStealingEUFCMA n n ops registry rented Stolen
      honestSigned (now k) n)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    {tip : Nat → Block}
    (hTip : ∀ k, (stripSigs (c k)).getLast? = some (tip k))
    (hRec : ∀ k, now k ≤ (tip k).slot + n)
    (hLong : ∀ k, n < (stripSigs (c k)).length)
    (hVal : ∀ k, validSignedChainK' n n ops registry (c k) = true)
    (hCadence : ∀ k, now (k + 1) ≤ now k + n)
    {a : Nat → Block}
    (hAnchor : ∀ k, blockAt? (stripSigs (c k))
      ((stripSigs (c k)).length - 1 - n) = some (a k))
    (hAcc : ∀ k, a k ∈ stripSigs (c (k + 1)))
    (hBudget : ∀ k u, now (k + 1) < u + 5 * n →
      (badSlotsIn (badKeyrot n n rented Stolen (stripSigs (c (k + 1)))) u n).card
        ≤ faultBudget n)
    {rTip : Nat → Block}
    (hRTip : ∀ k, (stripSigs (R k)).getLast? = some (rTip k))
    (hRVal : ∀ k, validSignedChainK' n n ops registry (R k) = true)
    (hRRecent : ∀ k, now k ≤ (rTip k).slot + n)
    (hRLong : ∀ k, n < (stripSigs (R k)).length)
    (hRLe : ∀ k, (tip k).height ≤ (rTip k).height)
    (hRPrefix : ∀ k, stripSigs (R k) <+: stripSigs (R (k + 1)))
    (hBase : a 0 ∈ stripSigs (R 0)) :
    ∀ k, a k ∈ stripSigs (R k) := by
  let d : SyncInductionData n :=
    { a := a
      R := fun k => stripSigs (R k)
      hPrefix := hRPrefix
      hBase := hBase
      hStep := by
        intro k hMem
        obtain ⟨i', hi', hEq⟩ :=
          sync_rule_mem hn (hEUF (k + 1)) hHash
            (hVal k) (hTip k) (hRec k) (hLong k) (hAnchor k) (hCadence k)
            (hAcc k) hMem (hBudget k)
            (hVal (k + 1)) (hRVal (k + 1)) (hTip (k + 1)) (hRTip (k + 1))
            (hRec (k + 1)) (hRRecent (k + 1)) (hLong (k + 1)) (hRLong (k + 1))
            (hRLe (k + 1)) (hAnchor (k + 1))
        exact mem_of_blockAt? hEq }
  exact d.invariant

end Molt
