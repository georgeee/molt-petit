import MoltPetit.Model.KeyStealingLockstep

/-!
# MoltPetit — mode 3 (free-cadence lockstep) at the certificate presentation

The certificate form of `KeyStealingLockstep.lean`'s mode 3, delivering W1:
the honest-scope bound that mode 3's theorems are "full chains only, the
certificate form is future work" is discharged here.

Four design answers, recorded up front because they are not visible from the
statements alone:

1. **Pinning cannot be gated at fold time.** `rosterGen` is execution-level
   and unknown to any verifier, but it is DERIVED at fold-state level: the
   fold carries exactly the state the no-mixing rule needs — the prefix
   tip's declared generation, threaded as a single `Nat`. The
   certificate-level pinning theorems (`lockstep_cert_declares_rosterGen`,
   `lockstep_cert_gen_pinned`) are corollaries of the existing
   `lockstep_declares_rosterGen`, applied to the reconstructed recent full
   chain. No per-window table, no running counter beyond the one threaded
   `Nat`, no lagged counter carried as wire data: `lagSched` stays
   proof-internal, exactly as in the full-chain development.
2. **Reuse is near-total.** Every reconstruction step (`validChain`
   extension, density bookkeeping, suffix attachment, materialisation) is
   copied from `KeyStealingScheduleCert.lean`'s `GroundedCertSched` path
   with the pin conjunct replaced by the no-mixing conjunct; the agreement
   theorem routes through the *existing*, unmodified
   `lockstep_validSignedChainSched` and `sched_deep_block_agreement_of_length`
   — nothing in `KeyStealingLockstep.lean` or `KeyStealingScheduleResults.lean`
   is touched.
3. **The budget needs no restating.** `LockstepPackage`'s `rentBound` /
   `exposedBound` / `budget_le` are chain-independent (`badSched` at
   `lagSched n rosterGen` reads no chain), so the certificate theorem takes
   `hP : LockstepPackage` unchanged — no `AttestedHistory` quantification,
   the same simplification mode 2's certificate form already enjoyed.
4. **The wire contract.** Beyond the plain claim, the certificate attests
   the tip generation `g` — the one-`Nat` analogue of `GroundedCertK`'s
   floor vector. For `n ≥ 2` this is provably redundant
   (`groundedCertLock_gen_of_tail`: the tip block is the last element of
   `cl.tail`, so `g` is a function of the claim alone); only `n = 1` (empty
   tail) genuinely needs the extra counter. Leaving `g` unauthenticated
   would be a real attack — `g* = 0` lets a suffix block signed under a
   stolen retired-generation key pass, exactly mode 2's `schedule* ≡ 0`
   attack — so implementations should derive `g` from `cl.tail`'s last
   block whenever `n ≥ 2`, and this docstring records the wire contract as
   `GroundedCertK`'s does.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- (A) No-mixing algebra
-- ===========================================================================

/-- `lockstepOk` over an append: the no-mixing relation splits the same way
`List.Pairwise` splits over `++` — left, right, and cross. Public replacement
for the private `lockstep_rel`/`lockstep_const` pair in `KeyStealingLockstep.lean`,
which carry position arguments this development does not need. -/
theorem lockstepOk_append_iff {n : Nat} (c s : Chain) :
    lockstepOk n (c ++ s) = true ↔
      lockstepOk n c = true ∧ lockstepOk n s = true ∧
        ∀ a ∈ c, ∀ b ∈ s, (a.slot / n = b.slot / n → a.keyIndex = b.keyIndex) ∧
          a.keyIndex ≤ b.keyIndex := by
  rw [lockstepOk_iff_pairwise, lockstepOk_iff_pairwise, lockstepOk_iff_pairwise,
    List.pairwise_append]

/-- Roster-wide monotonicity (`lockstepOk`) implies same-producer
monotonicity (`keyMonoOk`): the FULL `validSignedChainLock` is reconstructible
from certificate data alone. Unlike mode 2's certificate path, no core
lockstep validator and no core mirrors of the lockstep theorems are needed
here. -/
theorem keyMonoOk_of_lockstepOk {n : Nat} {c : Chain} (h : lockstepOk n c = true) :
    keyMonoOk n c = true := by
  rw [keyMonoOk_iff_pairwise]
  exact ((lockstepOk_iff_pairwise c).mp h).imp (fun hab _ => hab.2)

/-- The suffix-side no-mixing check a certificate-syncing verifier runs: fold
the boundary state (tip slot, tip generation) through the suffix. Each block
must not decrease the generation, and must equal it when the block lies in
the same grid window (`slot / n`) as the current state; the state then
becomes `(b.slot, b.keyIndex)`. Analogue of `keyMonoFrom` with a single `Nat`
instead of an `n`-vector, and of `schedPinned` run over a suffix in mode 2.
Pure function of `(tipSlot, g, suffix)`. -/
def lockstepFrom (n : Nat) : Nat → Nat → Chain → Bool
  | _, _, [] => true
  | ts, g, b :: rest =>
      decide (g ≤ b.keyIndex ∧ (ts / n = b.slot / n → g = b.keyIndex))
      && lockstepFrom n b.slot b.keyIndex rest

/-- Sandwich: if `a ≤ t ≤ b` and `a` and `b` sit in the same `n`-window, so
does `t`. The one genuinely new piece of arithmetic this item needs; `omega`
alone cannot see through `Nat` division, so the window facts are established
as opaque atoms first via `Nat.div_le_div_right`, then closed by `omega`. -/
private theorem div_sandwich {a t b n : Nat} (ha : a ≤ t) (htb : t ≤ b)
    (h : a / n = b / n) : t / n = a / n := by
  have h1 : a / n ≤ t / n := Nat.div_le_div_right ha
  have h2 : t / n ≤ b / n := Nat.div_le_div_right htb
  omega

/-- Attaching a `lockstepFrom`-checked suffix to a `lockstepOk` prefix yields
a `lockstepOk` whole, given the prefix's own boundary facts against the fold's
starting state `(ts, g)`. Serves BOTH the one-block fold step of
`groundedCertLock_history` (`s := [b]`) and the suffix attachment in
`groundedCertLock_suffix_history`. -/
theorem lockstepOk_append_of_from {n : Nat} {c s : Chain} {ts g : Nat}
    (hLock : lockstepOk n c = true)
    (hSlots : ∀ a ∈ c, a.slot ≤ ts)
    (hMax : ∀ a ∈ c, a.keyIndex ≤ g)
    (hConst : ∀ a ∈ c, a.slot / n = ts / n → a.keyIndex = g)
    (hGt : ∀ b ∈ s, ts < b.slot)
    (hSS : StrictSlots s)
    (hFrom : lockstepFrom n ts g s = true) :
    lockstepOk n (c ++ s) = true := by
  induction s generalizing c ts g with
  | nil => simpa using hLock
  | cons b rest ih =>
    rw [lockstepFrom, Bool.and_eq_true, decide_eq_true_eq] at hFrom
    obtain ⟨hb, hrest⟩ := hFrom
    have hSingle : lockstepOk n (c ++ [b]) = true := by
      rw [lockstepOk_append_iff]
      refine ⟨hLock, by simp [lockstepOk], ?_⟩
      intro a ha b' hb'
      rw [List.mem_singleton] at hb'
      symm at hb'; subst hb'
      refine ⟨fun haeq => ?_, le_trans (hMax a ha) hb.1⟩
      have hsand : ts / n = a.slot / n :=
        div_sandwich (hSlots a ha) (le_of_lt (hGt b (List.mem_cons_self ..))) haeq
      have hgb : g = b.keyIndex := hb.2 (hsand.trans haeq)
      exact (hConst a ha hsand.symm).trans hgb
    have hEq : c ++ b :: rest = (c ++ [b]) ++ rest := by simp
    rw [hEq]
    have hSlots' : ∀ a ∈ c ++ [b], a.slot ≤ b.slot := by
      intro a ha
      rcases List.mem_append.mp ha with hac | hab
      · exact le_of_lt (lt_of_le_of_lt (hSlots a hac) (hGt b (List.mem_cons_self ..)))
      · rw [List.mem_singleton] at hab; symm at hab; subst hab; exact le_refl _
    have hMax' : ∀ a ∈ c ++ [b], a.keyIndex ≤ b.keyIndex := by
      intro a ha
      rcases List.mem_append.mp ha with hac | hab
      · exact le_trans (hMax a hac) hb.1
      · rw [List.mem_singleton] at hab; symm at hab; subst hab; exact le_refl _
    have hConst' : ∀ a ∈ c ++ [b], a.slot / n = b.slot / n → a.keyIndex = b.keyIndex := by
      intro a ha haeq
      rcases List.mem_append.mp ha with hac | hab
      · have hsand : ts / n = a.slot / n :=
          div_sandwich (hSlots a hac) (le_of_lt (hGt b (List.mem_cons_self ..))) haeq
        have hgb : g = b.keyIndex := hb.2 (hsand.trans haeq)
        exact (hConst a hac hsand.symm).trans hgb
      · rw [List.mem_singleton] at hab; symm at hab; subst hab; rfl
    exact ih hSingle hSlots' hMax' hConst' (List.pairwise_cons.mp hSS).1
      (List.pairwise_cons.mp hSS).2 hrest

-- ===========================================================================
-- (B) The certificate
-- ===========================================================================

/-- The lockstep certificate derivation: `GroundedCertSched`'s shape (same
tail buffer, same Nat-form density premise, so `windowCount_append` /
`windowCount_filter_low` transfer verbatim) with the pin premise replaced by
the two-clause no-mixing check against the threaded tip generation `g`, and
the state stepped to `b.keyIndex`. Every check is a pure function of
`(claim, g, block)` — what a recursive certificate attests per fold. The
genesis state is `G.keyIndex`, matching `LockstepPackage.genesis_gen`. -/
inductive GroundedCertLock (n : Nat) (Signed : Block → Prop) (G : Block) :
    CertClaim → Nat → Prop
  | genesis :
      genesisOk G = true →
      G.slot = 0 →
      Signed G →
      GroundedCertLock n Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) } G.keyIndex
  | extend (cl : CertClaim) (g : Nat) (b : Block) :
      GroundedCertLock n Signed G cl g →
      b.height = cl.tipHeight + 1 →
      cl.tipSlot < b.slot →
      b.prev = some cl.tipId →
      Signed b →
      g ≤ b.keyIndex →
      (cl.tipSlot / n = b.slot / n → g = b.keyIndex) →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCertLock n Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) } b.keyIndex

/-- What a `GroundedCertLock` derivation reconstructs: a `validChain`-accepted,
`lockstepOk`-passing prefix matching the claim, tip additionally carrying
`keyIndex = g`, and two invariants (every prefix block's generation ≤ `g`;
every prefix block in the tip's grid window declares `g`) that make the
`extend` step purely arithmetic — no positional reasoning about the tip
inside `c` is ever needed. -/
structure GroundedHistoryLock (n : Nat) (Signed : Block → Prop) (G : Block)
    (cl : CertClaim) (g : Nat) (c : Chain) : Prop where
  valid     : validChain n c = true
  lock      : lockstepOk n c = true
  head      : blockAt? c 0 = some G
  tip       : ∃ t : Block, c.getLast? = some t ∧
                t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight ∧
                t.keyIndex = g
  tail_eq   : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)
  len_eq    : c.length = cl.tipHeight + 1
  signed    : ∀ B ∈ c, Signed B
  gen_max   : ∀ B ∈ c, B.keyIndex ≤ g
  win_const : ∀ B ∈ c, B.slot / n = cl.tipSlot / n → B.keyIndex = g

/-- **History reconstruction for the lockstep certificate** (mirrors
`groundedCertSched_history` minus every floor step, plus no-mixing
propagation via `lockstepOk_append_of_from`). -/
theorem groundedCertLock_history {n : Nat} (hn : 1 ≤ n) {Signed : Block → Prop}
    {G : Block} {cl : CertClaim} {g : Nat}
    (h : GroundedCertLock n Signed G cl g) :
    ∃ c : Chain, GroundedHistoryLock n Signed G cl g c := by
  induction h with
  | genesis hG hSlot hSig =>
    refine ⟨[G], ?_, by simp [lockstepOk], by simp [blockAt?],
      ⟨G, by simp, rfl, rfl, rfl, rfl⟩, rfl, ?_,
      fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ hSig,
      fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ le_refl _,
      fun B hB _ => by rw [List.mem_singleton] at hB; exact hB ▸ rfl⟩
    · -- validChain n [G]
      rw [validChain, show ([G] : Chain).getLast? = some G from rfl,
        Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hG, rfl⟩, ?_⟩
      show maturedWindowsDense n [G] G.slot = true
      rw [maturedWindowsDense, List.all_eq_true]
      intro u hu
      have hu' := List.mem_range.mp hu
      have hn1 : n = 1 ∧ u = 0 := by omega
      obtain ⟨rfl, rfl⟩ := hn1
      rw [windowDense, decide_eq_true_eq]
      have : windowCount [G] 0 1 = 1 := by
        simp [windowCount, blockInWindow, hSlot]
      rw [this]
      unfold quorum
      omega
    · -- length
      have : G.height = 0 := by
        rw [genesisOk, decide_eq_true_eq] at hG
        exact hG.1
      simp [this]
  | extend cl g b hcl hH hS hP hSig hLe hWin hD ih =>
    obtain ⟨c, hist⟩ := ih
    obtain ⟨t, hTipEq, htId, htSlot, htHeight, htKey⟩ := hist.tip
    have hChild : childOk t b = true := by
      rw [childOk, decide_eq_true_eq]
      exact ⟨by omega, by omega, by rw [hP, htId]⟩
    have hMat := (validChain_sound hist.valid).2.2.2
    have hStrictC : StrictSlots c := (validChain_sound hist.valid).2.1
    have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
    have hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
        windowDense n (c ++ [b]) u = true := by
      intro u hu
      rw [windowDense, decide_eq_true_eq]
      by_cases hOld : u + n ≤ t.slot + 1
      · calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
          _ ≤ windowCount (c ++ [b]) u n :=
              windowCount_mono (List.sublist_append_left c [b])
      · have hcount := hD u (by omega) hu
        have heq : windowCount (cl.tail ++ [b]) u n = windowCount (c ++ [b]) u n := by
          rw [windowCount_append, windowCount_append, hist.tail_eq,
            windowCount_filter_low (by omega)]
        omega
    have hSlotsC : ∀ a ∈ c, a.slot ≤ t.slot := fun a ha =>
      slot_le_tip_of_mem hStrictC hTipEq ha
    have hLockNew : lockstepOk n (c ++ [b]) = true :=
      lockstepOk_append_of_from hist.lock hSlotsC hist.gen_max
        (fun a ha haeq => hist.win_const a ha (by rw [haeq, htSlot]))
        (fun b' hb' => by
          rw [List.mem_singleton] at hb'; symm at hb'; subst hb'; rw [htSlot]; exact hS)
        (by simp [StrictSlots])
        (by
          unfold lockstepFrom
          rw [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨hLe, ?_⟩, rfl⟩
          rw [htSlot]
          exact hWin)
    refine ⟨c ++ [b], ?_, hLockNew, ?_, ⟨b, by simp, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact validChain_append_one hist.valid hTipEq hChild hAllDense
    · -- head preserved
      have hcLen : 0 < c.length := by
        have := hist.len_eq
        omega
      have hHead := hist.head
      unfold blockAt? at hHead ⊢
      rw [List.getElem?_append_left hcLen]
      exact hHead
    · -- tail re-filtering
      show (cl.tail ++ [b]).filter (fun x => decide (b.slot + 2 - n ≤ x.slot)) =
        (c ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot)
      rw [List.filter_append, List.filter_append, hist.tail_eq, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro x _
      by_cases hx : b.slot + 2 - n ≤ x.slot
      · have hlo : cl.tipSlot + 2 - n ≤ x.slot := by omega
        simp [hx, hlo]
      · simp [hx]
    · simp [hist.len_eq, hH]
    · -- every block signed
      intro B hB
      rcases List.mem_append.mp hB with hBc | hBb
      · exact hist.signed B hBc
      · rw [List.mem_singleton] at hBb
        exact hBb ▸ hSig
    · -- gen_max
      intro B hB
      rcases List.mem_append.mp hB with hBc | hBb
      · exact le_trans (hist.gen_max B hBc) hLe
      · rw [List.mem_singleton] at hBb; exact hBb ▸ le_refl _
    · -- win_const
      intro B hB hBW
      rcases List.mem_append.mp hB with hBc | hBb
      · have hsand : t.slot / n = B.slot / n :=
          div_sandwich (hSlotsC B hBc) (le_of_lt (htSlot ▸ hS)) hBW
        have hgb : g = b.keyIndex := hWin (by rw [← htSlot]; exact hsand.trans hBW)
        exact (hist.win_const B hBc (by rw [← htSlot]; exact hsand.symm)).trans hgb
      · rw [List.mem_singleton] at hBb; exact hBb ▸ rfl

/-- For `n ≥ 2` the threaded generation is redundant: it is exactly the
generation of the last element of the claim's own tail buffer. So the
"nothing beyond the plain claim" reading of the certificate holds without
restriction for every `n ≥ 2`; only `n = 1` (empty tail) needs `g` as genuine
extra state. -/
theorem groundedCertLock_gen_of_tail {n : Nat} (hn2 : 2 ≤ n) {Signed : Block → Prop}
    {G : Block} {cl : CertClaim} {g : Nat}
    (h : GroundedCertLock n Signed G cl g) :
    ∃ t ∈ cl.tail, t.slot = cl.tipSlot ∧ t.keyIndex = g := by
  obtain ⟨c, hist⟩ := groundedCertLock_history (by omega) h
  obtain ⟨t, hTipEq, htId, htSlot, htHeight, htKey⟩ := hist.tip
  have htmem : t ∈ c := by
    have h' := blockAt_getLast hTipEq
    unfold blockAt? at h'
    exact List.mem_of_getElem? h'
  refine ⟨t, ?_, htSlot, htKey⟩
  rw [hist.tail_eq]
  exact List.mem_filter.mpr ⟨htmem, by rw [decide_eq_true_eq]; omega⟩

/-- **Grounded-lock prefix + validated suffix = full accepted chain.** Mirrors
`groundedCertSched_suffix_history`; the suffix-side rotation check is the
`lockstepFrom` fold, replacing the default certificate's `keyMonoFrom` against
a carried floor snapshot and mode 2's `schedPinned`. -/
theorem groundedCertLock_suffix_history {n : Nat} (hn : 1 ≤ n) {Signed : Block → Prop}
    {G : Block} {cl : CertClaim} {g : Nat}
    (hG : GroundedCertLock n Signed G cl g)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
      u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B) :
    ∃ c : Chain,
      validChain n (c ++ s₁ :: srest) = true ∧
      lockstepOk n (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧
      (∀ B ∈ c ++ s₁ :: srest, Signed B) ∧
      (∃ t ∈ c, t.slot = cl.tipSlot ∧ t.keyIndex = g) ∧
      (∀ B ∈ cl.tail, B ∈ c) := by
  obtain ⟨c, hist⟩ := groundedCertLock_history hn hG
  obtain ⟨t, hTipEq, htId, htSlot, htHeight, htKey⟩ := hist.tip
  have hMat := (validChain_sound hist.valid).2.2.2
  have hStrictC : StrictSlots c := (validChain_sound hist.valid).2.1
  have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
  have hSuffixStrict : StrictSlots (s₁ :: srest) :=
    strictSlots_of_checks (linksOk_isChain hLinks)
  have hSlotsLe : ∀ x ∈ s₁ :: srest, x.slot ≤ sTip.slot := fun x hx =>
    slot_le_tip_of_mem hSuffixStrict hTipS hx
  have hFullDense : ∀ u, u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (c ++ s₁ :: srest) u n := by
    intro u hu
    by_cases hOld : u + n ≤ t.slot + 1
    · calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
        _ ≤ windowCount (c ++ s₁ :: srest) u n :=
            windowCount_mono (List.sublist_append_left ..)
    · have hcount := hDense u (by push_cast; omega) hu
      have heq : windowCount (cl.tail ++ s₁ :: srest) u n =
          windowCount (c ++ s₁ :: srest) u n := by
        rw [windowCount_append, windowCount_append, hist.tail_eq,
          windowCount_filter_low (by omega)]
      omega
  have hLinksT : linksOk (t :: s₁ :: srest) = true := by
    rw [show linksOk (t :: s₁ :: srest) =
      (childOk t s₁ && linksOk (s₁ :: srest)) from rfl, Bool.and_eq_true]
    refine ⟨?_, hLinks⟩
    rw [childOk, decide_eq_true_eq]
    exact ⟨by omega, by omega, by rw [hLink.2.2, htId]⟩
  have hSlotsC : ∀ a ∈ c, a.slot ≤ t.slot := fun a ha =>
    slot_le_tip_of_mem hStrictC hTipEq ha
  have hGtAll : ∀ b' ∈ s₁ :: srest, t.slot < b'.slot := by
    intro b' hb'
    rw [List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · rw [htSlot]; exact hLink.2.1
    · have hlt : s₁.slot < b'.slot := (List.pairwise_cons.mp hSuffixStrict).1 b' hb'
      have hlt2 : cl.tipSlot < s₁.slot := hLink.2.1
      omega
  have hLockFull : lockstepOk n (c ++ s₁ :: srest) = true :=
    lockstepOk_append_of_from hist.lock hSlotsC hist.gen_max
      (fun a ha haeq => hist.win_const a ha (by rw [haeq, htSlot]))
      hGtAll
      hSuffixStrict
      (by rw [htSlot]; exact hLockS)
  have htmem : t ∈ c := by
    have h' := hTipAt
    unfold blockAt? at h'
    exact List.mem_of_getElem? h'
  refine ⟨c, ?_, hLockFull, ?_, hist.len_eq, ?_, ⟨t, htmem, htSlot, htKey⟩, ?_⟩
  · exact validChain_append_suffix hFullDense (s₁ :: srest) c t rfl
      hist.valid hTipEq hLinksT hSlotsLe
  · have hcLen : 0 < c.length := by
      have := hist.len_eq
      omega
    have hHead := hist.head
    unfold blockAt? at hHead ⊢
    rw [List.getElem?_append_left hcLen]
    exact hHead
  · intro B hB
    rcases List.mem_append.mp hB with hBc | hBs
    · exact hist.signed B hBc
    · exact hSigned B hBs
  · intro B hB
    rw [hist.tail_eq] at hB
    exact (List.mem_filter.mp hB).1

-- ===========================================================================
-- (C) Materialisation
-- ===========================================================================

/-- The single materialisation lemma every headline result below starts
from: a `GroundedCertLock` derivation plus a checked suffix yields a full
`SignedChain` accepted by `validSignedChainLock`, with `keyMonoOk` supplied
by `keyMonoOk_of_lockstepOk` (no core validator variant needed). -/
theorem groundedCertLock_signedChain {n : Nat} (hn : 1 ≤ n) {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {G : Block} {cl : CertClaim}
    {g : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
      u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B) :
    ∃ (c : Chain) (sc : SignedChain Sig),
      stripSigs sc = c ++ s₁ :: srest ∧
      validSignedChainLock n ops registry sc = true ∧
      blockAt? (stripSigs sc) 0 = some G ∧
      (stripSigs sc).getLast? = some sTip ∧
      c.length = cl.tipHeight + 1 ∧
      (∃ t ∈ c, t.slot = cl.tipSlot ∧ t.keyIndex = g) ∧
      (∀ B ∈ cl.tail ++ s₁ :: srest, B ∈ stripSigs sc) := by
  obtain ⟨c, hV, hLock, hHead, hLen, hCov, ht, hTail⟩ :=
    groundedCertLock_suffix_history hn hcl hTipS hLink hLinks hDense hLockS hSigned
  obtain ⟨sc, hstrip, hsigs⟩ :=
    exists_signedChain_of_covered (Sig := Sig) (fun B hB => hCov B hB)
  refine ⟨c, sc, hstrip, ?_, ?_, ?_, hLen, ht, ?_⟩
  · rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hsigs, ?_⟩, ?_⟩
    · rw [validChainK, Bool.and_eq_true]
      exact ⟨hstrip ▸ hV, keyMonoOk_of_lockstepOk (hstrip ▸ hLock)⟩
    · exact hstrip ▸ hLock
  · rw [hstrip]; exact hHead
  · rw [hstrip, List.getLast?_append, hTipS]; rfl
  · intro B hB
    rw [hstrip]
    rcases List.mem_append.mp hB with hBtail | hBsuffix
    · exact List.mem_append_left _ (hTail B hBtail)
    · exact List.mem_append_right _ hBsuffix

-- ===========================================================================
-- (D) Headline
-- ===========================================================================

/-- **Certificate-level pinning, single window.** The certificate's own tip
counter equals the roster's counter for its grid window once the suffix
matures that window (witnessed by any suffix block `D` with
`(tipSlot/n)*n + n ≤ D.slot + 1`). The sharp form of "pinning at fold-state
level": the counter the certificate carries is exactly `rosterGen` of its
window as soon as the suffix reaches it. -/
theorem lockstep_cert_gen_pinned
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {cl : CertClaim} {g : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    {s₁ : Block} {srest : Chain} {sTip : Block} (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
      u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ)
    (hMat : ∃ D ∈ s₁ :: srest, (cl.tipSlot / n) * n + n ≤ D.slot + 1) :
    g = rosterGen (cl.tipSlot / n) := by
  obtain ⟨c, sc, hstrip, hValL, hHead, hfullTip, hLen, ⟨t, htmem, htSlot, htKey⟩, _⟩ :=
    groundedCertLock_signedChain hn hcl hTipS hLink hLinks hDense hLockS hSigned
  obtain ⟨D, hDmem, hDmat⟩ := hMat
  have htMem' : t ∈ stripSigs sc := hstrip ▸ List.mem_append_left _ htmem
  have hDMem' : D ∈ stripSigs sc := hstrip ▸ List.mem_append_right _ hDmem
  have hthm := lockstep_declares_rosterGen hn hP hValL hHead ⟨sTip, hfullTip, hRecent⟩
    (cl.tipSlot / n) t htMem' (by rw [htSlot]) ⟨D, hDMem', hDmat⟩
  rw [← htKey]
  exact hthm

/-- **Certificate-level pinning census.** Over every verifier-visible block
(the tail buffer and the suffix), pinning is derived, not checked — the
verifier never sees `rosterGen`. -/
theorem lockstep_cert_declares_rosterGen
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {cl : CertClaim} {g : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    {s₁ : Block} {srest : Chain} {sTip : Block} (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
      u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ) :
    ∀ W, ∀ B ∈ cl.tail ++ s₁ :: srest, B.slot / n = W →
      (∃ D ∈ s₁ :: srest, W * n + n ≤ D.slot + 1) → B.keyIndex = rosterGen W := by
  obtain ⟨c, sc, hstrip, hValL, hHead, hfullTip, hLen, _, hTailMem⟩ :=
    groundedCertLock_signedChain hn hcl hTipS hLink hLinks hDense hLockS hSigned
  intro W B hB hBW hMat
  obtain ⟨D, hDmem, hDmat⟩ := hMat
  have hBMem' : B ∈ stripSigs sc := hTailMem B hB
  have hDMem' : D ∈ stripSigs sc := hstrip ▸ List.mem_append_right _ hDmem
  exact lockstep_declares_rosterGen hn hP hValL hHead ⟨sTip, hfullTip, hRecent⟩ W B hBMem' hBW
    ⟨D, hDMem', hDmat⟩

/-- **Free-cadence lockstep, certificate-level headline.** Mode 3's safety at
the certificate presentation: under the lockstep package alone (chain
independent budget, no `AttestedHistory`), two certificates rooted in one
genesis with recent suffixes agree on the block at the common global index,
`n` deep from both tips. Routes through the existing full-chain transport
(`lockstep_validSignedChainSched`, `LockstepPackage.toPackageA`) and the
existing consumer `sched_deep_block_agreement_of_length` — the same one
`sched_recent_certified_suffix_agreement` closes with — applied once to each
reconstructed recent full chain. -/
theorem lockstep_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {cl cl' : CertClaim} {g g' : Nat}
    (hcl : GroundedCertLock n (SignedDeclared n ops registry) G cl g)
    (hcl' : GroundedCertLock n (SignedDeclared n ops registry) G cl' g')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
      u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLockS : lockstepFrom n cl.tipSlot g (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
      u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hLockS' : lockstepFrom n cl'.tipSlot g' (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  obtain ⟨c, sc, hstrip, hValL, hHead, hfullTip, hLen, _, _⟩ :=
    groundedCertLock_signedChain hn hcl hTipS hLink hLinks hDense hLockS hSigned
  obtain ⟨c', sc', hstrip', hValL', hHead', hfullTip', hLen', _, _⟩ :=
    groundedCertLock_signedChain hn hcl' hTipS' hLink' hLinks' hDense' hLockS' hSigned'
  have hValS : validSignedChainSched n (lagSched n rosterGen) ops registry sc = true :=
    lockstep_validSignedChainSched hn hP hValL hHead ⟨sTip, hfullTip, hRecent⟩
  have hValS' : validSignedChainSched n (lagSched n rosterGen) ops registry sc' = true :=
    lockstep_validSignedChainSched hn hP hValL' hHead' ⟨sTip', hfullTip', hRecent'⟩
  have hBfull : blockAt? (stripSigs sc) (c.length + i) = some B := by
    rw [hstrip]
    unfold blockAt? at hB ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? (stripSigs sc') (c'.length + i') = some B' := by
    rw [hstrip']
    unfold blockAt? at hB' ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB'
  have hkEq : c'.length + i' = c.length + i := by omega
  rw [hkEq] at hB'full
  exact sched_deep_block_agreement_of_length hn
    (schedUnforgeable_of_core hP.toPackageA.unforgeable) hP.hashInj
    (packageA_byzantine_bounded hP.toPackageA) hValS hValS' hHead hHead'
    ⟨sTip, hfullTip, hRecent⟩ ⟨sTip', hfullTip', hRecent'⟩
    (k := c.length + i) hBfull hB'full
    (by rw [hstrip, List.length_append]; omega)
    (by rw [hstrip', List.length_append]; omega)

end MoltPetit.Model
