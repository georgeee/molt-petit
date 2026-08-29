import MoltPetit.Model.Grounded
import MoltPetit.Results.KeyStealingResults

/-!
# MoltPetit — grounded certificates for the index-pinned validator
(the key-rotation light-client wrapper)

The paper's headline is *"a constant-size certificate plus a clock is all a light
client needs"*. `KeyStealingResults.lean` proves the key-stealing safety theorems
over **full** `validSignedChainK'` chains; this module closes the gap to the
certificate presentation, mirroring `Grounded.lean`:

* `GroundedCertK` — the certificate derivation for the **index-pinned** validator.
  Beyond `GroundedCert`'s per-fold checks (link, signature, density over the tail
  buffer) it threads one extra piece of **constant-size state**: the per-producer
  **key floor** `fl : Nat → Nat` (only the `n` producers matter), and gates each
  fold on the monotone rule `fl (producer b) ≤ b.keyIndex`. This is exactly what a
  recursive circuit can check per fold; no history is consulted.
* `groundedCertK_history` — the reconstruction: a grounded-K claim's prefix chain
  exists, passes `validChainK` (structure + density + **monotone index**), starts
  at `G`, matches the claim and the floor snapshot, and every block is `Signed`.
* `inForcePinned_of_validChainK` — on a full chain, the monotone rule already
  implies the `≤`-pin (an earlier same-producer block realises the in-force floor
  and monotonicity lifts it), so reconstruction yields full `validChainK'`
  acceptance with **no additional certificate state** for the pin.
* `keyMonoFrom` — the suffix-side monotone check against the certificate's floor
  snapshot: the locally-checkable form of the monotone rule for a verifier that
  holds only `cert + suffix` (it cannot scan the history for the rotation
  announcement; the floor snapshot carries exactly what it needs).
* `SignedDeclared` / `exists_signedChain_of_covered` — the per-block "carries a
  verifying signature under its **declared** registry version" fact the
  certificate attests, and the reconstruction of a `SignedChain` (with `sigsOk`)
  from blockwise coverage.
* `keyrot_recent_certified_suffix_agreement` — the certificate-level light-client
  safety theorem under the key-stealing adversary: two verifying certificates
  grounded in the same genesis, each extended by a validated recent suffix, agree
  on every block that is `n`-deep in both suffixes. The name reserved by
  `KeyStealingResults.lean` is honoured here: this is the constant-blocks-download
  form.

**Honest accounting.** The corruption budget cannot be stated over verifier-visible
data (it quantifies over the whole execution), so it is assumed over **every
history the certificate could be attesting** (`AttestedHistoryK`): "whatever the
attested history was, the induced rent+theft corruption respects the 1/3 budget".
In a real execution the certificate attests the one real history, so this is the
natural reading of P2-A at the certificate level.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- foldl-max plumbing (local copies; the KeyIndex.lean helpers are private)
-- ---------------------------------------------------------------------------

private theorem foldl_max_le {m a : Nat} {L : List Nat} (ha : a ≤ m)
    (h : ∀ x ∈ L, x ≤ m) : L.foldl max a ≤ m := by
  induction L generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (max_le ha (h x (List.mem_cons_self ..)))
      fun y hy => h y (List.mem_cons_of_mem _ hy)

private theorem le_foldl_max' (a : Nat) (L : List Nat) : a ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left a x) (ih (max a x))

private theorem mem_le_foldl_max' (a : Nat) {x : Nat} {L : List Nat} (hx : x ∈ L) :
    x ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact le_trans (le_max_right a x) (le_foldl_max' (max a x) ys)
    · exact ih (max a y) hxs

/-- Membership form of `block_keyIndex_le_floor`. -/
theorem mem_keyIndex_le_floor (n : Nat) {c : Chain} {B : Block} (hB : B ∈ c) :
    B.keyIndex ≤ keyFloor n c (producerForSlot n B.slot) := by
  unfold keyFloor
  apply mem_le_foldl_max'
  exact List.mem_map.mpr ⟨B, List.mem_filter.mpr ⟨hB, by simp⟩, rfl⟩

/-- One-block floor evolution: appending `b` raises exactly its producer's
floor to `max floor b.keyIndex`. This is the fold-level bookkeeping the
certificate state mirrors. -/
theorem keyFloor_append_one (n : Nat) (c : Chain) (b : Block) (i : Nat) :
    keyFloor n (c ++ [b]) i =
      if producerForSlot n b.slot = i then max (keyFloor n c i) b.keyIndex
      else keyFloor n c i := by
  unfold keyFloor
  rw [List.filter_append, List.map_append, List.foldl_append]
  by_cases hp : producerForSlot n b.slot = i
  · simp [hp]
  · simp [hp]

-- ---------------------------------------------------------------------------
-- The `≤`-pin is free on full monotone chains
-- ---------------------------------------------------------------------------

/-- Two positions of a strict-slots chain are ordered like their slots. -/
private theorem pos_le_of_slot_le {c : Chain} (hS : StrictSlots c)
    {p q : Nat} {X B : Block}
    (hX : blockAt? c p = some X) (hB : blockAt? c q = some B)
    (hslot : X.slot ≤ B.slot) : p ≤ q := by
  rcases Nat.lt_or_ge p q with h | h
  · exact Nat.le_of_lt h
  · rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · exact absurd (strictSlots_lt hS hB hX hlt) (by omega)

/-- **The monotone rule implies the `≤`-pin on a full chain.** Every block in
the confirmed prefix at slot `s` that contributes to the in-force floor is an
earlier same-producer block, and `KeyIndexMonotone` lifts its index to the
block at `s`. So a full-chain validator that checks `keyMonoOk` gets
`inForcePinned` for free — the pin's separate value is *local checkability*
for certificate/suffix verifiers (cf. `keyMonoFrom`). -/
theorem inForcePinned_of_validChainK {n Δconf : Nat} {c : Chain}
    (h : validChainK n c = true) :
    inForcePinned n Δconf c = true := by
  rw [validChainK, Bool.and_eq_true] at h
  obtain ⟨hV, hM⟩ := h
  have hS : StrictSlots c := (validChain_sound hV).2.1
  have hMono : KeyIndexMonotone n c := keyMonoOk_sound hM
  rw [inForcePinned, List.all_eq_true]
  intro b hb
  rw [decide_eq_true_eq]
  unfold inForce keyFloor
  obtain ⟨q, hq⟩ := exists_blockAt_of_mem hb
  apply foldl_max_le (Nat.zero_le _)
  intro x hx
  obtain ⟨X, hXf, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hXconf, hXprod⟩ := List.mem_filter.mp hXf
  obtain ⟨hXmem, hXslot⟩ := List.mem_filter.mp hXconf
  rw [decide_eq_true_eq] at hXprod hXslot
  obtain ⟨p, hp⟩ := exists_blockAt_of_mem hXmem
  have hpq : p ≤ q := pos_le_of_slot_le hS hp hq (by omega)
  exact hMono hp hq hpq (by rw [hXprod])

/-- The index-pinned validator, from the monotone one: the pin is implied. -/
theorem validChainK'_of_validChainK {n Δconf : Nat} {c : Chain}
    (h : validChainK n c = true) :
    validChainK' n Δconf c = true := by
  rw [validChainK', Bool.and_eq_true]
  exact ⟨h, inForcePinned_of_validChainK h⟩

-- ---------------------------------------------------------------------------
-- The suffix-side monotone check against a floor snapshot
-- ---------------------------------------------------------------------------

/-- The **suffix monotone check**: fold the certificate's per-producer floor
snapshot through the suffix, gating each block on `floor (producer) ≤ keyIndex`.
This is the form of the monotone rule a `cert + suffix` verifier can actually
run — it never consults the history behind the certificate. -/
def keyMonoFrom (n : Nat) : (Nat → Nat) → Chain → Bool
  | _, [] => true
  | fl, b :: rest =>
      decide (fl (producerForSlot n b.slot) ≤ b.keyIndex) &&
      keyMonoFrom n
        (fun i => if producerForSlot n b.slot = i then max (fl i) b.keyIndex else fl i)
        rest

/-- Every suffix block clears any floor at-or-below the snapshot it was
checked against (floors only grow along the fold). -/
theorem keyMonoFrom_ge {n : Nat} {fl fl' : Nat → Nat} {s : Chain}
    (hle : ∀ i, fl i ≤ fl' i) (h : keyMonoFrom n fl' s = true) :
    ∀ y ∈ s, fl (producerForSlot n y.slot) ≤ y.keyIndex := by
  induction s generalizing fl fl' with
  | nil => intro y hy; simp at hy
  | cons b rest ih =>
    rw [keyMonoFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, hrest⟩ := h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hyr
    · exact le_trans (hle _) hb
    · refine ih (fl' := fun i =>
        if producerForSlot n b.slot = i then max (fl' i) b.keyIndex else fl' i)
        ?_ hrest y hyr
      intro i
      show fl i ≤ if producerForSlot n b.slot = i then max (fl' i) b.keyIndex else fl' i
      by_cases hp : producerForSlot n b.slot = i
      · rw [if_pos hp]
        exact le_trans (hle i) (le_max_left _ _)
      · rw [if_neg hp]
        exact hle i

/-- The suffix monotone check gives pairwise monotonicity inside the suffix. -/
theorem keyMonoFrom_pairwise {n : Nat} {fl : Nat → Nat} {s : Chain}
    (h : keyMonoFrom n fl s = true) :
    s.Pairwise (fun a b => producerForSlot n a.slot = producerForSlot n b.slot →
      a.keyIndex ≤ b.keyIndex) := by
  induction s generalizing fl with
  | nil => exact List.Pairwise.nil
  | cons b rest ih =>
    rw [keyMonoFrom, Bool.and_eq_true] at h
    obtain ⟨-, hrest⟩ := h
    refine List.Pairwise.cons ?_ (ih hrest)
    intro y hy hprod
    have h2 : (if producerForSlot n b.slot = producerForSlot n y.slot
          then max (fl (producerForSlot n y.slot)) b.keyIndex
          else fl (producerForSlot n y.slot)) ≤ y.keyIndex :=
      keyMonoFrom_ge (fun _ => Nat.le_refl _) hrest y hy
    rw [if_pos hprod] at h2
    exact le_trans (le_max_right _ _) h2

/-- **Assembling the full-chain monotone rule**: a monotone prefix, plus the
suffix checked against the prefix's floor snapshot, is a monotone full chain. -/
theorem keyMonoOk_append_of_from {n : Nat} {c s : Chain}
    (hc : keyMonoOk n c = true)
    (hs : keyMonoFrom n (keyFloor n c) s = true) :
    keyMonoOk n (c ++ s) = true := by
  rw [keyMonoOk_iff_pairwise] at hc ⊢
  rw [List.pairwise_append]
  refine ⟨hc, keyMonoFrom_pairwise hs, ?_⟩
  intro x hx y hy hprod
  have hxfloor : x.keyIndex ≤ keyFloor n c (producerForSlot n x.slot) :=
    mem_keyIndex_le_floor n hx
  have hyfloor := keyMonoFrom_ge (fun _ => Nat.le_refl _) hs y hy
  rw [← hprod] at hyfloor
  exact le_trans hxfloor hyfloor

-- ---------------------------------------------------------------------------
-- Blockwise signature coverage reconstructs a signed chain
-- ---------------------------------------------------------------------------

/-- "Carries a verifying signature under its **declared** registry version" —
the per-block fact the certificate attests (`sigOk`'s content, blockwise).
Strictly stronger than `KeyStealingSigned` (which existentially quantifies the
version): `SignedDeclared → KeyStealingSigned`. -/
def SignedDeclared {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (B : Block) : Prop :=
  ∃ sig : Sig,
    ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true

theorem keyStealingSigned_of_declared {Sig sk pk : Type} {n : Nat}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {B : Block}
    (h : SignedDeclared n ops registry B) : KeyStealingSigned n ops registry B := by
  obtain ⟨sig, hsig⟩ := h
  exact ⟨sig, B.keyIndex, hsig⟩

/-- Blockwise declared-signature coverage reconstructs a **signed chain** whose
stripped blocks are exactly `c` and which passes `sigsOk`. -/
theorem exists_signedChain_of_covered {Sig sk pk : Type} {n : Nat}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {c : Chain}
    (h : ∀ B ∈ c, SignedDeclared n ops registry B) :
    ∃ sc : SignedChain Sig, stripSigs sc = c ∧ sigsOk n ops registry sc = true := by
  induction c with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons b rest ih =>
    obtain ⟨sig, hsig⟩ := h b (List.mem_cons_self ..)
    obtain ⟨sc, hstrip, hok⟩ := ih fun B hB => h B (List.mem_cons_of_mem _ hB)
    refine ⟨⟨b, sig⟩ :: sc, ?_, ?_⟩
    · simp only [stripSigs, List.map_cons] at hstrip ⊢
      rw [hstrip]
    · rw [sigsOk, List.all_cons, Bool.and_eq_true]
      exact ⟨by rw [sigOk]; exact hsig, hok⟩

/-- `keyMonoFrom` only reads the floor pointwise. -/
theorem keyMonoFrom_congr {n : Nat} {f g : Nat → Nat} (hfg : ∀ i, f i = g i) :
    ∀ s : Chain, keyMonoFrom n f s = keyMonoFrom n g s
  | [] => rfl
  | b :: rest => by
    have hrest := keyMonoFrom_congr (n := n)
      (f := fun i => if producerForSlot n b.slot = i then max (f i) b.keyIndex else f i)
      (g := fun i => if producerForSlot n b.slot = i then max (g i) b.keyIndex else g i)
      (fun i => by
        show (if producerForSlot n b.slot = i then max (f i) b.keyIndex else f i)
           = (if producerForSlot n b.slot = i then max (g i) b.keyIndex else g i)
        by_cases hp : producerForSlot n b.slot = i
        · rw [if_pos hp, if_pos hp, hfg i]
        · rw [if_neg hp, if_neg hp, hfg i]) rest
    rw [keyMonoFrom, keyMonoFrom, hfg (producerForSlot n b.slot), hrest]

/-- `keyMonoFrom` reads the floor only at producer indices, which are all
`< n` — so agreement below `n` suffices. -/
theorem keyMonoFrom_congr_lt {n : Nat} (hn : 1 ≤ n) {f g : Nat → Nat}
    (hfg : ∀ i, i < n → f i = g i) :
    ∀ s : Chain, keyMonoFrom n f s = keyMonoFrom n g s
  | [] => rfl
  | b :: rest => by
    have hp : producerForSlot n b.slot < n := by
      unfold producerForSlot
      exact Nat.mod_lt _ hn
    have hrest := keyMonoFrom_congr_lt hn
      (f := fun i => if producerForSlot n b.slot = i then max (f i) b.keyIndex else f i)
      (g := fun i => if producerForSlot n b.slot = i then max (g i) b.keyIndex else g i)
      (fun i hi => by
        show (if producerForSlot n b.slot = i then max (f i) b.keyIndex else f i)
           = (if producerForSlot n b.slot = i then max (g i) b.keyIndex else g i)
        by_cases hpi : producerForSlot n b.slot = i
        · rw [if_pos hpi, if_pos hpi, hfg i hi]
        · rw [if_neg hpi, if_neg hpi, hfg i hi]) rest
    rw [keyMonoFrom, keyMonoFrom, hfg _ hp, hrest]

-- ---------------------------------------------------------------------------
-- Grounded certificates for the index-pinned validator
-- ---------------------------------------------------------------------------

/-- A certificate claim is **grounded-K in genesis `G`** when it arose from the
genesis claim by folding in one signed block at a time, each fold checking the
protocol rules **including the monotone key-index rule** against a threaded
per-producer floor `fl` (constant-size state: only the `n` producers matter).
The fold checks are exactly computable from `(claim, floor, block)` — no chain
is consulted — so this models what a recursive circuit can attest per fold.

Beyond `GroundedCert`: the genesis is itself `Signed` (the signed pinned
validator's `sigsOk` has no genesis exemption), each fold gates
`fl (producer b) ≤ b.keyIndex` (the monotone rule; on the reconstructed full
chain this *implies* the `≤`-pin, `inForcePinned_of_validChainK`), and the
floor is stepped to `max (fl i) b.keyIndex` at the block's producer. -/
inductive GroundedCertK (n : Nat) (Signed : Block → Prop) (G : Block) :
    CertClaim → (Nat → Nat) → Prop
  | genesis :
      genesisOk G = true →
      G.slot = 0 →
      Signed G →
      GroundedCertK n Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
        (fun i => if producerForSlot n G.slot = i then max 0 G.keyIndex else 0)
  | extend (cl : CertClaim) (fl : Nat → Nat) (b : Block) :
      GroundedCertK n Signed G cl fl →
      b.height = cl.tipHeight + 1 →
      cl.tipSlot < b.slot →
      b.prev = some cl.tipId →
      Signed b →
      fl (producerForSlot n b.slot) ≤ b.keyIndex →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCertK n Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }
        (fun i => if producerForSlot n b.slot = i then max (fl i) b.keyIndex else fl i)

/-- What the grounded-K derivation reconstructs: a `validChainK`-accepted
prefix (structure + density + **monotone index**) matching the claim, the
floor snapshot, and with **every** block signed (genesis included). -/
structure GroundedHistoryK (n : Nat) (Signed : Block → Prop) (G : Block)
    (cl : CertClaim) (fl : Nat → Nat) (c : Chain) : Prop where
  valid   : validChainK n c = true
  head    : blockAt? c 0 = some G
  tip     : ∃ t : Block, c.getLast? = some t ∧
              t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight
  tail_eq : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)
  len_eq  : c.length = cl.tipHeight + 1
  signed  : ∀ B ∈ c, Signed B
  floors  : ∀ i, keyFloor n c i = fl i

/-- **History reconstruction for the pinned validator** (mirrors
`groundedCert_history`, plus the monotone rule and the floor bookkeeping). -/
theorem groundedCertK_history {n : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {G : Block} {cl : CertClaim} {fl : Nat → Nat}
    (h : GroundedCertK n Signed G cl fl) :
    ∃ c : Chain, GroundedHistoryK n Signed G cl fl c := by
  induction h with
  | genesis hG hSlot hSig =>
    refine ⟨[G], ?_, by simp [blockAt?], ⟨G, by simp, rfl, rfl, rfl⟩, rfl, ?_,
      fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ hSig, ?_⟩
    · -- validChainK n [G] = validChain n [G] && keyMonoOk n [G]
      rw [validChainK, Bool.and_eq_true]
      refine ⟨?_, rfl⟩
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
    · -- floors of [G]
      intro i
      unfold keyFloor
      by_cases hp : producerForSlot n G.slot = i
      · simp [hp]
      · simp [hp]
  | extend cl fl b hcl hH hS hP hSig hKI hD ih =>
    obtain ⟨c, hist⟩ := ih
    have hcK := hist.valid
    rw [validChainK, Bool.and_eq_true] at hcK
    obtain ⟨hcV, hcM⟩ := hcK
    obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
    have hChild : childOk t b = true := by
      rw [childOk, decide_eq_true_eq]
      exact ⟨by omega, by omega, by rw [hP, htId]⟩
    have hMat := (validChain_sound hcV).2.2.2
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
    refine ⟨c ++ [b], ?_, ?_, ⟨b, by simp, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · -- validChainK n (c ++ [b])
      rw [validChainK, Bool.and_eq_true]
      refine ⟨validChain_append_one hcV hTipEq hChild hAllDense, ?_⟩
      refine keyMonoOk_append_of_from hcM ?_
      rw [keyMonoFrom, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [hist.floors]; exact hKI, rfl⟩
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
    · -- floor bookkeeping
      intro i
      rw [keyFloor_append_one]
      by_cases hp : producerForSlot n b.slot = i
      · rw [if_pos hp, if_pos hp, hist.floors]
      · rw [if_neg hp, if_neg hp, hist.floors]

/-- **Grounded-K prefix + validated suffix = full `validChainK'`-accepted
chain.** Mirrors `grounded_suffix_history`; the extra suffix hypothesis is the
monotone check `keyMonoFrom` against the certificate's floor snapshot — the
locally-checkable form of the monotone rule — and the conclusion is acceptance
by the **index-pinned** validator (the `≤`-pin is implied on the full chain,
`inForcePinned_of_validChainK`), with every block signed. -/
theorem groundedCertK_suffix_history {n : Nat} (Δconf : Nat) (hn : 1 ≤ n)
    {Signed : Block → Prop} {G : Block} {cl : CertClaim} {fl : Nat → Nat}
    (hG : GroundedCertK n Signed G cl fl)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hMono : keyMonoFrom n fl (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B) :
    ∃ c : Chain,
      validChainK' n Δconf (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧
      (∀ B ∈ c ++ s₁ :: srest, Signed B) := by
  obtain ⟨c, hist⟩ := groundedCertK_history hn hG
  have hcK := hist.valid
  rw [validChainK, Bool.and_eq_true] at hcK
  obtain ⟨hcV, hcM⟩ := hcK
  obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
  have hMat := (validChain_sound hcV).2.2.2
  have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
  have hSuffixStrict : StrictSlots (s₁ :: srest) :=
    strictSlots_of_checks (linksOk_isChain hLinks)
  have hSlotsLe : ∀ x ∈ s₁ :: srest, x.slot ≤ sTip.slot := fun x hx =>
    slot_le_tip_of_mem hSuffixStrict hTipS hx
  have hs₁Tip : s₁.slot ≤ sTip.slot := hSlotsLe s₁ (List.mem_cons_self ..)
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
  have hVfull : validChain n (c ++ s₁ :: srest) = true :=
    validChain_append_suffix hFullDense (s₁ :: srest) c t rfl hcV hTipEq hLinksT hSlotsLe
  have hMfull : keyMonoOk n (c ++ s₁ :: srest) = true := by
    refine keyMonoOk_append_of_from hcM ?_
    rw [keyMonoFrom_congr hist.floors]
    exact hMono
  refine ⟨c, ?_, ?_, hist.len_eq, ?_⟩
  · exact validChainK'_of_validChainK (by rw [validChainK, Bool.and_eq_true]; exact ⟨hVfull, hMfull⟩)
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

-- ---------------------------------------------------------------------------
-- The certificate-level light-client theorem under the key-stealing adversary
-- ---------------------------------------------------------------------------

/-- A full chain the certificate `(claim with tipHeight, suffix)` **could be
attesting**: accepted by the index-pinned validator, rooted at `G`, blockwise
declared-signed, and splitting as a `tipHeight+1`-block prefix followed by
exactly the suffix in hand. The corruption budget of the certificate-level
theorem is assumed over *every* such history (in a real execution the
certificate attests the one real history; quantifying over all of them is the
honest way to state an execution-level assumption from verifier-level data,
and only ever *strengthens* the hypothesis). -/
def AttestedHistoryK {Sig sk pk : Type} (n Δconf : Nat) (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (G : Block) (tipHeight : Nat)
    (suffix c : Chain) : Prop :=
  validChainK' n Δconf c = true ∧
  blockAt? c 0 = some G ∧
  (∀ B ∈ c, SignedDeclared n ops registry B) ∧
  ∃ p : Chain, c = p ++ suffix ∧ p.length = tipHeight + 1

/-- **Certificate-level light-client safety under the key-stealing adversary**
(the name reserved by `KeyStealingResults.lean`, honoured: this is the
constant-blocks-download form). Two verifying certificates grounded-K in the
same genesis, each extended by a validated **recent** suffix (structure +
density + the `keyMonoFrom` floor check + blockwise declared signatures), agree
on every block at the same global height that is `n`-deep in **both** suffixes
— under key theft (`Stolen`, no forward security) and `Δconf ≥ 2n`-gated
rotation, with the crypto surface exactly `KeyStealingEUFCMA` + collision
resistance (over the `SignedDeclared` domain — a *subset* of the full-chain
theorems' `KeyStealingSigned` domain, so a strictly **weaker** hash
assumption), and the budget assumed over every attestable history
(`AttestedHistoryK`).

A light client runs this from `O(n)` blocks: the claim (tip data + tail of
`≤ n−1` blocks), the `n`-producer floor snapshot, the suffix, and a clock —
never the chain interior. (`fl` is a `Nat → Nat` in the model, but only the
`n` producer indices are ever read — `producerForSlot n s < n` — so the wire
encoding is an `n`-vector.)

**Wire contract (MANDATORY for any instantiation — read before deploying).**
In this statement the claim `cl` and the floor snapshot `fl` are coupled by the
shared binder of `hcl : GroundedCertK … cl fl` and `hMono : keyMonoFrom n fl …`.
At the wire level that coupling is a contract: the certificate must **carry and
authenticate the pair `(cl, fl)` together** — a TS-level certificate-
unforgeability hypothesis must read
`∀ hc, verify hc = true → ∃ cl fl, claim hc = cl ∧ floors hc = fl ∧
GroundedCertK n Signed G cl fl` (note the plain path's `hUnf` attests only
`cl`; a naive port would leave `fl` unauthenticated). Feeding `keyMonoFrom` an
**unauthenticated** floor is a real attack, not a formality: present a genuine
certificate for `(cl, fl)` but claim `fl* := 0`; a suffix block signed with a
stolen *rotated-out* key `dk(i, j_old)` is `SignedDeclared` (verification is at
the declared version) and passes `keyMonoFrom n fl*` — the verifier accepts a
chain this theorem promises nothing about. The floor snapshot is exactly as
security-critical as the tip hash. -/
theorem keyrot_recent_certified_suffix_agreement
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {cl cl' : CertClaim} {fl fl' : Nat → Nat}
    (hcl  : GroundedCertK n (SignedDeclared n ops registry) G cl  fl)
    (hcl' : GroundedCertK n (SignedDeclared n ops registry) G cl' fl')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest ).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hMono : keyMonoFrom n fl (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hMono' : keyMonoFrom n fl' (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hBudget : ∀ c : Chain,
        AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c →
        ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c))
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁  :: srest ) i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁  :: srest ).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  -- reconstruct the two full pinned chains
  obtain ⟨c, hK, hHead, hLen, hCov⟩ :=
    groundedCertK_suffix_history Δconf hn hcl hTipS hLink hLinks hDense hMono hSigned
  obtain ⟨c', hK', hHead', hLen', hCov'⟩ :=
    groundedCertK_suffix_history Δconf hn hcl' hTipS' hLink' hLinks' hDense' hMono' hSigned'
  -- materialize the signed chains
  obtain ⟨sc, hstrip, hsigs⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => hCov B hB
  obtain ⟨sc', hstrip', hsigs'⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => hCov' B hB
  have hVal : validSignedChainK' n Δconf ops registry sc = true := by
    rw [validSignedChainK', Bool.and_eq_true]
    exact ⟨hsigs, by rw [hstrip]; exact hK⟩
  have hVal' : validSignedChainK' n Δconf ops registry sc' = true := by
    rw [validSignedChainK', Bool.and_eq_true]
    exact ⟨hsigs', by rw [hstrip']; exact hK'⟩
  -- the budget, instantiated at the attested history
  have hBud : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) := by
    rw [hstrip]
    exact hBudget _ ⟨hK, hHead, hCov, c, rfl, hLen⟩
  -- recent tips of the full chains
  have hfullTip : (c ++ s₁ :: srest).getLast? = some sTip := by
    rw [List.getLast?_append, hTipS]
    rfl
  have hfullTip' : (c' ++ s₁' :: srest').getLast? = some sTip' := by
    rw [List.getLast?_append, hTipS']
    rfl
  -- shared genesis
  have hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0 := by
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact ⟨G, by rw [hstrip]; exact hHead, by rw [hstrip']; exact hHead'⟩
  -- locate the blocks at their global heights
  have hBfull : blockAt? (c ++ s₁ :: srest) (c.length + i) = some B := by
    unfold blockAt? at hB ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? (c' ++ s₁' :: srest') (c'.length + i') = some B' := by
    unfold blockAt? at hB' ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB'
  have hkEq : c'.length + i' = c.length + i := by omega
  rw [hkEq] at hB'full
  -- blockwise B = G ∨ SignedDeclared coverage
  have hSig : ∀ b ∈ stripSigs sc, b = G ∨ SignedDeclared n ops registry b := by
    rw [hstrip]; exact fun b hb => Or.inr (hCov b hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b := by
    rw [hstrip']; exact fun b hb => Or.inr (hCov' b hb)
  -- assemble via the full-chain deep-block agreement
  refine keyrot_deep_block_agreement_of_length hn hΔ hEUF hHash hBud hVal hVal'
    hSig hSig'
    ⟨sTip, by rw [hstrip]; exact hfullTip, hRecent⟩
    ⟨sTip', by rw [hstrip']; exact hfullTip', hRecent'⟩
    hGenesis (k := c.length + i)
    (by rw [hstrip]; exact hBfull)
    (by rw [hstrip']; exact hB'full)
    ?_ ?_
  · rw [hstrip, List.length_append]
    omega
  · rw [hstrip', List.length_append]
    omega

end MoltPetit.Model
