import MoltPetit.TS.Bridge
import MoltPetit.Model.Liveness

/-!
# MoltPetit — grounded certificates and suffix-level safety

The certificate system (recursive ZK proofs in production) is modelled
*inductively*: a certificate claim is **grounded** when it was built from
the genesis claim by repeatedly folding in one **signed** block, each fold
checking exactly what the protocol demands (link to the current tip, a
verifying producer signature on the new block, density of the windows the
new block matures, counted over the claim's tail buffer). `GroundedCert`
is the derivation; the assumption "verifying certificates are grounded"
is certificate unforgeability — the proof system only ever attests fold
sequences that actually happened. Certificates are thus over *signed
valid chains*, never unsigned ones.

There is **no existential soundness axiom** ("a valid chain exists inside
the certificate"). Instead the prefix chain is *reconstructed from the
derivation* (`groundedCert_history` — a proved lemma, one cons per fold),
and a TypeScript-validated suffix extends it to a full validator-accepted
chain (`grounded_suffix_history`).

Safety is then **derived from the signature primitives** rather than from
a behavioural broadcast-record assumption:

* `SigUnforgeableRecent` — EUF-CMA plus honest signing discipline, over
  a `SigningLog`, **scoped to valid chains with a recent tip**: a
  verifying honest-slot signature on a block of a semantically valid,
  recency-passing chain pins the producer's unique signing call. Rogue signatures the adversary coerces
  during its own slots (even ones stamped for the producer's future
  slots) have no power unless they land inside a valid chain — and the
  only way honest nodes release signatures is `produceBlockCert`'s
  validate-before-ship path, at their true slot;
* `SignedHashInjective` — hash collision resistance over the blocks that
  can occur (signed, or the genesis);
* `ByzantineBounded` — the adversary's slot budget;
* certificate unforgeability (`hUnf`) — verifying certificates carry
  grounded claims.

Honest-slot uniqueness is *proved* from these: every block of a TS-validated certified chain
carries a verifying producer signature (suffix blocks via `sigsOk`,
prefix blocks via the grounding), and a verifying signature for an honest
slot can only come from the designated producer's unique signing call.
The proof-bearing theorem here is `ts_recent_certified_suffix_agreement`;
the headline light-client results built on it live in `Results/Results.lean`.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- Window-count plumbing
-- ---------------------------------------------------------------------------

theorem windowCount_append (a b : Chain) (u len : Nat) :
    windowCount (a ++ b) u len = windowCount a u len + windowCount b u len := by
  simp [windowCount, List.filter_append]

/-- Counting inside a window that starts at or above the filter bound sees
exactly the blocks the filter keeps. -/
theorem windowCount_filter_low {lo u : Nat} (hlo : lo ≤ u) (c : Chain) (len : Nat) :
    windowCount (c.filter fun x => decide (lo ≤ x.slot)) u len = windowCount c u len := by
  rw [windowCount, windowCount, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro x _
  by_cases hx : blockInWindow u len x = true
  · have : decide (lo ≤ x.slot) = true := by
      simp only [blockInWindow, decide_eq_true_eq] at hx
      simp only [decide_eq_true_eq]
      omega
    simp [hx, this]
  · simp only [Bool.not_eq_true] at hx
    simp [hx]

/-- Blocks at or beyond the window's right edge do not affect its count. -/
theorem windowCount_append_high {u len : Nat} {l later : Chain}
    (h : ∀ x ∈ later, u + len ≤ x.slot) :
    windowCount (l ++ later) u len = windowCount l u len := by
  rw [windowCount_append]
  have : windowCount later u len = 0 := by
    rw [windowCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx
    simp only [blockInWindow, decide_eq_true_eq, not_and, not_lt]
    intro _
    exact h x hx
  omega

/-- The blocks after a `linksOk` head occupy strictly later slots. -/
private theorem linksOk_slots_gt {b : Block} {rest : Chain}
    (h : linksOk (b :: rest) = true) : ∀ x ∈ rest, b.slot < x.slot := by
  have hS : StrictSlots (b :: rest) := strictSlots_of_checks (linksOk_isChain h)
  intro x hx
  exact (List.pairwise_cons.mp hS).1 x hx


-- ---------------------------------------------------------------------------
-- Grounded certificate claims
-- ---------------------------------------------------------------------------

/-- The genesis facts hold for every grounded claim (read off the root of
the derivation). -/
theorem groundedCert_facts {n : Nat} {Signed : Block → Prop} {G : Block}
    {cl : CertClaim} (h : GroundedCert n Signed G cl) :
    genesisOk G = true ∧ G.slot = 0 := by
  induction h with
  | genesis hG hS => exact ⟨hG, hS⟩
  | extend _ _ _ _ _ _ _ _ ih => exact ih

/-- What the grounding derivation reconstructs: a validator-accepted prefix
chain matching the claim exactly, every block of which is the genesis or
carries a verifying producer signature. -/
structure GroundedHistory (n : Nat) (Signed : Block → Prop) (G : Block)
    (cl : CertClaim) (c : Chain) : Prop where
  valid   : validChain n c = true
  head    : blockAt? c 0 = some G
  tip     : ∃ t : Block, c.getLast? = some t ∧
              t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight
  tail_eq : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)
  len_eq  : c.length = cl.tipHeight + 1
  signed  : ∀ B ∈ c, B = G ∨ Signed B

/--
**History reconstruction** (proved by induction on the derivation — this
replaces any existential certificate-soundness axiom): a grounded claim's
prefix chain exists, is validator-accepted, starts at `G`, and matches the
claim's tip and tail.
-/
theorem groundedCert_history {n : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {G : Block} {cl : CertClaim}
    (h : GroundedCert n Signed G cl) :
    ∃ c : Chain, GroundedHistory n Signed G cl c := by
  induction h with
  | genesis hG hSlot =>
    refine ⟨[G], ?_, by simp [blockAt?], ⟨G, by simp, rfl, rfl, rfl⟩, rfl, ?_,
      fun B hB => Or.inl (by simpa using hB)⟩
    · -- validChain n [G]
      rw [validChain, show ([G] : Chain).getLast? = some G from rfl,
        Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hG, rfl⟩, ?_⟩
      show maturedWindowsDense n [G] G.slot = true
      rw [maturedWindowsDense, List.all_eq_true]
      intro u hu
      have hu' := List.mem_range.mp hu
      -- with G.slot = 0 a window matures only when n = 1, u = 0
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
  | extend cl b hcl hH hS hP hSig hD ih =>
    obtain ⟨c, hist⟩ := ih
    obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
    have hChild : childOk t b = true := by
      rw [childOk, decide_eq_true_eq]
      exact ⟨by omega, by omega, by rw [hP, htId]⟩
    -- density of all windows matured at b over c ++ [b]
    have hMat := (validChain_sound hist.valid).2.2.2
    have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
    have hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
        windowDense n (c ++ [b]) u = true := by
      intro u hu
      rw [windowDense, decide_eq_true_eq]
      by_cases hOld : u + n ≤ t.slot + 1
      · calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
          _ ≤ windowCount (c ++ [b]) u n :=
              windowCount_mono (List.sublist_append_left c [b])
      · -- newly matured: the claim-level check counted over tail ++ [b]
        have hcount := hD u (by omega) hu
        have heq : windowCount (cl.tail ++ [b]) u n = windowCount (c ++ [b]) u n := by
          rw [windowCount_append, windowCount_append, hist.tail_eq,
            windowCount_filter_low (by omega)]
      -- (filter bound: cl.tipSlot + 2 - n ≤ u from ¬hOld and htSlot)
        omega
    refine ⟨c ++ [b], ?_, ?_, ⟨b, by simp, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
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
    · -- every block is genesis-or-signed
      intro B hB
      rcases List.mem_append.mp hB with hBc | hBb
      · exact hist.signed B hBc
      · rw [List.mem_singleton] at hBb
        exact Or.inr (hBb ▸ hSig)

-- ---------------------------------------------------------------------------
-- Attaching a validated suffix
-- ---------------------------------------------------------------------------

/--
Appending a linked suffix to a validator-accepted chain stays accepted,
provided every window matured at the overall tip is dense in the **full**
chain. Windows matured at intermediate steps count the same blocks as in
the full chain, because later suffix blocks lie beyond their right edge.
-/
theorem validChain_append_suffix {n : Nat} {sTipSlot : Nat}
    {full : Chain}
    (hDense : ∀ u, u + n ≤ sTipSlot + 1 → quorum n ≤ windowCount full u n) :
    ∀ (suffix c : Chain) (t : Block),
      full = c ++ suffix →
      validChain n c = true →
      c.getLast? = some t →
      linksOk (t :: suffix) = true →
      (∀ x ∈ suffix, x.slot ≤ sTipSlot) →
      validChain n full = true := by
  intro suffix
  induction suffix with
  | nil =>
    intro c t hfull hValid _ _ _
    rw [hfull, List.append_nil]
    exact hValid
  | cons b rest ih =>
    intro c t hfull hValid hTipEq hLinks hSlots
    rw [show linksOk (t :: b :: rest) = (childOk t b && linksOk (b :: rest)) from rfl,
      Bool.and_eq_true] at hLinks
    obtain ⟨hChild, hLinksRest⟩ := hLinks
    have hbSlot : b.slot ≤ sTipSlot := hSlots b (List.mem_cons_self ..)
    have hRestGt := linksOk_slots_gt hLinksRest
    -- one-step extension
    have hStep : validChain n (c ++ [b]) = true := by
      apply validChain_append_one hValid hTipEq hChild
      intro u hu
      rw [windowDense, decide_eq_true_eq]
      have hfullCount := hDense u (by omega)
      have heq : windowCount full u n = windowCount (c ++ [b]) u n := by
        rw [hfull, show c ++ b :: rest = (c ++ [b]) ++ rest by simp]
        exact windowCount_append_high fun x hx => by
          have := hRestGt x hx
          omega
      omega
    -- recurse with the grown prefix
    have hLast : (c ++ [b]).getLast? = some b := by
      simp
    exact ih (c ++ [b]) b (by simpa using hfull) hStep hLast
      (by simpa using hLinksRest)
      (fun x hx => hSlots x (List.mem_cons_of_mem _ hx))

/--
**Grounded prefix + validated suffix = full accepted chain.** The suffix
hypotheses are exactly what `ts_validateSuffix_sound` extracts from a
passing TypeScript `validateSuffix` run.
-/
theorem grounded_suffix_history {n : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {G : Block} {cl : CertClaim}
    (hG : GroundedCert n Signed G cl)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n) :
    ∃ c : Chain,
      validChain n (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧
      (∀ B ∈ c, B = G ∨ Signed B) := by
  obtain ⟨c, hist⟩ := groundedCert_history hn hG
  obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
  have hMat := (validChain_sound hist.valid).2.2.2
  have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
  -- suffix slots are bounded by the suffix tip's slot
  have hSuffixStrict : StrictSlots (s₁ :: srest) :=
    strictSlots_of_checks (linksOk_isChain hLinks)
  have hSlotsLe : ∀ x ∈ s₁ :: srest, x.slot ≤ sTip.slot := fun x hx =>
    slot_le_tip_of_mem hSuffixStrict hTipS hx
  have hs₁Tip : s₁.slot ≤ sTip.slot := hSlotsLe s₁ (List.mem_cons_self ..)
  -- density of the full chain on all windows matured at the suffix tip
  have hFullDense : ∀ u, u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (c ++ s₁ :: srest) u n := by
    intro u hu
    by_cases hOld : u + n ≤ t.slot + 1
    · calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
        _ ≤ windowCount (c ++ s₁ :: srest) u n :=
            windowCount_mono (List.sublist_append_left ..)
    · -- newly matured: counted over tail ++ suffix, which agrees with the
      -- full chain on windows starting at or above the tail bound
      have hcount := hDense u (by push_cast; omega) hu
      have heq : windowCount (cl.tail ++ s₁ :: srest) u n =
          windowCount (c ++ s₁ :: srest) u n := by
        rw [windowCount_append, windowCount_append, hist.tail_eq,
          windowCount_filter_low (by omega)]
      omega
  refine ⟨c, ?_, ?_, hist.len_eq, hist.signed⟩
  · -- the suffix links from the prefix tip
    have hLinksT : linksOk (t :: s₁ :: srest) = true := by
      rw [show linksOk (t :: s₁ :: srest) =
        (childOk t s₁ && linksOk (s₁ :: srest)) from rfl, Bool.and_eq_true]
      refine ⟨?_, hLinks⟩
      rw [childOk, decide_eq_true_eq]
      exact ⟨by omega, by omega, by rw [hLink.2.2, htId]⟩
    exact validChain_append_suffix hFullDense (s₁ :: srest) c t rfl
      hist.valid hTipEq hLinksT hSlotsLe
  · have hcLen : 0 < c.length := by
      have := hist.len_eq
      omega
    have hHead := hist.head
    unfold blockAt? at hHead ⊢
    rw [List.getElem?_append_left hcLen]
    exact hHead

-- ---------------------------------------------------------------------------
-- Cryptographic assumptions, signature level
-- ---------------------------------------------------------------------------



-- ---------------------------------------------------------------------------
-- Headline theorem: suffix-level deep agreement
-- ---------------------------------------------------------------------------

/--
**End-to-end, suffix-only safety for the TypeScript implementation,
derived from the signature primitives.**

Assumptions: signatures are unforgeable and honest nodes keep their keys
(`SigUnforgeable` over the `SigningLog` — at most one signing call per
honest slot), block ids are collision-resistant over occurring blocks
(`SignedHashInjective`), the adversary owns at most `⌊(n-1)/3⌋` slots per
`n`-window, and certificates are unforgeable: every verifying certificate
carries a claim **grounded** in the deployment genesis `G`
(`GroundedCert` — whose folds check producer signatures, so certificates
are over *signed* chains). Two nodes hold certified chains whose suffixes
pass the TypeScript `validateSuffix` against their claims and whose
suffix blocks all carry verifying signatures (`hSigned`/`hSigned'` — what
`sigsOk` checks; discharged by `validateCertifiedChain` at the chain
level).

Then the suffixes agree on every block at the same global height that has
at least `n` blocks above it *within each suffix*. No broadcast record
and no behavioural `HonestExecution` assumption appears: honest-slot
uniqueness is **derived** from the signatures the certificate and the
suffix were checked against. No chain is assumed to exist inside any
certificate — the prefixes are reconstructed from the grounding
derivations.

`hB`/`hB'` locate the blocks inside the suffixes (`blockAt?` is list
indexing); the global height of suffix index `i` is `tipHeight + 1 + i`.

The unforgeability assumption is **recency-scoped**
(`SigUnforgeableRecent`): the suffix tips must lie within `Δ` of the
verifier's clock `now` (`hRecent`/`hRecent'`), and only such chains'
honest slots are pinned. `ts_certified_suffix_agreement` recovers the
unscoped form (`now := 0` accepts every chain).
-/
theorem recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {signed : SigningLog}
    {Signed : Block → Prop} {G : Block} {now Δ : Nat}
    (hBudget : ByzantineBounded n bad)
    (hSig : SigUnforgeableRecent n bad Signed signed now Δ)
    (hHash : SignedHashInjective Signed G)
    {cl cl' : CertClaim}
    (hcl  : GroundedCert n Signed G cl)
    (hcl' : GroundedCert n Signed G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned  : ∀ B ∈ s₁ :: srest,  Signed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', Signed B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁ :: srest)   i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  classical
  -- reconstruct the full chains
  obtain ⟨c, hValid, hHead, hLen, hCSig⟩ :=
    grounded_suffix_history hn hcl hTipS hLink hLinks hDense
  obtain ⟨c', hValid', hHead', hLen', hCSig'⟩ :=
    grounded_suffix_history hn hcl' hTipS' hLink' hLinks' hDense'
  set full  : Chain := c  ++ s₁  :: srest  with hfull
  set full' : Chain := c' ++ s₁' :: srest' with hfull'
  have hVS  : ValidChain n full  := validChain_sound hValid
  have hVS' : ValidChain n full' := validChain_sound hValid'
  -- the full chains end at the (recent) suffix tips
  have hfullTip : full.getLast? = some sTip := by
    rw [hfull, List.getLast?_append, hTipS]
    rfl
  have hfullTip' : full'.getLast? = some sTip' := by
    rw [hfull', List.getLast?_append, hTipS']
    rfl
  -- every block of either chain is the genesis or carries a verifying
  -- producer signature
  have hFullSig : ∀ x ∈ full, x = G ∨ Signed x := by
    intro x hx
    rcases List.mem_append.mp hx with hxc | hxs
    · exact hCSig x hxc
    · exact Or.inr (hSigned x hxs)
  have hFullSig' : ∀ x ∈ full', x = G ∨ Signed x := by
    intro x hx
    rcases List.mem_append.mp hx with hxc | hxs
    · exact hCSig' x hxc
    · exact Or.inr (hSigned' x hxs)
  have hG0 : G.slot = 0 := (groundedCert_facts hcl).2
  -- the record of this execution: the blocks of the two chains, by slot
  set record : SlotRecord :=
    (fun s => ((full ++ full').filter fun x => x.slot == s).toFinset) with hrec
  have hmem : ∀ {s : Nat} {x : Block},
      x ∈ record s ↔ (x ∈ full ∨ x ∈ full') ∧ x.slot = s := by
    intro s x
    simp [hrec]
    exact or_and_right.symm
  -- a block of either chain at slot 0 is the genesis (slots ascend strictly)
  have hAtZero : ∀ {fl : Chain}, blockAt? fl 0 = some G → StrictSlots fl →
      ∀ x ∈ fl, x.slot = 0 → x = G := by
    intro fl hflHead hflStrict x hx hx0
    cases fl with
    | nil => simp [blockAt?] at hflHead
    | cons g rest =>
      have hgG : g = G := by simpa [blockAt?] using hflHead
      subst hgG
      rcases List.mem_cons.mp hx with rfl | hxr
      · rfl
      · have := (List.pairwise_cons.mp hflStrict).1 x hxr
        omega
  -- honest-slot uniqueness, derived: a verifying signature for an honest
  -- slot can only come from the designated producer's unique signing call
  have hUniq : HonestSlotsUnique bad record := by
    intro s hs x x' hxr hx'r
    obtain ⟨hxm, hxs⟩ := hmem.mp hxr
    obtain ⟨hx'm, hx's⟩ := hmem.mp hx'r
    have hxsig : x = G ∨ Signed x :=
      hxm.elim (hFullSig x) (hFullSig' x)
    have hx'sig : x' = G ∨ Signed x' :=
      hx'm.elim (hFullSig x') (hFullSig' x')
    rcases hxsig with rfl | hxS
    · rcases hx'sig with rfl | hx'S
      · rfl
      · have hx'0 : x'.slot = 0 := by omega
        exact (hx'm.elim
          (fun hm => hAtZero hHead hVS.2.1 x' hm hx'0)
          (fun hm => hAtZero hHead' hVS'.2.1 x' hm hx'0)).symm
    · rcases hx'sig with rfl | hx'S
      · have hx0 : x.slot = 0 := by omega
        exact hxm.elim
          (fun hm => hAtZero hHead hVS.2.1 x hm hx0)
          (fun hm => hAtZero hHead' hVS'.2.1 x hm hx0)
      · -- both blocks live in valid *recent* chains: the recency-scoped
        -- unforgeability pins each to the producer's unique signing call
        have h1 : signed (producerForSlot n x.slot) x.slot = some x :=
          hxm.elim
            (fun hm => hSig.verified_was_signed hVS hm
              ⟨sTip, hfullTip, hRecent⟩ (by rw [hxs]; exact hs) hxS)
            (fun hm => hSig.verified_was_signed hVS' hm
              ⟨sTip', hfullTip', hRecent'⟩ (by rw [hxs]; exact hs) hxS)
        have h2 : signed (producerForSlot n x'.slot) x'.slot = some x' :=
          hx'm.elim
            (fun hm => hSig.verified_was_signed hVS hm
              ⟨sTip, hfullTip, hRecent⟩ (by rw [hx's]; exact hs) hx'S)
            (fun hm => hSig.verified_was_signed hVS' hm
              ⟨sTip', hfullTip', hRecent'⟩ (by rw [hx's]; exact hs) hx'S)
        rw [hxs] at h1
        rw [hx's] at h2
        rw [h1] at h2
        exact Option.some.inj h2
  -- id injectivity, from collision resistance over occurring blocks
  have hInj : IdInjective record := by
    intro s t x x' hxr hx'r hid
    obtain ⟨hxm, -⟩ := hmem.mp hxr
    obtain ⟨hx'm, -⟩ := hmem.mp hx'r
    exact hHash (hxm.elim (hFullSig x) (hFullSig' x))
      (hx'm.elim (hFullSig x') (hFullSig' x')) hid
  -- both chains live in the record by construction
  have hRec : ChainInRecord record full := by
    intro k x hk
    unfold blockAt? at hk
    exact hmem.mpr ⟨Or.inl (List.mem_of_getElem? hk), rfl⟩
  have hRec' : ChainInRecord record full' := by
    intro k x hk
    unfold blockAt? at hk
    exact hmem.mpr ⟨Or.inr (List.mem_of_getElem? hk), rfl⟩
  -- locate the blocks at their global heights
  have hBfull : blockAt? full (c.length + i) = some B := by
    unfold blockAt? at hB ⊢
    rw [hfull, List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? full' (c'.length + i') = some B' := by
    unfold blockAt? at hB' ⊢
    rw [hfull', List.getElem?_append_right (by omega)]
    simpa using hB'
  -- the global heights agree
  have hkEq : c.length + i = c'.length + i' := by omega
  -- observed blocks n heights above
  have hfullLen : c.length + i + n < full.length := by
    rw [hfull, List.length_append]
    omega
  have hfullLen' : c'.length + i' + n < full'.length := by
    rw [hfull', List.length_append]
    omega
  obtain ⟨E, hE⟩ : ∃ E, blockAt? full ((c.length + i) + n) = some E := by
    unfold blockAt?
    exact ⟨full[(c.length + i) + n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨E', hE'⟩ : ∃ E', blockAt? full' ((c'.length + i') + n) = some E' := by
    unfold blockAt?
    exact ⟨full'[(c'.length + i') + n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  -- shared genesis
  have hGenesis : CommonPrefixUpTo full full' 0 := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    exact ⟨G, hHead, hHead'⟩
  -- apply the height-depth safety theorem
  have := deep_block_agreement_of_height_depth hn hBudget hUniq hInj
    hVS hVS' hRec hRec' hGenesis
    hBfull (hkEq ▸ hB'full) hE (hkEq ▸ hE')
    le_rfl le_rfl
  exact this

/-- **TypeScript instantiation.** The certified-suffix agreement for the
Thales-emitted `validateSuffix`: unpack its structural soundness and take
`Signed := TSSigned n sigOps`. (The shared proof is
`recent_certified_suffix_agreement`.) -/
theorem ts_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {signed : SigningLog}
    {sigOps : MoltPetit.SigOps} {G : Block} {now Δ : Nat}
    (hBudget : ByzantineBounded n bad)
    (hSig : SigUnforgeableRecent n bad (TSSigned n sigOps) signed now Δ)
    (hHash : SignedHashInjective (TSSigned n sigOps) G)
    {cl cl' : CertClaim}
    (hcl  : GroundedCert n (TSSigned n sigOps) G cl)
    (hcl' : GroundedCert n (TSSigned n sigOps) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    (hval  : MoltPetit.validateSuffix n (toTSClaim cl)  (toTSChain (s₁ :: srest))   = true)
    (hval' : MoltPetit.validateSuffix n (toTSClaim cl') (toTSChain (s₁' :: srest')) = true)
    (hSigned  : ∀ B ∈ s₁ :: srest,  TSSigned n sigOps B)
    (hSigned' : ∀ B ∈ s₁' :: srest', TSSigned n sigOps B)
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁ :: srest)   i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' :=
  recent_certified_suffix_agreement hn hBudget hSig hHash hcl hcl' hTipS hTipS'
    (ts_validateSuffix_sound hTipS hval).1 (ts_validateSuffix_sound hTipS hval).2.1
    (ts_validateSuffix_sound hTipS hval).2.2
    (ts_validateSuffix_sound hTipS' hval').1 (ts_validateSuffix_sound hTipS' hval').2.1
    (ts_validateSuffix_sound hTipS' hval').2.2
    hSigned hSigned' hRecent hRecent' hB hB' hHeight hDeep hDeep'

-- ---------------------------------------------------------------------------
-- Height bookkeeping along linked segments
-- ---------------------------------------------------------------------------

/-- Heights along a linked segment ascend by one from the head. -/
theorem linksOk_height_at :
    ∀ {c : Chain} {x : Block}, linksOk (x :: c) = true →
      ∀ {i : Nat} {B : Block}, blockAt? (x :: c) i = some B →
        B.height = x.height + i := by
  intro c
  induction c with
  | nil =>
    intro x _ i B hB
    match i, hB with
    | 0, hB =>
      simp [blockAt?] at hB
      subst hB
      omega
    | i + 1, hB =>
      simp [blockAt?] at hB
  | cons y rest ih =>
    intro x hL i B hB
    rw [show linksOk (x :: y :: rest) = (childOk x y && linksOk (y :: rest)) from rfl,
      Bool.and_eq_true] at hL
    match i, hB with
    | 0, hB =>
      simp [blockAt?] at hB
      subst hB
      omega
    | i + 1, hB =>
      have hB2 : blockAt? (y :: rest) i = some B := by
        simpa [blockAt?] using hB
      have hys := ih hL.2 hB2
      have hC := (childOk_iff.mp hL.1).1
      omega
end MoltPetit.Model
