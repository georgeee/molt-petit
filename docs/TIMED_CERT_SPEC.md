# Pass 8 spec: certified-history timed safety

Reviewer-owned. Pinned statement: `MoltPetit.Model.timed_certified_agreement` in
`MoltPetit/Model/TimedSafetyCert.lean`. Its exact type and axiom set are pinned by
`Molt/AxiomsTimedSafetyCert.lean`, which you must not edit. Replace the `sorry`;
do not change the statement, and do not add hypotheses, axioms or `sorry`.

## What the theorem says

A light client holds a grounded certificate claim `cl` plus a validated suffix
`s₁ :: srest`, and verifies at real slot `R` with `R ≤ sTip.slot + n`. Take any
history `c` the grounding attests (`GroundedHistory`), and the same for a second
presentation (`cl'`, `c'`, `s₁' :: srest'`). The two full chains agree at every
height `h` that is more than `n` below both tips. No "exposure" hypothesis is
needed. This removes Theorem 1's "exposes that height" clause.

## Proof plan

Step 1, mechanical refactor in `MoltPetit/Model/Grounded.lean`. Add
`grounded_suffix_history_of`. It has the same hypotheses as
`grounded_suffix_history`, but it takes a given `hist : GroundedHistory n Signed G cl c`
instead of obtaining `c` from `groundedCert_history`, and it concludes
`validChain n (c ++ s₁ :: srest) = true`. The existing proof only uses `hist`
after line ~280, so move that body here. Then re-prove `grounded_suffix_history`
from it in two lines (`obtain ⟨c, hist⟩ := groundedCert_history hn hG`). Do not
change `grounded_suffix_history`'s statement.

Step 2. In the new theorem, for each side:
- Get `ValidChain n (c ++ s₁ :: srest)` from Step 1 and `validChain_sound`
  (Soundness.lean:130).
- Get the head: `blockAt? (c ++ …) 0 = some G`, from `hc.head` and `c ≠ []`
  (`hc.len_eq`).
- Get the tip: `(c ++ s₁ :: srest).getLast? = some sTip`, from `hTipS`.
- Get availability: `∀ B ∈ c ++ s₁ :: srest, AvailableAt log G B R`. Use `hc.signed`
  for the `c` part and `hSigned` for the suffix, then `hbridge` (`AvailableAt` is
  `B = G ∨ ∃ r ≤ R, B ∈ log r`).

Step 3. WLOG (by `le_total` on the lengths, with symmetry), let `L` be the
shorter full chain's length. `hDeep` gives `n < L`.
`timed_tip_ancestor_agreement` gives agreement at index `L - 1 - n`. Then
`same_block_same_prefix_timed` (TimedSafety.lean:474), or the index-wise prefix
lemma next to it, gives agreement at every `h ≤ L - 1 - n`. That holds because
`h + n < L`.

## Paper-facing alias

Add `Molt.timed_light_client_safety` in a Molt file (beside
`Molt.light_client_safety`): a one-line `theorem … := MoltPetit.Model.timed_certified_agreement …`
with the identical statement. Also add a `#print axioms` guard to `Molt/Axioms.lean`,
in the same style as the existing ones, expecting `[propext, Classical.choice, Quot.sound]`.

## Done when

`bash tools/check.sh` prints `check: all green` (the guard compiles, so there is
no sorryAx). Keep lines ≤ 100 characters. Keep each docstring. Commit small steps on publish-prep.
Record progress in `docs/TIMED_CERT_PROGRESS.md`.
