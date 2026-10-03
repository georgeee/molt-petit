# Pass 9 spec: Theorem 1 and recency rework (paper)

This spec is reviewer-owned, and the reviewer decides every point in it. You
edit `paper/molt.tex` only. Do not change any Lean file. Each paper claim must
match its Lean statement exactly; if a sentence cannot be backed by a Lean
theorem, delete it rather than soften it.

## Decisions (do not re-open)

1. **Theorem 1 (`thm:lc`, §6.1) becomes the timed theorem**
   `Molt.timed_light_client_safety` (Molt/Results.lean). Its title cites that
   name. Restate it with exactly these hypotheses, in prose, one per Lean
   argument:
   - `n ≥ 1`, and a deployment genesis `G`.
   - A timed execution (`TimedExecution`). Signing happens at real slots, and
     at a bad real slot the producer's key signs arbitrarily many blocks with
     any stamp in its residue class (`key_match`). An honest real slot signs
     only its own current block (`honest_stamp`), and at most once
     (`honest_once`). A block is signed only once its parent is available
     (`chain_order`). Collision resistance holds over the blocks that occur
     (`id_inj`).
   - The fault budget over **real** slots (`ByzantineBounded`).
   - The verifier is at real slot `R`. Every producer signature it accepts was
     produced at some real slot no later than `R` (`hbridge`): EUF-CMA plus
     causality, meaning no signature from the future.
   - There are two presentations. Each is a grounded certificate claim
     (`GroundedCert`) plus a suffix that passes the validator: link, links,
     density and signatures (`hLink`, `hLinks`, `hDense`, `hSigned`).
   - Both tips are recent in real time: `R ≤ tip.slot + n`.
   - **Conclusion:** take any histories the two groundings attest
     (`GroundedHistory`). The two full chains (attested history ++ suffix) agree
     at every height `h` with `h + n` below both lengths. Equivalently, they
     agree on everything at least `n` blocks below the lower tip.

   **Delete** the "exposes that height" clause and the paragraph after the
   theorem that argues it away ("The ``exposes that height'' hypothesis is a
   restriction of presentation …"). Keep the two remarks (produced chains;
   uniqueness derived, not assumed), rewritten so they cite the timed model.
   The proof idea is now: availability by real slot `R`, plus the
   half-speed forging bound, plus the counting argument.

2. **The untimed `Molt.light_client_safety` is demoted.** Mention it in one
   short remark after Theorem 1: it is the same conclusion in the untimed
   model, but it assumes the residue `SigUnforgeableRecent` directly and keeps
   the exposure hypothesis. It is not the headline.

3. **Assumptions (§5) are rewritten so the headline needs only the following:**
   - **Fault budget** (`ass:budget`): per real slot. In Lean,
     `ByzantineBounded` over the timed execution's real slots. Keep the
     per-slot (not per-participant) wording.
   - **Signatures** (`ass:sig`): keep (a) custody and (b) EUF-CMA. Replace (c),
     the `SigUnforgeableRecent` residue, with the timed formal content:
     `TimedExecution`'s `key_match`, `honest_stamp` and `honest_once`, plus
     the bridge `hbridge`. `chain_order` is the id-formation contract
     (§3). Delete the paragraph "The recency scoping in (c) is essential …",
     and replace it with two sentences: the adversary may hold coerced
     signatures stamped for any future slot of the coerced producer, and the
     model gives it exactly that power. Keep the key-rotation forward note
     unchanged.
   - **Hash** (`ass:hash`): for the headline, the Lean content is
     `TimedExecution.id_inj` (over `SignedEver`). Keep the rotation sentence
     about `SignedHashInjective` / `SignedDeclared` for the rotation results.
   - **Certificate grounding** (`ass:cert`): unchanged.
   - **Clock** (`ass:clock`), new text: the verifier reads local time `now`,
     and real time is at most `δ` slots ahead of it (`R ≤ now + δ`). The
     verifier accepts a tip when `now ≤ tip.slot + b`. Theorem 1 applies
     whenever `b + δ ≤ n`, because `R ≤ now + δ ≤ tip.slot + b + δ ≤ tip.slot + n`.
     Here δ covers clock skew and propagation combined. Example: `b = n/2`
     leaves `n/2` slots, about 14 s at the prototype's parameters, for skew
     plus propagation. Make every place that states the recency rule (§4 rule
     text, `sec:verifier-rule`, the abstract's "tip is recent", the §5 intro
     sentence at "err by up to ≈ n/2") consistent with the bar `b` and
     `b + δ ≤ n`.

4. **Unproven numbers go.** Delete every claim that the recency rule is safe
   out to ≈ 3/2·n staleness, that there is a ≈ 50% margin, or that it
   "absorbs ≈ n/2 slots of skew" beyond what `b + δ ≤ n` gives. That covers §5
   Clock and the §6.2 paragraph "This is what makes the verifier's recency rule
   sound, with numbers …". Replace that paragraph with: Theorem 2 is the engine
   of Theorem 1. A fork meeting the real-time recency bar has had too little
   real time to forge an `n`-deep ancestor, and Theorem 1 is the
   machine-checked statement of exactly that at staleness `n`. Keep the
   "patient adversary grows a fork at half speed and falls behind real time"
   sentence. Delete "This is also why Assumption (c) is derived rather than
   primitive …" and point to the appendix instead (item 5).

5. **Appendix A** (`app:timed-uniq`) is reframed as "The untimed residue,
   derived". It is the route by which the *untimed* `light_client_safety`'s
   residue `SigUnforgeableRecent` follows from EUF-CMA plus `NoBackdate`.
   Add one opening sentence: the headline Theorem 1 does not use this residue
   or `NoBackdate`. Keep the rest of the appendix's content accurate. Retitle
   it if needed, and fix the cross-references.

6. **Abstract:** keep it to one paragraph. Replace "which makes the verifier's
   recency check a load-bearing safety ingredient" with a statement that
   light-client safety is proved directly in a timed model, against an
   adversary that harvests coerced signatures stamped for any slot, so the
   recency check is a machine-checked safety ingredient. Keep everything
   else.

7. **Sweep:** grep the paper for `exposes`, `SigUnforgeableRecent`,
   `NoBackdate`, `n/2`, `tfrac{3}{2}`, `50\%`, `light\_client\_safety` and
   `recency`, and make each hit consistent with items 1 to 6. That includes the
   intro, the results overview and table, Limitations, and any list of Lean
   names. In key-rotation sections, `SigUnforgeableRecent`-style residues of
   the *rotation* results stay as they are; Passes 10 to 13 handle those.

## Done when

- `bash tools/check.sh` prints `check: all green` (the paper builds).
- `grep -n 'exposes that height\|tfrac{3}{2}\|50\\\\%' paper/molt.tex`
  returns nothing.
- `grep -c 'timed\\\\_light\\\\_client\\\\_safety' paper/molt.tex` is at least 1, and
  it appears in the title of `thm:lc`.
- Pass 9 is ticked in `docs/PUBLISH_PREP_STATUS.md`, and the progress is
  recorded in `docs/PAPER_TIMED_REWORK_PROGRESS.md`.

Commit small steps on publish-prep. Never push, never switch branches.
