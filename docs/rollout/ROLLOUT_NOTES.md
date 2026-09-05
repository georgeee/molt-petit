# Rollout notes — the post-annotation Lean work (started 2026-09-05)

Companion to `docs/rollout/ROLLOUT_PLAN.md`. Ground rules for this arc, from George:

- **The paper is not edited until the Lean lands.** Everything that will change in
  `paper/molt.tex` is logged in §1 below as it becomes known, with the phrase to
  grep for, so the edit can be made in one targeted pass per page later.
- **New Lean only.** New modules, new definitions, new theorems. Nothing existing is
  modified. The only touches permitted to existing files are (a) one import line per
  new module in a root module (`MoltPetit.lean`, `Molt.lean`) and (b) new axiom-guard
  files rather than edits to an existing `Axioms.lean`. Every touch is logged in §2.
- Axiom hygiene as in `CLAUDE.md`: every new headline theorem gets a `#guard_msgs`
  guard; `#print axioms` must yield exactly `[propext, Classical.choice, Quot.sound]`.

Build in this container (see `/etheron-pod/toolchains/lake.sh`):

    /etheron-pod/toolchains/lake.sh build MoltPetit.Model.<NewModule>
    /etheron-pod/toolchains/lake.sh build MoltPetit Molt      # everything + guards

## 1. Paper changes pending (do NOT apply yet)

Keyed by the work item that unlocks them and the annotation that asked. Locations are
given by section and a grep-able phrase (line numbers drift).

| Unlocked by | Annotation | Where in `paper/molt.tex` | What changes |
|---|---|---|---|
| W1 | AN/9a, AN/28, AN/30 | §2 mode 3 paragraph, phrase `currently proved for full chains` | drop the parenthetical's first clause once the certified lockstep theorem exists |
| W1 | AN/28 | §6.3 "A realistic mode-3 deployment", phrase `verifying the full signed chain on wake, since the certificate presentation is future work` | replace with the certificate recipe (fetch certificate + suffix, verify, recency), cite the new Lean name |
| W1 | AN/30 | §6.3 "Honest scope", phrase `Third, mode 3's theorems are about full chains` | delete the third bound |
| W1 | — | §4 Validate, item 5, phrase `future work for mode 3` | cite the new certified lockstep theorem next to the mode 1–2 names |
| W1 | — | §6 intro sentence `keyrot_recent_certified_suffix_agreement and its scheduled twin` | add the lockstep twin |
| W2 | AN/21 | §6.3 mode 1, phrase `carrying the anchored, trailing-$5n$ form to certificates is future work` | replace with the new certified anchored theorem name; the deployment walkthrough's conclusion can then be stated for the certificate client |
| W3a | AN/20, AN/17 | §6.3 mode 1, the paragraphs `Why the cadence cannot simply be enlarged` and `The standing assumption is then` | state the budget in the derived form (theft rate + reaction bound ⇒ trailing budget), cite the derivation; possibly quote the theorem in the one-line form |
| W3a/W3b | AN/24, AN/29 | §6.3 mode 1 `theft \emph{times} inside the signature assumptions`; "Honest scope" first bound `distinguishing thefts before a block's creation` | rewrite according to what lands (W3a: theft times as a derivation layer; W3b: non-retroactive census) |
| W4 | AN/26 | §6.3 mode 1 walkthrough, phrase `argued on paper, not itself machine-checked` and `an informal argument` | cite the machine-checked induction; keep the honest-tip-recency side condition as a stated hypothesis |
| W5 | AN/9b | §2 mode 3 paragraph `erasure's per-generation credit against the budget is designed but not yet formalized`; §6.3 "Honest scope" second bound; mode 3 operator duties `(its budget credit: honest scope below)`; modes table erasure column | state the per-generation budget and cite it |
| W6 | AN/34b | Appendix `What no-back-dating is`; each mode's "What must then be true of the world" list; §Limitations "Named seams" phrase `assumed, not derived from the timed model` | either list no-back-dating per mode as a named operational assumption (text-only variant) or cite the per-mode derivation |
| W7 | AN/31 | §6.4, phrase `a fully multi-chain network model is future work` | only if W7 is done |
| — | AN/27 | none (design question) | a short design note answering the VRF-derived-key idea; not a paper change unless George wants it in Limitations |

Also carried from the annotation round (not Lean-gated, George's call):

- AN/15: the dropped sentence was the paper's only disclosure that the representability
  lemmas are production-side only; Theorem 1's "exposes that height" hypothesis now has
  no stated reason for not being proved away.
- Page count moved 17 → 18 with the annotation edits.
- AN/23: a one-clause cross-reference at the `F_max = S - 4n` formula back to "Two
  readings of the budget clause" would stop the re-read.
- `paper/build.sh` does not run in this container (see `/etheron-pod/toolchains/lake.sh`
  header and the agent memory for the derivation-based PDF build).
- `paper/molt.pdf` on disk is the pre-annotation build.

## 2. Existing Lean touched

Policy: none, except the two kinds of touch listed at the top. Log every one here.

| Date | File | Touch | Why |
|---|---|---|---|
| — | — | — | — |

## 3. New Lean added

| Date | Module | Headline names | Guard file | Status |
|---|---|---|---|---|
| — | — | — | — | — |

## 4. Recovery record

The planning workflow's first run died on a usage limit; recovery notes and the
recorded module maps live outside the repo at `/etheron-pod/rollout-work/`
(`journal-scan.md`, `maps/`, `designs-partial/`).
