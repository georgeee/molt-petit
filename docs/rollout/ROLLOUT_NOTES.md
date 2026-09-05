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

## 1b. Answers to the question-annotations (2026-09-04, not yet in the paper)

These annotations asked questions rather than requesting edits. The answers were
given to George in chat; recorded here so they are not re-derived.

**AN/23 — "would it follow from rho+T < f for F=n?"** Yes, and the paper already
says so three paragraphs above where the question was asked: a deployment keeping
rho+T within f on every window from genesis satisfies the hypothesis outright, and
`client_refresh_rule` at `A :=` genesis recovers the lifetime statement exactly.
`F_max = S - 4n` at `S = 5n` gives `F = n`, the sync rule. The point of the
trailing form is that it demands strictly *less*. A one-clause cross-reference at
the `F_max` formula would prevent the re-read (listed in the carried items below).

**AN/21 — "carrying the anchored trailing-5n form to certificates: what will it
buy us?"** Today the certified mode-1 theorem holds only under the global
all-window budget, i.e. the lifetime assumption the paper argues no deployment can
defend under key theft. So the constant-size client — the client the paper is
written for — does not get the two-minute budget; only a full-chain client does.
Closing it removes a gap between the headline claim and the certified form. This
is work item **W2**, now designed.

**AN/29 — "what would the theft-timing work buy; necessary or vain curiosity?"**
Not vain, not necessary. It removes the retroactive census, which is the one thing
forcing the n-slot cadence: with theft times a theft charges only windows at or
after it, so the budget stops being a per-stretch total and becomes closer to a
concurrency bound — far easier for an operator to attest — and `F_max` rises. It
is the single highest-leverage relaxation available, and it is the same machinery
as **W3a** (derivation layer) and **W3b** (non-retroactive census).

**AN/27 — the VRF-derived-next-key idea.** George's own diagnosis is right and it
is fatal: if `SK_{j+1} = KDF(SK_j, seed)` then a thief of `SK_j` owns every future
generation, so rotation buys nothing and healing — which mode 1's entire budget
rests on — disappears. A public seed does not help; the secret input is `SK_j`.
The nearest workable neighbour is forward security (evolve, then erase `SK_j`),
which fixes back-dating but not forward theft, and the paper already cites it in
the long-range-residual paragraph. Capping forward theft requires that the cold
root not be derivable from the live key — which is the current design. If the
motivation is fewer cold-root ceremonies, the dial that actually moves is the era
length R in mode 2. This is a design judgement, not a proved statement; it is not
a paper change unless George wants it in Limitations.

## 2. Existing Lean touched

Policy: none, except the two kinds of touch listed at the top. Log every one here.

| Date | File | Touch | Why |
|---|---|---|---|
| — | — | — | — |

## 3. New Lean added

| Date | Module | Headline names | Guard file | Status |
|---|---|---|---|---|
| — | — | — | — | — |

## 3b. Provisional effort and ordering (NOT yet verified)

The sequencing agent never ran, so this is the planner's provisional reading, not
a checked result. Effort for W1/W2/W5 is each design's own estimate; the rest are
rough. Nothing here should be treated as settled until a sequencing pass runs
over the verified designs.

| item | effort | note |
|---|---|---|
| W2 | 1-2 sessions | cheapest of the three designed; no dependencies; adds a generic-Signed anchored engine that W4 can also use |
| W1 | 2-3 sessions | self-contained; consumes the lockstep package opaquely, so W5 does not invalidate it |
| W4 | 1-2 sessions | abstract over the per-sync step, so it instantiates at both the full-chain and (later) certificate presentations |
| W3a | 1-2 sessions | mirrors the mode-2 timed layer; the survey is salvaged |
| W5 | 3-4 sessions | the deep one (the D1-prime-full census); do after W1 |
| W6 | text-only, or 1-2 sessions | a text-only variant exists and may be the right call |
| W3b | 4-6 sessions | subsumes W3a's relaxation; never before W3a |
| W7 | 4-6 sessions | lowest priority; buys a liveness hypothesis discharge, not safety |

Two loop risks the designs flag and a sequencer must settle: who owns the shared
timed structure carrying theft times (W3a vs W5 vs W6), and whether W3b's surface
change would force any W3a result to be restated.

## 4. Recovery record

The planning workflow's first run died on a usage limit; recovery notes and the
recorded module maps live outside the repo at `/etheron-pod/rollout-work/`
(`journal-scan.md`, `maps/`, `designs-partial/`).
