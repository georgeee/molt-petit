# Rollout planning record (2026-09-04/05)

The planning artifacts for the post-annotation Lean work, produced by a
multi-agent planning run and preserved here because they were expensive to
generate and are the input to the implementation. The working copy lives
outside the repo at `/etheron-pod/rollout-work/`; this is the committed record.

Companion files at the repo root: `docs/rollout/ROLLOUT_NOTES.md` (the pending-paper-change
ledger and the additive-only ground rules) and, once written, `docs/rollout/ROLLOUT_PLAN.md`
(the dependency-ordered rollout).

## What is here

| directory | contents |
|---|---|
| `maps/` | Eight structured maps of the Lean modules and design docs: every definition and theorem of consequence with its exact name, file, line, complete hypothesis list, plus per-group reuse notes and open items. `.json` is the structured form, `.md` the human digest. This is the index the designers worked from. |
| `designs/` | The three completed work-item designs (W1, W2, W5): new files, definitions with signatures, theorem statements with complete hypothesis lists, a proof sketch per theorem naming the lemmas it composes, dependencies, paper changes, size/effort, risks, rejected alternatives, and questions for the owner. |
| `designs-partial/` | Salvage of designer subagents killed mid-run by usage limits. `W*.md` = first run (all died on their first tool call; near-empty). `W*-run2.md` = second run (substantial: full file inventories and verbatim Lean signatures with file:line). `W*-run3.md` = third run. |
| `verdicts/` | Salvage of the six adversarial verifiers (W1/W2/W5 x accuracy/ordering). **All are PARTIAL** — every verifier was killed before returning a verdict, so these record only the claims each had confirmed or doubted so far. No design has a completed verification. |
| `journal-scan.md` | The recovery record: which workflow runs died when, which subagent produced what, and how each result was recovered. |

## Work-item keys

| key | item |
|---|---|
| W1 | Mode 3 (lockstep) at certificate level — **designed** |
| W2 | Mode 1 anchored trailing-5n form at certificate level — **designed** |
| W3a | Timed theft layer for mode 1 (trailing budget from theft rate + reaction) — survey salvaged, not designed |
| W3b | Time-aware signature surface (non-retroactive census) — sketch, not designed |
| W4 | Machine-check the induction over syncs — survey salvaged, not designed |
| W5 | Mode 3 per-generation census (erasure credit) — **designed** |
| W6 | No-back-dating derivation per mode — survey salvaged, not designed |
| W7 | Multi-chain network model for liveness — sketch, not designed |

## State of the plan

Done: the eight module maps; designs for W1, W2, W5; salvage of every
interrupted subagent.

Not done: designs for W3a, W3b, W4, W6, W7; a completed adversarial
verification of any design; the dependency-ordered sequencing; and
`docs/rollout/ROLLOUT_PLAN.md` itself. No Lean has been written and the paper is untouched.

## Reading order for whoever picks this up

1. `docs/rollout/ROLLOUT_NOTES.md` (root) — the ground rules and the paper-change ledger.
2. This file, then `journal-scan.md` for what happened.
3. `designs/W1.md`, `W2.md`, `W5.md` — the three designs.
4. `verdicts/*-partial.md` — what the verifiers had established before dying;
   read before re-verifying, to avoid repeating their checks.
5. `designs-partial/*-run2.md` — the surveys for the five undesigned items;
   read before re-designing, for the same reason.
6. `maps/*.md` — the module index, consulted as needed.
