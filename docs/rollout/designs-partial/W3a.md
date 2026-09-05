# W3a salvage -- timed theft layer for mode 1 deriving the trailing budget

## Header

- Agent id: `ad74e6582be902c9b`
- Transcript: `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_8cd2c3cc-ea5/agent-ad74e6582be902c9b.jsonl`
- Work item: **W3a** (confirmed from content; matches the guess)
- Repository / cwd: `/etheron-pod/mini-consensus-lean` (gitBranch `HEAD`, i.e. detached)
- Model: claude-fable-5-1, effort high, started 2026-09-04T21:14:55Z
- Killed: 2026-09-04T21:14:58Z by `429 rate_limit` -- "You've hit your session limit · resets 1am (UTC)" (rateLimitType `five_hour`, overage disabled at org level)
- Transcript lines seen: offsets 5, 6, 7, 8 (4 lines). Offset 9 is past end of file. Offsets 0-4 (prompt + harness attachments) not read, per salvage protocol.
- Transcript lines skipped as too large: none.

### Evidence for W3a

1. First assistant sentence (line 5): *"I'll start by confirming the signatures that this design depends on, beginning with the mode-2 timed layer to mirror and the mode-1 budget consumers."*
   - "mode-2 timed layer to mirror" = `MoltPetit/Model/KeyStealingScheduleTimed.lean`; W3a is a timed theft layer for mode 1 mirrored on the mode-2 one.
   - "mode-1 budget consumers" = the trailing budget that W3a is meant to derive.
2. The only tool call (line 6) sizes exactly the files a timed-layer-for-mode-1 design would need: `KeyStealingScheduleTimed.lean`, `KeyStealingBudget.lean`, `KeyStealing.lean`, `KeyRotation.lean`, `Molt/ClientRule.lean`, `Molt/MaxSync.lean`, `KeyStealingHorizon.lean`, `KeyStealingHorizonCore.lean`, `KeyStealingLongRange.lean`.

No other work item (W1/W2/W4-W7/W3b) mentions a timed layer plus budget consumers.

## Extent of the salvage (read this first)

The subagent was killed **three seconds** into its run, after **one** Bash command. It never opened a Lean file, never read a declaration, never wrote a definition or theorem statement, never drafted a StructuredOutput, and never recorded a decision or rejected alternative. Everything below is the complete content of the transcript; there is nothing more to recover. A fresh designer starts essentially from zero, with only the file inventory below already confirmed.

## 1. Files examined

Only one tool call was made (line 6, `Bash`):

```
git log --oneline -3 && git status --short | head && wc -l \
  MoltPetit/Model/KeyStealingScheduleTimed.lean \
  MoltPetit/Model/KeyStealingBudget.lean \
  MoltPetit/Model/KeyStealing.lean \
  MoltPetit/Model/KeyRotation.lean \
  Molt/ClientRule.lean \
  Molt/MaxSync.lean \
  MoltPetit/Model/KeyStealingHorizon.lean \
  MoltPetit/Model/KeyStealingHorizonCore.lean \
  MoltPetit/Model/KeyStealingLongRange.lean
```

Description given by the subagent: "Show repo state and file sizes". Why (from the assistant text at line 5): to begin confirming the signatures the design depends on -- the mode-2 timed layer it intends to mirror and the mode-1 budget consumers.

No file contents were read (no `Read`, `Grep`, `cat`, or `sed` calls). No line ranges were examined.

## 2. Verified facts about the repository

All from the tool result at line 7 (run in `/etheron-pod/mini-consensus-lean`, 2026-09-04T21:14:58Z):

### Git state

| Commit | Subject |
|---|---|
| `8b8b766` (HEAD) | paper2 p16: appendix -- recency window, no-back-dating scope (AN/33, AN/34) |
| `60bd4bd` | paper2 p13: trim the prover-cost aside (AN/32) |
| `4d950bb` | paper2 p11: drop the redundant length clause (AN/25) |

`git status --short | head` printed nothing: the working tree was clean at that moment.

### File inventory (all nine files exist; `wc -l` line counts)

| File | Lines |
|---|---|
| `MoltPetit/Model/KeyStealingScheduleTimed.lean` | 423 |
| `MoltPetit/Model/KeyStealingBudget.lean` | 125 |
| `MoltPetit/Model/KeyStealing.lean` | 134 |
| `MoltPetit/Model/KeyRotation.lean` | 445 |
| `Molt/ClientRule.lean` | 341 |
| `Molt/MaxSync.lean` | 230 |
| `MoltPetit/Model/KeyStealingHorizon.lean` | 339 |
| `MoltPetit/Model/KeyStealingHorizonCore.lean` | 365 |
| `MoltPetit/Model/KeyStealingLongRange.lean` | 81 |
| **Total** | **2483** |

### Facts about Lean declarations

**None.** No declaration names, hypothesis lists, file:line locations, or gotchas were established. The subagent did not get as far as opening any of the files above.

## 3. Design direction (partial -- intent only)

The only statement of direction is the opening sentence:

> "I'll start by confirming the signatures that this design depends on, beginning with the mode-2 timed layer to mirror and the mode-1 budget consumers."

What can be read off this, marked as the subagent's stated intent rather than a concluded design:

- **Mirroring strategy:** the mode-1 timed theft layer is to be modelled on the existing mode-2 timed layer (`MoltPetit/Model/KeyStealingScheduleTimed.lean`, 423 lines) -- i.e. the mode-2 file's structure is the template.
- **Target:** the derived object is the mode-1 trailing budget; the "consumers" of that budget (presumably in `KeyStealingBudget.lean` and the Molt client files `Molt/ClientRule.lean`, `Molt/MaxSync.lean`) are what the timed layer must feed.
- **Dependency surface the subagent intended to survey** (inferred from the wc list, in the order given): `KeyStealingScheduleTimed` (mode-2 timed layer), `KeyStealingBudget` (budget), `KeyStealing` (base), `KeyRotation` (rotation model), `Molt/ClientRule` and `Molt/MaxSync` (mode-1 client side), `KeyStealingHorizon` / `KeyStealingHorizonCore` (horizon layer), `KeyStealingLongRange` (long-range).

Not reached: planned files, definitions, theorem statements, proof sketches, lemmas to compose, dependencies on other work items (e.g. W2 / W4), effort estimates.

## 4. Decisions and rejected alternatives

None recorded.

## 5. Partial structured output

None. No StructuredOutput call was made and no JSON was drafted in assistant text.

## 6. Open questions

The subagent raised none explicitly. Questions implied by where it stopped (for the next designer, not the subagent's own):

- What are the exact signatures in `KeyStealingScheduleTimed.lean` (the mode-2 timed layer) that the mode-1 layer must mirror?
- Which declarations in `KeyStealingBudget.lean`, `Molt/ClientRule.lean`, and `Molt/MaxSync.lean` consume the mode-1 trailing budget, and in what form (hypothesis shape) do they expect it?
- How do `KeyStealingHorizon(Core).lean` and `KeyStealingLongRange.lean` relate to the budget -- are they inputs to the timed layer or consumers of it?
- Interaction with W2 (mode-1 anchored trailing-5n form at certificate level): does W3a supply the budget W2 assumes?

## Where the salvaged design stopped

At the very first step: "confirm the signatures this design depends on". The repo-state / file-size survey succeeded; the next action would have been reading `KeyStealingScheduleTimed.lean` and `KeyStealingBudget.lean`. Nothing after that exists.
