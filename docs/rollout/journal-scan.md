# Recovery record — workflow `molt-rollout-understand` (run wf_8cd2c3cc-ea5), 2026-09-05

First run died in the Design phase: every designer hit "You've hit your session limit · resets 1am (UTC)". Readers (8/8) completed and are cached in the workflow journal; their outputs are re-recorded under `maps/` by the resumed run. Five designers ran (~320K tokens each) before failing; three never started (immediate 429). Sequencer ran with an empty design list.

Harness notes (not worked around, reported): `grant_read` on the journal was refused because the transcript directory's real path resolves under `/state/`; `grant_read` on the `/tmp/claude-1007/...` result file reported success but the executor still got Permission denied. All recovery was done in-process (Read tool) via subagents.

## Journal (36 lines; result records are too large for a single Read call)

| line | type | agentId | note |
|---|---|---|---|
| 1-2 | started | acf31dddfaa8e3cb3 | reader (duplicate start record) |
| 3 | started | a5dd4fc46312daee4 | reader |
| 4 | started | a7085fef81cf40c09 | reader |
| 5 | started | a600689c7f4abf77c | reader |
| 6 | started | ae17c47d40b3f1252 | reader |
| 7 | started | a20cd86ceb0ef00d4 | reader |
| 8 | started | a4dbb20eb80b7d18f | reader |
| 9 | result | (too large) | reader result |
| 10 | started | ab5b8b5d3a55a6bc2 | reader (design-docs, started ~7 min after the others) |
| 11-15 | result | (too large) | reader results |
| 16 | result | acf31dddfaa8e3cb3 | reader result (mode2-horizon-timed), readable |
| 17 | result | (too large) | reader result |
| 18 | started | a71b5bdcf1ae9fdee | designer |
| 19 | started | a8b6d9f655e212aa8 | designer |
| 20 | started | ad74e6582be902c9b | designer |
| 21 | started | ab9cd6418be45fd3c | designer |
| 22 | started | ab9a3fba02babc59e | designer |
| 23 | started | af7c7c333c74c9a27 | designer (never ran: immediate 429) |
| 24 | failed | af7c7c333c74c9a27 | |
| 25 | failed | a8b6d9f655e212aa8 | |
| 26 | failed | ab9a3fba02babc59e | |
| 27 | started | afdc46c1ebf56d0a7 | designer (never ran: immediate 429) |
| 28 | failed | afdc46c1ebf56d0a7 | |
| 29 | started | a6cc5f1e9c4e4f24c | designer (never ran: immediate 429) |
| 30 | failed | ad74e6582be902c9b | |
| 31 | failed | a6cc5f1e9c4e4f24c | |
| 32 | failed | a71b5bdcf1ae9fdee | |
| 33 | failed | ab9cd6418be45fd3c | |
| 34 | started | a2a831b0896558558 | sequencer (received an empty design list) |
| 35 | failed | a2a831b0896558558 | |
| 36 | started | abfb481b7af312d42 | map-writer from the first (serial) resume, stopped |

## Agents

| agentId | role | evidence |
|---|---|---|
| acf31dddfaa8e3cb3 | reader:mode2-horizon-timed | result group "horizon-and-timed-theft-layer" |
| a5dd4fc46312daee4 | reader:results-molt | prompt file list |
| a7085fef81cf40c09 | reader:timed-core-liveness | prompt file list |
| a600689c7f4abf77c | reader:mode3-lockstep | prompt file list |
| ae17c47d40b3f1252 | reader:mode2-cert-budget | prompt file list |
| a20cd86ceb0ef00d4 | reader:mode1-chain | prompt file list |
| a4dbb20eb80b7d18f | reader:core-grounded-cert1 | prompt file list |
| ab5b8b5d3a55a6bc2 | reader:design-docs | prompt file list |
| a8b6d9f655e212aa8 | designer, W1 (inferred) | "beginning with the lockstep module and the scheduled certificate" |
| ad74e6582be902c9b | designer, W3a (inferred) | "beginning with the mode-2 timed layer to mirror and the mode-1 budget consumers" |
| ab9cd6418be45fd3c | designer, W5 (inferred) | "beginning with the lockstep module and the design note's audit section" |
| a71b5bdcf1ae9fdee | designer, W2 or W4 | "confirming the signatures this design depends on, then check for any plan document naming the other work items" |
| ab9a3fba02babc59e | designer, W4 or W2 | "confirming the exact signatures of the theorems this work item composes" |
| af7c7c333c74c9a27, afdc46c1ebf56d0a7, a6cc5f1e9c4e4f24c | designers, never ran | line 5 of each transcript is the 429 rate-limit message |

Designer prompts were ~335K tokens each (all eight reader maps inlined). The re-run gives each designer only the relevant maps plus the salvage briefing, and reads the rest from `maps/` on disk.

Salvage of the five partial transcripts: run wf_96b45f67-7c2 → `designs-partial/<W>.md`. Outcome: every one of the five died on its FIRST tool call (the ~314K-token prompt was the cost); nothing substantive to carry forward.

## Second design run (wf_6b051052-ec7, `molt-rollout-design`), 2026-09-05

Slimmer prompts (relevant map digests read from disk). Hit the next five-hour usage limit ("resets 9am (UTC)") after ~14 min:

| agent | tokens | outcome |
|---|---|---|
| design:W1 | 198K | completed (design recorded → `designs/W1.json`) |
| design:W2 | 181K | completed (→ `designs/W2.json`) |
| design:W5 | 191K | completed (→ `designs/W5.json`) |
| design:W3a | 189K | failed mid-work → salvage `designs-partial/W3a-run2.md` |
| design:W4 | 182K | failed mid-work → salvage `designs-partial/W4-run2.md` |
| design:W6 | 168K | failed mid-work → salvage `designs-partial/W6-run2.md` |
| design:W7 | 85K | failed mid-work → salvage `designs-partial/W7-run2.md` |
| design:W3b | 0 | never started |
| verify:* (W1, W2, W5 × 2 lenses) | 0 | never started |
| sequence | 0 | never started |

Continuation: verify W1/W2/W5 from the recorded designs; re-design W3a/W4/W6/W7/W3b with the run-2 salvage briefings; verify; sequence.

## Third and fourth kills, 2026-09-05 (limit "resets 2pm UTC")

**Resume of wf_6b051052-ec7** ("Resume 1"): Design (cached) and Record phases succeeded — the three designs and their digests landed in `designs/`. All six Verify agents then died, each after real work:

| agent | label (inferred by indexer, confirmed at salvage) | transcript lines | tokens |
|---|---|---|---|
| a8e88b94f9f6d0dde | verify:W1:accuracy | 26 | 64K |
| aca2d452765aa1db9 | verify:W1:ordering | 20 | 55K |
| a8a1dd1d6e965042e | verify:W2:accuracy | 39 | 77K |
| a2b07dddf4e929a26 | verify:W2:ordering | 30 | 93K |
| a5601039f915c0f63 | verify:W5:accuracy | 47 | 138K |
| ac2445934a3cd7c7d | verify:W5:ordering | 56 | 126K |

Lens attribution was recovered from two independent signals: prompt sizes cluster into exact pairs (47205/47074 = W5, 39706/39575 = W1, 37374/37243 = W2, matching theorem counts 15 > 11 > 6, with a constant 131-token delta inside each pair), and the larger member of each pair opens by reading root modules / lakefile / docs/rollout/ROLLOUT_NOTES.md (ordering) while the smaller opens by locating cited declarations (accuracy). Launch order agrees.

**wf_dba98d3b-916** (`molt-rollout-design2`): 11-line journal, no result records; five designers died within 17 seconds but each had made a few tool calls (13–19 lines):

| agent | item | lines |
|---|---|---|
| a4cd8772fbe5855fd | design2:W3a | 13 |
| a106047acc40a13bf | design2:W4 | 17 |
| ad424c9c6dc77ce98 | design2:W6 | 15 |
| a39a6e30ae161a695 | design2:W7 | 13 |
| a8b20f7aa718e3de4 | design2:W3b | 19 (weakest label; never opened a `-run2.md` partial) |

Also in wf_6b051052-ec7's journal: eight 5-line transcripts (a4155a89acefe88f4, a4e074b746121a200, aa01ca238e02db8ec, a903ad762ce132cd8, a368a7f9085e5bb8e, af5da61f217ab7f62, a4317d918482ad49f, a90bfd759243e8ed6) that produced no assistant output at all — the rate-limit record sits at offset 4. Nothing to salvage and their labels are unrecoverable, since the only identifying text is in the oversized prompt line.

Salvage of these 11: run wf_13ac64ad-fe2 → `verdicts/<W>-<lens>-partial.md` and `designs-partial/<W>-run3.md`.
