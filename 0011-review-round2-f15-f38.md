---
id: 0011
kind: task
status: done
title: Reviewer round 2 (F15-F38): verbatim, carve-outs, length
owner: session 375f62fc (Molt Petit driver), host bare1
created: 2026-10-15
updated: 2026-10-15
needs_george: "75ed6a9 is a [FOR GEORGE REVIEW] commit (pre-assumption sections): F19/F21/F22/F30 + cuts F31-F34"
data: [bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/review-5.md, bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/memo-6.md]
commits: [molt-petit@75ed6a9, molt-petit@2b4e35f ([FOR GEORGE REVIEW]), molt-petit@4e9246d (pushed 19:20Z, 15 pages total)]
---

George 10-15 mandate: iterate with the reviewer on three axes (paper text faithful to the Lean, no carve-outs,
total page count). review-5 at 17a9a36 raised F15-F38, all confirmed against Spec/. Paper-only fixes:
[A] statement wording F15-F23, [B] disclosures F24-F30, [C] cuts F31-F38. Text now ends on p15 (16 pages
including references). Open: the reviewer re-review (memo-6), and whether F24 (timed mode-3 theorem) and F25
(mode-1 certified, version-indexed) get a Lean pass rather than disclosure.

Update 14:44Z: review-6 closed all F15-F38. Q1: the proposed timed mode-3 theorem would itself be a carve-out
(validator does not check rosterGen), so disclosure stands. Q2: disclosure enough. Q3 cuts pushed at 2b4e35f:
16 pages, 25 lines of references on p16. memo-7 asks for ~25 more lines.

Update 19:20Z: review-7 cleared 2b4e35f (no loss) and listed more cuts. Only the after-cutoff ones were taken (4e9246d): 15 pages total. memo-8 asks for a re-review plus any remaining verbatim/carve-out issues.
