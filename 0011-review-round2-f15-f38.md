---
id: 0011
kind: task
status: in_progress
title: Reviewer round 2 (F15-F38): verbatim, carve-outs, length
owner: session 375f62fc (Molt Petit driver), host bare1
created: 2026-10-15
updated: 2026-10-15
needs_george: "75ed6a9 is a [FOR GEORGE REVIEW] commit (pre-assumption sections): F19/F21/F22/F30 + cuts F31-F34"
data: [bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/review-5.md, bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/memo-6.md]
commits: [molt-petit@ac6a2e5, molt-petit@f179dbe, molt-petit@75ed6a9 (pushed main+publish-prep 11:31Z, gate green)]
---

George 10-15 mandate: iterate with the reviewer on three axes (paper text faithful to the Lean, no carve-outs,
total page count). review-5 at 17a9a36 raised F15-F38, all confirmed against Spec/. Paper-only fixes:
[A] statement wording F15-F23, [B] disclosures F24-F30, [C] cuts F31-F38. Text now ends on p15 (16 pages
including references). Open: the reviewer re-review (memo-6), and whether F24 (timed mode-3 theorem) and F25
(mode-1 certified, version-indexed) get a Lean pass rather than disclosure.
