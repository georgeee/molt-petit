---
id: 0012
kind: task
status: in_progress
title: Pass 30, disclosed carve-outs removed in Lean (signed liveness, density from budget, per-mode producer, two check times)
owner: session 375f62fc (Molt Petit driver), host bare1
created: 2026-10-15
updated: 2026-10-16
needs_george: ""
data: [bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/review-10.md, bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/memo-11.md]
commits: [molt-petit@a5768f7 (scaffold), molt-petit@10f82f3 (scaffold fix), molt-petit@193fd8b (Archon proofs), molt-petit@a71c1cc (paper; main+publish-prep 10-16 08:56Z, gate green, 15 pages)]
---

From review-9's ranking of the disclosed limits that could be removed in Lean, review-10 approved four statement groups:
- S1: signed liveness, `liveness_produce_signed_block{,K}`, with the signed definitions moved into Spec.
- S2: deployed producer with density derived from `ByzantineBounded` and delivery.
- S3: per-mode producer theorems (k, sched, lock).
- S4: deployed clients at two real times R, R' at most d apart.

Archon proved all 7 steps in 31 minutes (run a52c4928). An earlier 6-minute run stopped on a missing comma in my
scaffold. The paper drops "mode 1 unsigned", "one real time R", "no per-mode producer yet" and "density assumed".
Gate: check.sh all green, nix flake check passed. The page count stays at 15.

Open: the reviewer's re-review (memo-11).
