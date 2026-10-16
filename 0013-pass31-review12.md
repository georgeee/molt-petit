---
id: 0013
kind: task
status: done
title: Pass 31, review-12 follow-up (F39-F41, three more Lean-removable limits, page cuts)
owner: session 375f62fc (Molt Petit driver), host bare1
created: 2026-10-16
updated: 2026-10-16
needs_george: ""
data: [bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/review-12.md, bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/memo-13.md]
commits: [molt-petit@9d61ccb (paper F39/F40, cuts), molt-petit@027b940 (pass31 scaffold), molt-petit@853505c (Archon proofs, run fe4faea1 23 min), molt-petit@06ef317 (paper F41 + AttestsCore; main+publish-prep 10-16 10:28Z, gate green, 15 pages)]
---

review-12 found no math drift and no carve-outs, plus three wording items:
- F39 is partly confirmed: badSched is the count of mode 3 and the untimed mode 2. Fixed.
- F40: the key-loss producer now cites the signed liveness theorem. Fixed.
- F41 waits on S1.

Page cuts:
- Done: the "limits of this subsection" paragraph is cut to one sentence, and the slot-time formula is gone. Net 11 lines shorter; still 15 pages.
- Rejected: cutting the "What is trusted" list. It is the only place several unchecked facts are named.

Pass 31 statements (scaffold 027b940):
- S1: signed liveness for modes 2 and 3.
- S2: the TypeScript deployed client at two real check times.
- S3: the mode-free deployed client reads its certificate through a core fold (AttestsCore) instead of mode 1's.

Done:
- Archon proved S1-S3.
- The paper now cites the signed liveness theorems for all three modes (F41 closed).
- The mode-free client assumes only AttestsCore.
- review-13 approved the statements.
- The gate is green; main = publish-prep = 06ef317.

Open: memo-14 asks the reviewer to verify the new text and rank what is left on the three axes.
