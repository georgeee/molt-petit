---
id: 0013
kind: task
status: in_progress
title: Pass 31, review-12 follow-up (F39-F41, three more Lean-removable limits, page cuts)
owner: session 375f62fc (Molt Petit driver), host bare1
created: 2026-10-16
updated: 2026-10-16
needs_george: ""
data: [bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/review-12.md, bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/memo-13.md]
commits: [molt-petit@9d61ccb (paper F39/F40, cuts), molt-petit@027b940 (pass31 scaffold)]
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

Next:
1. Archon run, on 18's BIG GO after the Yak ledger window.
2. Paper: F41, and drop the "reads the certificate as mode 1's fold" clause.
3. Gate.
4. Fast-forward main.
5. Reviewer approval of the statements (memo-13).
