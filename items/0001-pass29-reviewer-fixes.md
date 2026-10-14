---
id: 0001
kind: task
status: done
title: Pass 29: fix independent-review findings F1-F14
owner: session 375f62fc (Molt Petit driver), host bare1
created: 2026-10-14
updated: 2026-10-14
needs_george: ""
data: [bare1:/srv/agent-cage/etheron-bare/agent/etheron-bare/work/review-moltpetit/]
commits: [molt-petit@27a9026 (scaffold), molt-petit@17a9a36 (proved + paper, pushed main+publish-prep)]
---

Independent review of 7ce7743 (item 0002) found F1-F14. Lean side: relational formedness from the genesis
(FormedFrom/TSFormed), signature-threaded certificate histories (SigHist -> cert_tip_sig), mode-2 validator
without the monotone rule, ks twins for modes 2/3. Reviewer approved the new statements (review-2).
Archon run 0a24c128 proving on local publish-prep (docs/PASS29_PROGRESS.md, 14 steps).
Paper wording fixes for all 14 findings on local branch p29-paper (tip 7aff96b), under reviewer re-check (memo-3).
Next: merge, gate, ff push main+publish-prep.
