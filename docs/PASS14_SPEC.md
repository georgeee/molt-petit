# Pass 14 spec: final consistency and polish

Reviewer-owned; decisions final. Never change any theorem STATEMENT, and never edit the pinned
guard files (Molt/AxiomsTimedSafety.lean, Molt/AxiomsTimedSafetyCert.lean,
Rust/AxiomsTimed.lean). Proof bodies, comments and docstrings may change.

1. **Lean lint** in MoltPetit/Model/TimedSafety.lean, MoltPetit/Model/TimedSafetyCert.lean,
   Rust/TimedResults_rust.lean: eliminate every linter warning that `lake build` prints for
   those three files (lines over 100 characters, "extra space", `show` misuse, flexible
   `simp` → `simp only [...]`/`simp?`), without changing statements. Restore a module
   docstring (`/-! … -/`) at the top of TimedSafety.lean describing the timed model result
   and naming `timed_tip_ancestor_agreement` as its main theorem; every public theorem in these
   files has a `/-- … -/` docstring.
2. **Stale numbers in Lean comments**: the docstring of `SigUnforgeableRecent`
   (MoltPetit/Model/Definitions.lean ~line 660) claims a breakeven at Δ ≈ 1.5n and a ~50% margin.
   These are not machine-checked; rewrite the comment to say the timed headline
   (`timed_tip_ancestor_agreement`) proves safety at staleness `n` directly, and this residue is
   only the untimed model's assumption. grep the repo's .lean comments for `1.5n`, `50%`, `3/2`
   and fix any other such claim the same way.
3. **§2 table** (paper/molt.tex, the results/overview table in §2): every row accurate and
   naming the current headline Lean theorem: Theorem 1 `timed_light_client_safety`
   (+ Rust: `rust_timed_certified_agreement`), Theorem 3 `sync_rule_timed`, Theorem 4 the
   horizon pair, Theorem 5/5b as stated. Check each row's hypotheses/conclusion against the
   theorem text in §6.
4. **README.md**: wherever it lists headline theorems or the axiom audit, add
   `Molt.timed_light_client_safety` and `Rust.rust_timed_certified_agreement`.
5. **docs/PUBLISH_PREP_STATUS.md §4 "Open Questions"**: remove item 3 (representability /
   exposure hypothesis: obsolete, Theorem 1 no longer has it). Add: mode-1 reaction delay
   `Reacts` is read off the validated chain (open, disclosed in Named seams).
6. Run `bash tools/check.sh` (must print `check: all green`), then tick Pass 14 and append the
   line `STATUS: READY FOR REVIEW` at the end of docs/PUBLISH_PREP_STATUS.md. Never write
   `STATUS: COMPLETE`.
