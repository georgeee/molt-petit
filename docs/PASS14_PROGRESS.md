# Pass 14 Progress: Final Consistency and Polish

Tracking implementation and verification of Pass 14 per `docs/PASS14_SPEC.md`.

## Status Summary

- [x] **Item 1: Lean lint**
  - Cleaned up linter warnings in `MoltPetit/Model/TimedSafety.lean`, `MoltPetit/Model/TimedSafetyCert.lean`, and `Rust/TimedResults_rust.lean`.
  - Verified no lines exceed 100 characters in these files.
  - Confirmed no `show` misuse, flexible `simp`, or whitespace warnings.
  - Restored module docstring (`/-! ... -/`) at top of `TimedSafety.lean` naming `timed_tip_ancestor_agreement` as its main theorem.
  - Added docstrings to all public theorems and definitions across these three files.
- [x] **Item 2: Stale numbers in Lean comments**
  - Updated docstring of `SigUnforgeableRecent` in `MoltPetit/Model/Definitions.lean` to state that the timed headline (`timed_tip_ancestor_agreement`) proves safety at staleness $n$ directly, and the residue is only an assumption of the untimed model.
  - Updated `MoltPetit/Results/Results.lean` commentary regarding recency and rate limits.
  - Checked repository `.lean` sources for any remaining stale occurrences of `1.5n`, `50%`, `3/2` outside `.lake`.
- [x] **Item 3: §2 Table (paper/molt.tex)**
  - Re-positioned and formatted the operational modes table in §2 of `paper/molt.tex`.
  - Every row accurately cites the corresponding headline Lean theorem:
    - Mode 0: Thm.~\ref{thm:lc}: `timed_light_client_safety` (+ Rust: `rust_timed_certified_agreement`)
    - Mode 1: Thm.~\ref{thm:refresh}: `sync_rule_timed`
    - Mode 2: Thm.~\ref{thm:sched}: `sched_recent_tip_ancestor_agreement_horizon`, `sched_recent_tip_ancestor_mem_horizon`
    - Mode 3: Thm.~\ref{thm:lock}: `lockstep_client_safety`; Thm.~\ref{thm:lock-gen}: `lockstep_client_safety_gen`, `lockstepGen_recent_tip_ancestor_mem`
  - Replaced duplicate table in §6.3 with cross-reference back to §2.
  - Adjusted column widths to prevent overfull hboxes.
- [x] **Item 4: README.md**
  - Updated presentation layer description to cite headline theorem `Molt.timed_light_client_safety`.
  - Updated Rust protocol section to include `TimedResults_rust.lean` and `AxiomsTimed.lean`, citing `Rust.rust_timed_certified_agreement`.
  - Updated Full Gate aggregate check description to note `#guard_msgs` axiom audits for `Molt.timed_light_client_safety` and `Rust.rust_timed_certified_agreement`.
- [x] **Item 5: docs/PUBLISH_PREP_STATUS.md §4 Open Questions**
  - Removed obsolete item 3 (representability / exposure hypothesis).
  - Added mode-1 reaction delay `Reacts` read off the validated chain (open, disclosed in Named seams).
- [x] **Item 6: Gate & Status**
  - Executed `tools/check.sh` confirming Lean builds with zero sorry, zero axioms, clean axiom audits, and paper builds cleanly (`check: all green`).
  - Ticked Pass 14 in `docs/PUBLISH_PREP_STATUS.md`.
  - Appended `STATUS: READY FOR REVIEW` to `docs/PUBLISH_PREP_STATUS.md`.
