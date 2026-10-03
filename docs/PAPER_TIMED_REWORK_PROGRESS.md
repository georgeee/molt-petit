# Pass 9 Progress Log: Theorem 1 and Recency Rework (Paper)

Tracking rework of `paper/molt.tex` per `docs/PAPER_TIMED_REWORK_SPEC.md`.

## Summary of Decisions & Implementation

- [x] **Decision 1: Theorem 1 (`thm:lc`, §6.1) becomes timed theorem `Molt.timed_light_client_safety`**
  - Cites `Molt.timed_light_client_safety` in title.
  - Hypotheses stated in prose matching Lean arguments:
    - $n \ge 1$ and deployment genesis $G$.
    - `TimedExecution`: `key_match`, `honest_stamp`, `honest_once`, `chain_order`, `id_inj`.
    - Real-slot fault budget: `ByzantineBounded n bad`.
    - Verifier real slot $R$ and EUF-CMA + causality bridge `hbridge`.
    - Two presentations with `GroundedCert` and validator suffix conditions (`hLink`, `hLinks`, `hDense`, `hSigned`).
    - Recency in real time: $R \le tip.slot + n$.
    - Conclusion over attested histories `GroundedHistory`: full chains agree at every height $h$ with $h + n$ below lengths.
  - Removed "exposes that height" clause and presentation restriction paragraph.
  - Rewrote remarks to cite timed model and proof idea (availability at $R$, half-speed forging bound, counting argument).

- [x] **Decision 2: Untimed `Molt.light_client_safety` demoted**
  - Included as short remark after Theorem 1: reaches same conclusion in untimed model assuming `SigUnforgeableRecent` directly and keeping exposure hypothesis.

- [x] **Decision 3: Assumptions (§5) rewritten for headline needs**
  - Fault budget (`ass:budget`): per real slot, citing `ByzantineBounded`.
  - Signatures (`ass:sig`): kept custody and EUF-CMA; replaced residue with timed signing discipline (`key_match`, `honest_stamp`, `honest_once`, `hbridge`, `chain_order`); replaced paragraph with note on coerced future stamps.
  - Hash (`ass:hash`): updated headline citation to `TimedExecution.id_inj` over `SignedEver`.
  - Certificate grounding (`ass:cert`): unchanged.
  - Clock (`ass:clock`): stated as verifier local time `now`, $R \le now + \delta$, accept when $now \le tip.slot + b$, with $b + \delta \le n$ (example $b = n/2$ leaving $n/2$ slots for skew + propagation). Updated all recency occurrences in §2, §3.3 / `sec:verifier-rule`, Table 1, and §5 intro.

- [x] **Decision 4: Drop unproven numbers**
  - Removed claims of $\approx 3/2 \cdot n$ staleness safety margin and $50\%$ margin.
  - Reframed §6.2: Theorem 2 is the engine of Theorem 1; fork meeting recency bar has had too little real time to forge an $n$-deep ancestor; Theorem 1 machine-checks this at staleness $n$.

- [x] **Decision 5: Appendix A reframed as "The untimed residue, derived"**
  - Added opening clarification that headline Theorem 1 does not use `SigUnforgeableRecent` or `NoBackdate`.
  - Explained route by which untimed `light_client_safety` residue follows from EUF-CMA and `NoBackdate`.
  - Updated cross-references.

- [x] **Decision 6: Abstract updated**
  - Replaced recency check phrasing with statement that light-client safety is proved directly in a timed model against an adversary harvesting coerced signatures for any slot.

- [x] **Decision 7: Sweep & Validation**
  - Verified no occurrences of `exposes that height`, `tfrac{3}{2}`, or `50\%`.
  - Verified `timed_light_client_safety` cited and in title of `thm:lc`.
  - Verified all cited Lean names exist in `Molt/` and `MoltPetit/`.
  - LaTeX build passes cleanly (`paper/build.sh` produces `molt.pdf`).
  - `bash tools/check.sh` prints `check: all green`.
