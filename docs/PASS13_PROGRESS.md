# Pass 13 Progress Log: Mode 1 Sync-Rule Budget (Paper)

Tracking rework of Theorem 3 (`thm:refresh`) in `paper/molt.tex` per `docs/PASS13_SYNC_RULE_SPEC.md`.

## Summary of Decisions & Implementation

- [x] **Decision 1: Restate Theorem 3 with timed hypotheses as primary statement**
  - Title cites `sync\_rule\_timed`, `sync\_rule\_mem\_timed`.
  - Hypotheses stated in prose, one per Lean argument:
    - Key-stealing surface (`hEUF`): `KeyStealingEUFCMA` with `Stolen := stolenOf stolenAt`.
    - Hash injectivity (`hHash`): collision resistance on signed blocks (`SignedHashInjective`) over genesis $G$ and `KeyStealingSigned`.
    - Cadence and anchor (`hVPrev … hCadence`, `hA`, `hA'`): client re-verified valid chain `scPrev` of length $> n$ at $t \le \mathit{tipPrev.slot} + n$, took anchor $A$ as $n$-deep block, returns within $n$ slots ($\mathit{now} \le t + n$), and both `sc`, `sc'` contain $A$.
    - Rent rate (`hRent`): on every window $u$ with $\mathit{now} < u + 5n$, rented slots (`badSlotsIn`) total at most $\rho$.
    - Theft census (`hTheft`): on every window $u$ with $\mathit{now} < u + 5n$, distinct producers hit by theft within $d$ slots of $u$ (`recentTheftProducersK`) total at most $T$.
    - Fault budget (`hRT`): $\rho + T \le \fmax$ on windows starting in trailing $5n$ slots or later.
    - Reaction delay $d$ (`hReacts`): within $d$ slots of theft of seat $i$'s version $j$, version in force for $i$ on validated chain `sc` is above $j$ (`Reacts`).
    - Validity (`hVal`, `hVal'`): both `sc` and `sc'` pass `validSignedChainK'`.
    - Recency (`hRecent`, `hRecent'`): tips recent ($\mathit{now} \le \mathit{sTip.slot} + \Delta$).
    - Chain length (`hLong`): both chains longer than $n$ blocks.
    - Tip height (`hTipHeight` / `hLe`): equal height for equal-height form, lower tip height $\le$ other for membership form.
  - Conclusion unchanged: agree on $n$-deep block ($B = B'$) at equal height; lower chain's $n$-deep block is block of taller chain at unequal heights.

- [x] **Decision 2: Reaction duty exact specification and limitations disclosure**
  - Stated reaction duty exactly as Lean has it: within $d$ slots of a theft of seat $i$'s version $j$, the version in force for $i$ on the chain being validated is above $j$.
  - Added clarifying sentence after theorem: duty is read off the validated chain (its confirmed prefix), rotations take force at $n$-deep where all accepted chains agree, and a fully chain-independent form of the duty is open (§Limitations).
  - Added limitation item in §Limitations (`sec:limitations`) and noted in Named Seams.

- [x] **Decision 3: Untimed census form as engine & updated boxed summary**
  - Added sentence after theorem: "`sync\_rule`/`sync\_rule\_mem` are the same conclusion under the census budget read off the lower chain's floors; the timed form derives it (`budget\_of\_reaction`)".
  - Updated boxed one-sentence summary to timed reading (rent plus thefts-within-$d$ per window $\le \fmax$ over trailing $5n$ slots, plus reaction delay $d$).

- [x] **Decision 4: Shorten later paragraph on reaction delay**
  - Shortened paragraph "That budget need not be assumed outright..." to reference Theorem 3 and derivation via `budget_of_reaction`, while preserving Lean names (`Reacts`, `budget_of_reaction`, `sync_rule_timed`, `max_sync_period_timed`).

- [x] **Decision 5: Lean declaration audit**
  - Verified every cited Lean name exists in `Molt/` and `MoltPetit/` (`sync_rule_timed`, `sync_rule_mem_timed`, `KeyStealingEUFCMA`, `stolenOf`, `SignedHashInjective`, `KeyStealingSigned`, `validSignedChainK'`, `badSlotsIn`, `recentTheftProducersK`, `faultBudget`, `Reacts`, `sync_rule`, `sync_rule_mem`, `budget_of_reaction`, `stripSigs`).

- [x] **Validation**
  - `bash paper/build.sh` runs clean with 0 errors and 0 warnings (19 pages).
  - `grep -n 'sync\_rule\_timed' paper/molt.tex` hits inside `thm:refresh` title.
  - `bash tools/check.sh` prints `check: all green`.
