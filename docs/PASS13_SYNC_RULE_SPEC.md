# Pass 13 spec: Mode 1 sync-rule budget (paper)

Reviewer-owned; decisions final. Edit `paper/molt.tex` and docs only. No Lean edits.

## Problem
Theorem 3 (`thm:refresh`, Lean `sync_rule`, `sync_rule_mem`) takes as hypothesis a
budget over `badKeyrot … (stripSigs sc)` — corruption read off the floors of the very
chain being validated. A deployment cannot check that in advance. The timed wrappers
`Molt.sync_rule_timed` / `Molt.sync_rule_mem_timed` (Molt/SyncRuleTimed.lean) replace
it by quantities a deployment can attest: a rent rate `ρ` per window (`hRent`), a
per-window census `T` of producers hit by a theft within `d` slots of the window
(`hTheft`, `recentTheftProducersK` — chain-independent, indexed by real theft time),
`ρ + T ≤ fmax` (`hRT`), and the reaction duty `Reacts n n d (stripSigs sc) stolenAt`.

## Decisions
1. Restate Theorem 3 with the timed hypotheses as **the** statement. Title cites
   `sync\_rule\_timed`, `sync\_rule\_mem\_timed`. Hypotheses in prose, one per Lean
   argument: key-stealing surface (`hEUF`, with `Stolen := stolenOf stolenAt`), hash
   injectivity, the cadence + anchor (`hVPrev … hCadence`, `hA`, `hA'`), rent rate,
   theft census, `ρ + T ≤ fmax` on windows starting in the trailing `5n` slots or later,
   reaction delay `d`, validity, recency, `hLong`, `hTipHeight` (equal-height form) /
   `hLe` (membership form). Conclusion unchanged.
2. State the reaction duty exactly as Lean has it: within `d` slots of a theft of
   seat `i`'s version `j`, the version in force for `i` **on the chain being validated**
   is above `j`. Add one sentence saying plainly that this duty is read off the
   validated chain (its confirmed prefix), that rotations take force at `n`-deep where
   all accepted chains agree, and that a fully chain-independent form of the duty is
   open (add it to Limitations, §Limitations, as one item).
3. Keep the untimed census form as the engine: one sentence after the theorem —
   "`sync\_rule`/`sync\_rule\_mem` are the same conclusion under the census budget read
   off the lower chain's floors; the timed form derives it (`budget\_of\_reaction`)".
   Update the boxed one-sentence summary after the theorem to the timed reading
   (rent plus thefts-within-`d` per window ≤ fmax over the trailing 5n slots, plus
   the reaction delay `d`).
4. Shorten the later paragraph "That budget need not be assumed outright …" so it
   does not repeat the theorem; keep its Lean names.
5. Every Lean name cited must exist (grep Molt/ MoltPetit/).

## Done when
- `bash tools/check.sh` prints `check: all green`.
- `grep -n 'sync\\\\_rule\\\\_timed' paper/molt.tex` hits inside the `thm:refresh` title.
- Pass 13 ticked in `docs/PUBLISH_PREP_STATUS.md`.
