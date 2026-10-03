# Pass 8c spec: timed certified safety for the TypeScript validator

Reviewer-owned. The pinned statement is `MoltPetit.Model.ts_timed_certified_agreement`
in `MoltPetit/TS/TimedResults.lean`. Its type and axiom set are pinned by
`Molt/AxiomsTSTimed.lean`; do not edit that file. Replace the `sorry`, and add no new
hypotheses, axioms or `sorry`.

## Proof plan

Mechanical: copy the extraction from `ts_recent_tip_ancestor_agreement`
(MoltPetit/TS/Results.lean, around line 80) and finish like `Rust.rust_timed_certified_agreement`.

1. **Injectivity helpers.** Put them next to `toTSClaim` in `MoltPetit/TS/Bridge.lean`, or
   at the top of `TimedResults.lean`.
   - `toTSChain_injective : Function.Injective toTSChain`, by induction on the list. Every
     `Block` field is carried; `Nat → Int` casts and `Option.map Int.ofNat` are injective
     (`Int.ofNat.inj`, `Option.map_injective`). Use `Block.ext` or `cases` plus `simp_all`.
   - `toTSClaim_injective : Function.Injective toTSClaim`, from the previous helper and
     structure eta.
2. **Validation.** Apply `ts_validateCertifiedChain_sound` to `hval` and to `hval'` to get
   `hcv, hsg, hsfx`. Then rewrite `hsc` into `hsfx`, as the existing proof does.
3. **Claims.** `hUnf h hcv` gives `cl₀, hclEq, hG`. From `hclEq` and `hcl`, get
   `toTSClaim cl₀ = toTSClaim cl`, and so `cl₀ = cl` by `toTSClaim_injective`. Then `subst`.
   Do the same for the primed side.
4. **Signatures.** `ts_sigsOk_signed` gives `hSigned` and `hSigned'`, exactly as in the existing proof.
5. **Suffix.** `ts_validateSuffix_sound hTipS hsfx` gives `hLink, hLinks, hDense` (keep all
   three; the existing proof drops `hDense` with `-`). Do the same for the primed side.
   If the density form differs from the one `timed_certified_agreement` takes, bridge it
   with the lemma the untimed `ts_recent_certified_suffix_agreement` uses.
6. `exact timed_certified_agreement hn hexec hBudget hbridge hG hG' hTipS hTipS' hLink hLinks
   hDense hLink' hLinks' hDense' hSigned hSigned' hRecent hRecent' hc hc' hDeep hDeep'`.
   (`Signed := TSSigned n sigOps`.)

## Second item: the `NoTheftBackdating` degeneracy lemma

`noTheftBackdating_degenerate` in `MoltPetit/Model/KeyStealingSignatureTimed.lean` is pinned
(statement fixed by `Molt/AxiomsTSTimed.lean`). Prove it: specialise `h i j r 0 hst`. At
`s = 0` and `1 ≤ Δconf`, `confirmedPrefix Δconf c₀ 0 = []` (no `b.slot + Δconf ≤ 0`), so
`inForce n Δconf c₀ i 0 = keyFloor n [] i = 0 ≤ j`, and so `r ≤ 0`.

Then update the docstrings of `NoTheftBackdating`, `theft_exposure_window` and every theorem
that takes a `NoTheftBackdating` hypothesis (`grep -rn NoTheftBackdating MoltPetit Molt`).
Add one sentence to each: "This hypothesis is degenerate: it forces every theft to real slot
0 (`noTheftBackdating_degenerate`); the result is retained only as a documented negative
result." Do not change any statement.

## Done when

`bash tools/check.sh` prints `check: all green`. Record progress in
`docs/TS_TIMED_PROGRESS.md`, and tick Pass 8c in `docs/PUBLISH_PREP_STATUS.md`. Commit small
steps on publish-prep. Never push, never switch branches.
