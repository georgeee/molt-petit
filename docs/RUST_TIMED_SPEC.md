# Pass 8b spec: timed certified safety for the shipped Rust validator

Reviewer-owned. Pinned statement: `Rust.rust_timed_certified_agreement` in
`Rust/TimedResults_rust.lean`. Its type and axiom set are pinned by `Rust/AxiomsTimed.lean`
(do not edit it). Replace the `sorry`; no new hypotheses, axioms, or `sorry`.

## Proof plan (mechanical: copy the extraction from `rust_recent_tip_ancestor_agreement`,
Rust/Results_rust.lean ~line 157)

1. `validate_certified_chain_sound hval` / `hval'` → `cl₀, stripped, hcl₀, hstrip, hcv, hsg, hsfx`.
   Rewrite `hstr` into `hstrip` and `injection` exactly as the existing proof does. From `hcl`
   and `hcl₀` get `cl₀ = cl` (rewrite + `injection`), and likewise for the primed side.
2. `hUnf cert hcv` → `GroundedCert … (RustSigned I crypto n) G (toModelClaim cl)` (match the
   claim with `hcl`). `hUnf' cert' hcv'` then `groundedCert_mono hCryptoSig` → under `crypto`.
3. `sigs_ok_signed` → `hSigned`, `hSigned'` (map the primed one through `hCryptoSig`, after
   `rw [toModelChain_cons]`).
4. `validate_suffix_sound hTipS hsfx` → `hLink, hLinks, hDense` (both sides).
5. `hc'` is over `RustSigned I crypto' n`. Move it to `crypto`. Either add a small lemma
   `groundedHistory_mono` next to `groundedCert_mono` (only the `signed` field changes:
   `B = G ∨ S₁ B → B = G ∨ S₂ B`), or build the structure inline.
6. `exact MoltPetit.Model.timed_certified_agreement hn hexec hBudget hbridge hG hG' hTipS hTipS'
   hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned' hRecent hRecent' hc hc'' hDeep hDeep'`.

## Done when
`bash tools/check.sh` prints `check: all green`. Record progress in `docs/RUST_TIMED_PROGRESS.md`.
Tick Pass 8b in `docs/PUBLISH_PREP_STATUS.md`.
