# Molt Petit

Molt Petit is a slot-based Byzantine-fault-tolerant (BFT) consensus protocol with recursive certificates. Its light-client contract requires holding genesis and a local clock, fetching a constant-size recursive certificate, checking that the certificate verifies and its tip is recent, and acting on everything $n$ blocks deep. Validity is governed by a density rule — every matured $n$-slot window must contain blocks from at least two-thirds of a fixed validator roster — with no voting rounds and deterministic, fixed-depth finality.

All safety theorems are machine-checked in Lean 4. In addition to classical counting arguments, the development proves that forged chains advance at at most half real-time speed (making tip recency a load-bearing safety requirement) and establishes key rotation inside consensus against an adversary who steals keys and retains them indefinitely across three operational modes. When measured with post-quantum signatures on commodity hardware, the verified consensus rule adds under 2% to certificate proving cost.

## Repository Layout

- `paper/`: The paper source (`molt.tex`, `yak-wordmark.pdf`, `build.sh`).
- `Spec/`, `Spec.lean`: The paper's definitions and statements, and nothing else: no proofs, and no imports beyond `Spec/`, Mathlib and Aeneas. `Spec/TS.lean` (emitted from `moltPetit.ts` by Thales) and `Spec/Rust.lean` (extracted from `rust/src/lib.rs` by Charon + Aeneas) are the generated implementation code; `Spec/Model.lean`, `Spec/Reference.lean` and `Spec/RustBridge.lean` hold the model, reference-verifier and Rust-to-model definitions; `Spec/Statements.lean` states each result the paper cites as `xxx` as `MoltPaper.thm_xxx`. The rest of the development imports `Spec/`.
- `Paper/`, `Paper.lean`: `Paper/Proofs.lean` proves each `thm_xxx` as `MoltPaper.xxx` by the development's theorem. `tools/paper-check.sh --bundle OUT.tgz` writes `Spec/*.lean` and `paper/molt.tex` as a review bundle.
- `Molt/`, `Molt.lean`: The presentation layer re-exporting and packaging definitions and theorems under the paper's vocabulary, including the headline safety theorem `Molt.timed_light_client_safety`.
- `MoltPetit/`, `MoltPetit.lean`: The formal protocol model, inductive state machine, and proof development.
- Three-way correspondence:
  - **Rust protocol**: `rust/src/lib.rs` (the standalone validator crate), `Spec/Rust.lean` (extracted from `rust/src/lib.rs` via Charon + Aeneas), and the other files in `Rust/` (`Bridge.lean`, `BridgeK.lean`, `Equiv.lean`, `Properties.lean`, `Results_rust.lean`, `TimedResults_rust.lean`, `Axioms.lean`, `AxiomsTimed.lean`) containing the proofs relating them to the model, including headline theorem `Rust.rust_timed_certified_agreement`.
  - **TypeScript protocol**: `moltPetit.ts`, `tools/thales-reemission/`, `Spec/TS.lean` (emitted from `moltPetit.ts` via Thales (vendored with the deviations in `tools/thales-reemission/`)), and the other files in `MoltPetit/TS/` (`Bridge.lean`, `BridgeK.lean`, `Results.lean`) containing the proofs relating them to the model.
- `nix/`, `flake.nix`, `flake.lock`, `NIX.md`: Hermetic toolchain pins for Charon, Aeneas, and Thales, and faithfulness checks.
- `docs/review/`: Annotation and wording review records (`PAPER_WORDING_PROPOSED.md`, `ANNOTATION_REVIEW_REPORT.html`).
- `docs/rollout/`: Planning and verification records for the post-annotation development (`ROLLOUT_PLAN.md`, `ROLLOUT_NOTES.md`, maps, designs, and verdicts).

## Building

All commands run from the repository root unless noted otherwise.

### Full Gate
```bash
tools/check.sh
```
The project's aggregate check: builds every Lean target (including the `#guard_msgs` axiom audits, notably for `Molt.timed_light_client_safety` and `Rust.rust_timed_certified_agreement`), fails on any `sorry` or `axiom` declaration in this repository's sources, runs `tools/paper-check.sh` (`Spec/` holds no proof and imports only `Spec/`, Mathlib and Aeneas; every theorem the paper cites has `thm_xxx` and `xxx`, every cited definition is in `Spec/`, and every proof uses only `propext`, `Classical.choice` and `Quot.sound`), and builds the paper.

### Lean Proofs
```bash
lake build
```

### Extraction Packages (Nix)
```bash
nix build .#lean-from-rust   # Aeneas extraction from rust/src/lib.rs
nix build .#lean-from-ts     # Thales emission from moltPetit.ts
```

### Faithfulness Checks (Nix)
```bash
nix flake check              # Verify extraction faithfulness against checked-in Lean
```

To run only the lightweight check subset:
```bash
nix build .#checks.x86_64-linux.tsc \
          .#checks.x86_64-linux.cargo \
          .#checks.x86_64-linux.pin-consistency \
          .#checks.x86_64-linux.ts-golden-digest \
          .#checks.x86_64-linux.ts-deviation-sites \
          .#checks.x86_64-linux.ts-vendored-deviations \
          .#checks.x86_64-linux.thales-fixes-patch
```

### Proof Soundness Verification (Nix)
```bash
nix run .#verify-lean        # Lake build inside hermetic toolchain (requires network)
```

### Paper
```bash
cd paper && ./build.sh
```

## Provenance

This repository was created as a history-preserving split from `georgeee/mini-consensus-lean` (branch `feature/key-rotation-sound`) starting at base snapshot `3a22bf11bc3fce950a2dab24aa86c886df0854dc`. All replayed commits preserve original authorship, committer metadata, and timestamps, and carry an `Original-commit: georgeee/mini-consensus-lean@<sha>` trailer.

For a complete lookup table of original commit hashes to new commit hashes, see [docs/ORIGINAL-COMMITS.md](docs/ORIGINAL-COMMITS.md).
