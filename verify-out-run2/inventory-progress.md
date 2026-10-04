# Inventory Progress

- **Status**: COMPLETE
- **Paper**: `paper/molt.tex`
- **Output files**:
  - `verify-out/claims-draft.json`: Initial inventory of formal and prose claims extracted from the paper.
  - `verify-out/Stmts.lean`: Lean script containing `#check @Name` and `#print axioms Name` for all 194 referenced declarations across `Molt`, `MoltPetit`, and `Rust`.
  - `verify-out/lean-statements.txt`: Verbatim execution output from Lean 4.30.0-rc2 containing `#check` signatures and axiom dependencies for all declarations.
  - `verify-out/claims.json`: Complete structured JSON inventory of all 107 claims ({id, kind, tex_lines, tex_statement, lean_decls, lean_resolved, lean_statement, axioms, notes}).

## Summary of Results
1. **Total Claims Identified**: 107
   - 8 formal `\begin{theorem}...\end{theorem}` environments (Theorems 1 through 8 in the paper: `thm:lc`, `thm:forge`, `thm:refresh`, `thm:sched`, `thm:lock`, `thm:lock-gen`, `thm:live`, `thm:timed-uniq`).
   - 99 prose claims asserting machine-checked / proved results or citing Lean declarations (`\code{...}`).
2. **Symbols and Declarations Mapped**:
   - 110 unique code symbols extracted from claims across `paper/molt.tex`.
   - All 110 symbols resolved to their underlying declarations in `MoltPetit.Model`, `Molt`, or `Rust` (resolving aliases between the `Molt.*` convenience namespace and the underlying `MoltPetit.Model.*` declarations).
   - High-level prose assertions without specific code identifiers (e.g. general design/paper summaries or informal density remarks) are explicitly annotated in `notes` with their context and relationship to the formal codebase.
3. **Ground Truth Verification**:
   - `verify-out/Stmts.lean` constructed and verified via `$(cat verify-out/lake-cmd.txt) env lean verify-out/Stmts.lean > verify-out/lean-statements.txt 2>&1`.
   - All 194 `#check` and `#print axioms` invocations succeeded without errors.
   - All statements and axioms extracted verbatim into `verify-out/claims.json`.
