# Thales upstream contributions — self-contained package

Run `./open-prs.sh` on any machine with an authenticated `gh` (as
`georgeee`; override with `GH_USER=`). It forks `jessealama/thales`,
opens **three fix PRs** — each carrying one patch plus a conformance
regression test for the `accept/` bucket — and **three emitter issues**
with verified minimal repros. `DRY_RUN=1` previews the side-effecting
commands.

All evidence was verified against the pinned upstream commit `55b03fb`:
the three patches `git apply --check` cleanly at that commit; the three
error messages quoted in the PR bodies were captured from a pristine
(unpatched) build; the three regression tests print byte-identical
output under Node (`--experimental-strip-types`) and under
`thales` + `lake env lean` with the fixes applied; and the three issue
repros' emitted Lean and elaboration outputs are quoted verbatim
(binder capture elaborates with exit 0 — silent miscompilation; the
other two fail loudly).

Layout: `patches/` (one per PR), `tests/` (conformance regression
tests), `bodies/` (PR and issue markdown), `repro/` (the issue-only
snippets, also embedded in the bodies).

Scope note: this is Thales-only. The Rust pipeline (Charon + Aeneas)
went through the same re-extraction/reconciliation discipline and came
out clean — nothing to report upstream there.
