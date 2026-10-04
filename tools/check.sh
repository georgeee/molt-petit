#!/usr/bin/env bash
# Aggregate gate: every Lean target (including the #guard_msgs axiom audits),
# no sorry and no axiom declarations in this repository's sources, and the paper. Exit 0 only if all pass.
set -euo pipefail
cd "$(dirname "$0")/.."

if command -v lake >/dev/null 2>&1; then
  LAKE=(lake)
else
  LAKE=(nix-run "$HOME/.elan/toolchains/$(sed 's|/|--|; s|:|---|' lean-toolchain)/bin/lake")
fi

echo "== lake build"
log=$(mktemp)
trap 'rm -f "$log"' EXIT
"${LAKE[@]}" build 2>&1 | tee "$log"

echo "== sorry check (Lean's own warnings, this repository's sources only)"
if grep -E "^(warning|error): (\./)?(Spec|Molt|MoltPetit|Rust|Paper|Main)[^:]*\.lean:.*declaration uses .sorry." "$log"; then
  echo "found sorry" >&2
  exit 1
fi

echo "== axiom declaration scan"
if grep -rnE '^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]' --include='*.lean' \
     Spec Molt MoltPetit Rust Paper Spec.lean Molt.lean MoltPetit.lean Rust.lean Paper.lean Main.lean; then
  echo "found axiom declaration" >&2
  exit 1
fi

echo "== paper check (Spec/ purity, citations, axioms)"
bash tools/paper-check.sh

echo "== paper"
bash paper/build.sh >/dev/null

echo "check: all green"
