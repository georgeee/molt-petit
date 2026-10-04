#!/usr/bin/env bash
# Regenerate Paper/Bundle.lean, the self-contained file of the paper's
# definitions and statements (see tools/paper-bundle/bundle.py).
#   tools/paper-bundle.sh          regenerate Paper/Bundle.lean
#   tools/paper-bundle.sh --check  fail unless Paper/Bundle.lean is current
# Both modes check the paper's citations and compile the bundle standalone.
set -euo pipefail
cd "$(dirname "$0")/.."
if command -v lake >/dev/null 2>&1; then
  LAKE=(lake)
else
  LAKE=(nix-run "$HOME/.elan/toolchains/$(sed 's|/|--|; s|:|---|' lean-toolchain)/bin/lake")
fi
python3 tools/paper-bundle/bundle.py cited
"${LAKE[@]}" build Paper.Proofs >/dev/null
"${LAKE[@]}" env lean tools/paper-bundle/Extract.lean
out=Paper/Bundle.lean
if [ "${1:-}" = --check ]; then out=.lake/paper-bundle/Bundle.lean; fi
python3 tools/paper-bundle/bundle.py emit "$out"
python3 tools/paper-bundle/bundle.py tokens "$out"
# The bundle elaborates to the same terms as the development: hash every
# declaration's type and value on both sides (tools/paper-bundle/Hashes.lean).
D=.lake/paper-bundle
{ echo "import Paper.Statements"; sed 1d tools/paper-bundle/Hashes.lean
  echo "#paper_hashes \"$D/dev.tsv\""; } > "$D/DevHashes.lean"
{ cat "$out"; echo; sed 1d tools/paper-bundle/Hashes.lean
  echo "#paper_hashes \"$D/bundle.tsv\""; } > "$D/BundleHashes.lean"
"${LAKE[@]}" env lean "$D/DevHashes.lean"
"${LAKE[@]}" env lean "$D/BundleHashes.lean"   # also compiles the bundle standalone
if ! diff "$D/dev.tsv" "$D/bundle.tsv" >&2; then
  echo "the bundle elaborates differently from the development (diff above)" >&2
  exit 1
fi
if [ "${1:-}" = --check ] && ! diff -q Paper/Bundle.lean "$out" >/dev/null; then
  echo "Paper/Bundle.lean is stale: run tools/paper-bundle.sh" >&2
  exit 1
fi
echo "paper-bundle: $(wc -l < "$out") lines, compiles standalone, $(wc -l < "$D/dev.tsv") declarations match the development"
