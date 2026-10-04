#!/usr/bin/env bash
# Regenerate the Lean extraction of the Rust protocol (Charon + Aeneas),
# the Rust analogue of re-vendoring the Thales TS output.
#
# Charon and Aeneas are pinned to compatible revisions (Charon must match
# the LLBC version Aeneas expects: charon 0.1.212 <-> this Aeneas).
#   CHARON=...  AENEAS=...  ./extract.sh
# By default they are taken from a local nix build under
#   ~/work/aeneas-toolchain/result-charon-pinned, result-aeneas
# built with:
#   nix build github:AeneasVerif/charon/9dd7f23c8458b2366ce0b5ca7529c5ad4c5fb350
#   nix build github:AeneasVerif/aeneas        # rev bf13c42…
set -euo pipefail
cd "$(dirname "$0")"

TC=${TC:-$HOME/work/aeneas-toolchain}
CHARON=${CHARON:-$TC/result-charon-pinned/bin/charon}
AENEAS=${AENEAS:-$TC/result-aeneas/bin/aeneas}

"$CHARON" cargo --preset=aeneas
mkdir -p lean-out
"$AENEAS" molt_petit.llbc -backend lean -dest lean-out

# Vendor into the Lean project with a header (see Spec/Rust.lean).
{
  sed -n '1,/^-\/$/p' ../Spec/Rust.lean   # keep the existing vendor header
  cat lean-out/MoltPetit.lean
} > ../Spec/Rust.lean.new
mv ../Spec/Rust.lean.new ../Spec/Rust.lean
echo "Regenerated Spec/Rust.lean"
