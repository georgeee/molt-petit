#!/usr/bin/env bash
# Build molt.pdf via TeX Live from nixpkgs — no system LaTeX needed.
#   ./build.sh
# Same minimal `texlive.combine` as georgeee/mini-consensus-lean: paper/build.sh (see the rationale there).
set -e
cd "$(dirname "$0")"
nix-shell -p '(texlive.combine { inherit (texlive) scheme-small latexmk microtype xcolor booktabs geometry amsmath amscls hyperref pgf; })' \
  --run "latexmk -pdf -interaction=nonstopmode -halt-on-error molt.tex"
