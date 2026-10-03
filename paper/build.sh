#!/usr/bin/env bash
# Build molt.pdf via TeX Live from nixpkgs — no system LaTeX needed.
set -e
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error molt.tex
elif [ -x /nix/store/xwg31kngm9c3p4cgqhjhyc0hzb8i24ji-texlive-2025-r78234-final-env/bin/latexmk ]; then
  nix-run /nix/store/xwg31kngm9c3p4cgqhjhyc0hzb8i24ji-texlive-2025-r78234-final-env/bin/latexmk -pdf -interaction=nonstopmode -halt-on-error molt.tex
else
  nix-run nix shell github:NixOS/nixpkgs/c27cdad491a991b11ed731760aa2ef8db0cb0410#texliveMedium --command latexmk -pdf -interaction=nonstopmode -halt-on-error molt.tex
fi
