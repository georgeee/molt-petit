#!/usr/bin/env bash
# Deterministic checks. Writes verify-out/checks.json (last) and verify-out/*.log. Safe to call repeatedly.
cd "$(git rev-parse --show-toplevel)"
[ -s verify-out/checks.json ] && { cat verify-out/checks.json; exit 0; }
if [ -e verify-out/.checks.running ]; then echo "checks already running since $(cat verify-out/.checks.running)"; exit 0; fi
date -u +%FT%TZ > verify-out/.checks.running
LAKE=$(command -v lake || true)
TC=$(sed 's|/|--|; s|:|---|' lean-toolchain)
[ -z "$LAKE" ] && [ -x "$HOME/.elan/toolchains/$TC/bin/lake" ] && LAKE="nix-run $HOME/.elan/toolchains/$TC/bin/lake"
[ -z "$LAKE" ] && [ -x "$HOME/.elan/bin/lake" ] && LAKE="nix-run $HOME/.elan/bin/lake"
echo "$LAKE" > verify-out/lake-cmd.txt
lake_rc=127; tex_rc=127
if [ -n "$LAKE" ]; then $LAKE build > verify-out/lake-build.log 2>&1; lake_rc=$?; fi
bash paper/build.sh > verify-out/tex-build.log 2>&1; tex_rc=$?
grep -rnE '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' --include='*.lean' . | grep -v '/\.lake/' | grep -vE ':[[:space:]]*--' > verify-out/sorry-hits.txt || true
grep -rnE '^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]' --include='*.lean' . | grep -v '/\.lake/' > verify-out/axiom-decls.txt || true
grep -nE 'Warning|undefined|Overfull|Rerun' paper/molt.log 2>/dev/null | head -50 > verify-out/tex-warnings.txt || true
printf '{"lake_cmd":"%s","lake_build_rc":%s,"tex_build_rc":%s,"sorry_hits":%s,"axiom_decls":%s,"tex_warning_lines":%s}\n' \
  "$LAKE" "$lake_rc" "$tex_rc" "$(wc -l < verify-out/sorry-hits.txt)" "$(wc -l < verify-out/axiom-decls.txt)" "$(wc -l < verify-out/tex-warnings.txt)" > verify-out/checks.json.tmp
mv verify-out/checks.json.tmp verify-out/checks.json
rm -f verify-out/.checks.running
cat verify-out/checks.json
