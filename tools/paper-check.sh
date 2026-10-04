#!/usr/bin/env bash
# Check the paper against Spec/ and Paper/ (part of tools/check.sh):
#  * Spec/*.lean import only Spec, Mathlib and Aeneas, and contain no
#    theorem, lemma, example, tactic block or sorry: definitions and
#    statements only;
#  * tools/paper/Check.lean: cited theorems have thm_xxx and xxx, cited
#    definitions live in Spec/, proofs use only the classical axioms.
# With --bundle OUT, also write OUT (.tgz): Spec/*.lean and paper/molt.tex.
set -euo pipefail
cd "$(dirname "$0")/.."
if command -v lake >/dev/null 2>&1; then
  LAKE=(lake)
else
  LAKE=(nix-run "$HOME/.elan/toolchains/$(sed 's|/|--|; s|:|---|' lean-toolchain)/bin/lake")
fi
python3 - <<'PY'
import re, glob, sys
bad = []
for f in sorted(glob.glob('Spec/*.lean')):
    src = open(f).read()
    # drop comments (nested block comments, then line comments) and strings
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if not depth: out.append(src[i])
        i += 1
    code = re.sub(r'--[^\n]*', '', ''.join(out))
    code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', code)
    for m in re.finditer(r'(?m)^import\s+(\S+)', code):
        if not re.match(r'(Spec\.|Mathlib$|Aeneas$)', m.group(1)):
            bad.append(f'{f}: imports {m.group(1)}')
    for kw in ('theorem', 'lemma', 'example', 'by', 'sorry', 'decreasing_by', 'admit'):
        for m in re.finditer(r'(?<![\w.])' + kw + r'(?![\w\'])', code):
            line = code[:m.start()].count('\n') + 1
            bad.append(f'{f}:{line}: `{kw}`')
for b in bad: print(b, file=sys.stderr)
sys.exit(1 if bad else 0)
PY
mkdir -p .lake/paper-check
python3 - <<'PY'
import re
tex = open('paper/molt.tex').read()
toks = re.findall(r'\\code\{([^}]*)\}', tex[tex.index('\\begin{document}'):])
toks = {t.replace('\\_', '_').replace("$'$", "'") for t in toks}
prose = {'typewriter', 'xxx', 'thm_xxx', 'MoltPaper.xxx'}
toks = sorted(t for t in toks if t not in prose and not re.search(r'[/ ]|^\d|^#|\.(lean|ts|rs)$', t))
open('.lake/paper-check/cited.txt', 'w').write('\n'.join(toks) + '\n')
PY
"${LAKE[@]}" build Spec Paper >/dev/null
"${LAKE[@]}" env lean tools/paper/Check.lean
if [ "${1:-}" = --bundle ]; then
  tar czf "$2" Spec/*.lean paper/molt.tex
  echo "paper-check: wrote $2"
fi
echo "paper-check: ok"
