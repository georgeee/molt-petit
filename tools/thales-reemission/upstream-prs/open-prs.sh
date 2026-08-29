#!/usr/bin/env bash
# Fork jessealama/thales under $GH_USER and open three fix PRs (each: one
# patch + one conformance regression test) plus three emitter issues, all
# with verified reproduction snippets.
#
# Requirements: gh (authenticated as $GH_USER: `gh auth login`), git.
# Usage:
#   ./open-prs.sh                 # do it
#   DRY_RUN=1 ./open-prs.sh       # print the side-effecting commands only
#   GH_USER=someone ./open-prs.sh # fork under a different account
set -euo pipefail
SRC="$(cd "$(dirname "$0")" && pwd)"

UPSTREAM=${UPSTREAM:-jessealama/thales}
GH_USER=${GH_USER:-georgeee}
BASE_PIN=55b03fb3fbbcca615cb438b2492d6a1c115d0394
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

run() { if [ "${DRY_RUN:-0}" = 1 ]; then echo "+ $*"; else "$@"; fi; }

gh auth status

# 1. Fork (idempotent) and make git pushes use gh's credentials.
run gh repo fork "$UPSTREAM" --clone=false --default-branch-only || true
run gh auth setup-git

# 2. Fresh upstream clone; PRs branch from the current default branch and
#    fall back to the pinned base commit if upstream has drifted.
git clone --quiet "https://github.com/$UPSTREAM" "$WORK/thales"
cd "$WORK/thales"
git remote add fork "https://github.com/$GH_USER/thales.git"
DEFAULT=$(git symbolic-ref --short refs/remotes/origin/HEAD | sed 's|origin/||')

open_pr() { # slug patch test title
  local slug=$1 patch=$2 test=$3 title=$4
  git checkout -q -B "fix/$slug" "origin/$DEFAULT"
  if ! git apply --3way "$SRC/patches/$patch" 2>/dev/null; then
    echo "NOTE: $patch does not apply on $DEFAULT cleanly; basing on pinned $BASE_PIN" >&2
    git checkout -q -B "fix/$slug" "$BASE_PIN"
    git apply "$SRC/patches/$patch"
  fi
  cp "$SRC/tests/$test" tests/conformance/accept/
  git add -A
  git commit -q -m "$title" \
    -m "Includes a conformance regression test (accept/ bucket); repro and
analysis in the PR description. Found while re-emitting a consensus
reference implementation written in the Thales subset."
  run git push -f fork "fix/$slug"
  run gh pr create --repo "$UPSTREAM" --head "$GH_USER:fix/$slug" \
    --title "$title" --body-file "$SRC/bodies/pr-$slug.md"
}

open_pr parser-paren-ternary 1-parser-paren-ternary.patch \
  ternary-paren-consequent.ts \
  "Parser: do not consume ': T' after a parenthesized expression unless '=>' follows"
open_pr typecheck-union-self-join 2-typecheck-union-self-join.patch \
  ternary-equal-arms-recursive-union.ts \
  "TypeCheck: collapse ternary arm join when both arms have the same type"
open_pr subsetcheck-th0086-scrutinee 3-subsetcheck-th0086-scrutinee.patch \
  switch-scrutinee-null-test.ts \
  "SubsetCheck: exempt switch-scrutinee field access from TH0086"

# 3. Emitter issues (no fixes yet; verified repros in the bodies).
run gh issue create --repo "$UPSTREAM" \
  --title "Emitter: match binders take union field names verbatim and capture enclosing bindings (silent miscompilation)" \
  --body-file "$SRC/bodies/issue-emitter-binder-capture.md"
run gh issue create --repo "$UPSTREAM" \
  --title "Emitter: union-literal field values skip the scrutinee-to-binder substitution" \
  --body-file "$SRC/bodies/issue-emitter-union-literal-projection.md"
run gh issue create --repo "$UPSTREAM" \
  --title "Emitter: numeric literal in a nullable position emits a bare numeral (OfNat (Option Int) failure)" \
  --body-file "$SRC/bodies/issue-emitter-option-literal.md"

echo "Done: 3 PRs + 3 issues against $UPSTREAM from $GH_USER/thales."
