# `moltPetit.ts`  --thales-->  MoltPetit.lean
#
# Output: `$out/MoltPetit.lean`, the raw unedited emission.  The checked-in
# copy of this is `tools/thales-reemission/MoltPetit.emitted.lean` (the
# "golden"); the file the Lean build actually consumes,
# `Spec/TS.lean`, is that golden plus a small reviewed delta —
# see `checks.ts-vendored-deviations`.
#
# HERMETICITY: fully offline, fully pinned (thales rev + repo patch + the
# Lean 4.29.0 release tarball).  Thales is deterministic: a fresh emission was
# observed byte-identical to the golden across independent runs.
{ lib, runCommand, thales, tsSrc }:

runCommand "molt-petit-lean-from-ts"
{
  nativeBuildInputs = [ thales ];
  meta.description = "Thales emission of moltPetit.ts to Lean 4";
} ''
  mkdir -p "$out"
  thales -o "$out" ${tsSrc}/moltPetit.ts
  # The emitted SET, not just the presence of the one file we consume: a file
  # thales emitted and nothing compared would be unchecked generated Lean.
  emitted=$(cd "$out" && ls | sort | tr '\n' ' ')
  if [ "$emitted" != "MoltPetit.lean " ]; then
    echo "thales emitted more than MoltPetit.lean: $emitted" >&2
    exit 1
  fi
''
