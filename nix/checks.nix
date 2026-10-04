# The faithfulness checks — the point of this flake.
#
# Each one pins a *generated, checked-in* artefact to the toolchain that
# generated it.  Read the "PROVES / DOES NOT PROVE" note on each: they pin
# artefacts to their sources, they do not audit the sources, and none of them
# says anything about whether the Lean project builds (that is `verify-lean`,
# which cannot be a derivation — see nix/apps.nix).
#
# THE PAIRING, stated once here and once in flake.nix because it is the thing
# most easily got wrong:  `nix flake check` proves FAITHFULNESS (the vendored
# Lean is what the pinned toolchains emit).  It says nothing about SOUNDNESS.
# A semantics-altering edit to rust/src/lib.rs or moltPetit.ts followed by
# `nix run .#update-extracted` passes every check here.  The proofs are only
# re-checked by `nix run .#verify-lean`, which needs the network and therefore
# cannot be a check.  Run both, or you have gated on half the claim.
#
# SCOPE: `rust-keyrot/` and `rust-keyrot-p3/` (in georgeee/mini-consensus-lean) are deliberately outside this
# flake — they are plonky2 demos that reuse the `molt_petit` crate as a
# library, nothing in the Lean development derives from them, and their
# `rust-toolchain.toml` says `channel = "stable"`.  Nothing below covers them.
{ lib
, runCommand
, writeText
, jq
, gnupatch
, gawk
, stdenv
, typescript
, nodejs
, cargo
, rustc
, lean-from-rust
, lean-from-ts          # null on systems where thales is not expressible
, extractedLean         # path to Spec/Rust.lean
, emittedLean           # path to Spec/TS.lean
, goldenEmitted         # path to tools/thales-reemission/MoltPetit.emitted.lean
, deviationsPatch       # path to tools/thales-reemission/vendored-deviations.patch, or null
, thalesFixesPatch      # path to tools/thales-reemission/thales-fixes.patch
, upstreamPrPatches     # dir tools/thales-reemission/upstream-prs/patches
, tsSrc                 # dir containing moltPetit.ts
, rustCrateSrc          # the molt_petit crate
, lakefileToml          # path to lakefile.toml
, charonRev             # locked rev of the `charon` flake input
, aeneasSrc             # source tree of the `aeneas` flake input
, aeneasRev             # locked rev of the `aeneas` flake input
, thalesSrc             # source tree of the `thales-src` flake input
, leanVersion           # leanRelease.version, e.g. "4.29.0"
, batteriesRev          # locked rev of the `batteries-src` flake input
, leanRegexRev          # locked rev of the `lean-regex-src` flake input
}:

let
  ##########################################################################
  # Recorded digests.
  #
  # These are TRIPWIRES, not cryptographic pins: this file is as
  # repo-controlled as the files it names, so anyone who can edit an artefact
  # can edit the constant too.  Their value is that they turn a silent
  # regeneration into a two-file diff a reviewer cannot miss.
  ##########################################################################

  # DIGEST-PIN goldenEmitted — rewritten by `nix run .#update-extracted`.
  # Keep this line's shape (two spaces, name, ` = "`, 64 hex, `";`): the app
  # rewrites it with sed and verifies that the rewrite took.
  goldenDigest = "39f7326c6d9cfd6d5d84140057e12c3d2ef9503dff9fef0295f056f3f5b37b9f";

  # DIGEST-PIN thalesFixesPatch — hand-maintained; nothing regenerates it.
  # This patch DEFINES what "faithful" means for the TypeScript path: it is
  # applied to the pinned Thales before the emitter runs, so a change here
  # changes the emission, and `ts-emission-golden` would happily re-bless the
  # new output.  Everything else in the chain is pinned by revision; this file
  # is the one link pinned only by review.
  thalesFixesDigest = "af8e38b91b2b60812d33131e7703c72e0a19d44053c04d57777e73cf1cb9f462";

  ##########################################################################
  # splitAssert — establish the vendor-header/body boundary, and PROVE the
  # header is inert.
  #
  # Both vendored files carry a prose header terminated by a bare `-/` line,
  # and the generated body starts on the next line.  Aeneas and Thales never
  # emit a bare `-/` (they close docstrings with a trailing ` -/` on the same
  # line), so the terminator is unambiguous.
  #
  # Asserting the terminator's position is NOT enough, and this is the whole
  # reason for the last two assertions.  Every check below reads the body as
  # `tail -n +$body_from`, so lines 1..hdr are outside all of them.  If those
  # lines were unconstrained, one could close the prose early with a
  # non-bare `… -/`, insert `import Something` (Lean module headers admit
  # comments and imports interleaved before the body's own imports), reopen
  # `/-`, and land the single bare `-/` back on its expected line.  The result
  # is arbitrary Lean — a high-priority `BEq` instance, a `macro_rules`, a
  # notation override — sitting above a body that every check still certifies
  # as byte-identical to the emitter output.  Requiring the header to be
  # exactly one block comment closes that.
  ##########################################################################
  splitAssert = file: expectedHeaderLines: ''
    n=$(grep -c '^-/$' ${file} || true)
    if [ "$n" != "1" ]; then
      echo "FAIL: expected exactly one bare '-/' header terminator in ${file}, found $n" >&2
      exit 1
    fi
    hdr=$(sed -n '1,/^-\/$/p' ${file} | wc -l)
    if [ "$hdr" != "${toString expectedHeaderLines}" ]; then
      echo "FAIL: vendor header of ${file} is $hdr lines, expected ${toString expectedHeaderLines}." >&2
      echo "      If the header legitimately changed, update nix/checks.nix." >&2
      exit 1
    fi
    if [ "$(sed -n '1p' ${file})" != "/-" ]; then
      echo "FAIL: ${file} must begin with a bare '/-' opening the vendor header." >&2
      echo "      Found: $(sed -n '1p' ${file})" >&2
      exit 1
    fi
    sed -n "2,$((hdr - 1))p" ${file} > header-interior.txt
    if grep -q -e '/-' -e '-/' header-interior.txt; then
      echo "FAIL: the vendor header of ${file} is not a single block comment." >&2
      echo "      Lines 2..$((hdr - 1)) must be plain prose.  A nested '/-' or '-/'" >&2
      echo "      can close the comment early and hide Lean declarations above the" >&2
      echo "      body, which every check reads starting at line $((hdr + 1))." >&2
      grep -n -e '/-' -e '-/' header-interior.txt >&2 || true
      exit 1
    fi
    rm -f header-interior.txt
    body_from=$((hdr + 1))
  '';

  ##########################################################################
  # declSplit — canonicalise a Thales emission into per-declaration files.
  #
  # Needed because the dominant "deviation" between the golden and the
  # vendored file is a 32-line BLOCK MOVE, which `diff -u` renders as one
  # deletion plus one insertion of nearly-identical text.  Real edits hide
  # inside such a hunk (they did: a `deriving` change and three
  # parenthesisation rewrites were buried in it).  Splitting by declaration
  # and comparing name-by-name makes a pure move produce nothing at all, so
  # only genuine edits survive to be enumerated.
  #
  # The emission's shape makes this safe: every top-level form starts in
  # column 0 and every continuation line is indented.
  ##########################################################################
  declSplitAwk = writeText "decl-split.awk" ''
    function flush() {
      if (name == "") return
      while (nbuf > 0 && buf[nbuf] ~ /^[[:space:]]*$/) nbuf--
      if (seen[name]++) { print "FAIL: duplicate top-level declaration: " name > "/dev/stderr"; exit 1 }
      for (i = 1; i <= nbuf; i++) print buf[i] > (dir "/" name)
      close(dir "/" name)
      print name > (dir "/.names")
      nbuf = 0
    }
    /^[^[:space:]]/ {
      flush()
      if ($1 == "abbrev" || $1 == "def" || $1 == "inductive" || $1 == "structure")
        name = $1 "@" $2
      else
        name = "0toplevel@" $0
      gsub(/[^A-Za-z0-9@._-]/, "_", name)
    }
    { buf[++nbuf] = $0 }
    END { flush(); close(dir "/.names") }
  '';

  # The declarations that Spec/TS.lean is allowed to differ from
  # the raw emission at, one per line, sorted.  Anything else — a new site, or
  # a site that stops differing — fails `ts-deviation-sites`.
  #
  #   inductive@Chain        deviation 2: `deriving Repr` -> `deriving Repr, BEq`
  #   inductive@FloorList    same, and NOT named by the header's deviation 2
  #   structure@SigOps       deviation 3: `deriving Repr, BEq` removed
  #   structure@CertOps      deviation 3: likewise
  #   def@monoAgainst        emitter binder capture: `slot` -> `slot'`
  #   def@produceBlock       emitter binder capture: `keyIndex` -> `keyIndex'`
  #   def@floorBump          union-literal projection `.fcons fl.producer` ->
  #                          `.fcons producer`, plus a parenthesisation rewrite
  #   def@floorsShapeFrom    parenthesisation only: `((i + 1))` -> `(i + 1)`
  #   def@keyMonoFromTs      parenthesisation only
  #
  # The three binder/projection sites are the semantic ones; the rest are
  # `deriving` clauses and redundant parentheses.  This list is what makes the
  # ledger an enumeration rather than a 122-line diff nobody reads.
  # Top-level forms of the golden that the vendored file removes (deviation
  # 5: the import of the empty Thales runtime and its `open`), so that
  # Spec/ imports nothing outside Spec/, Mathlib and Aeneas.
  removedSites = writeText "ts-removed-sites.txt" ''
    0toplevel@import_Thales.TS.Runtime
    0toplevel@open_Thales.TS
  '';

  deviationSites = writeText "ts-deviation-sites.txt" ''
    def@floorBump
    def@floorsShapeFrom
    def@keyMonoFromTs
    def@monoAgainst
    def@produceBlock
    inductive@Chain
    inductive@FloorList
    structure@CertOps
    structure@SigOps
  '';
in
{
  ##########################################################################
  # rust-extraction — byte-exact.
  #
  # PROVES: the body of Spec/Rust.lean is exactly what the pinned charon
  # (9dd7f23c…, 0.1.212) + aeneas (bf13c42e…) produce from the current
  # rust/src/lib.rs; no hand-edits; the theorems in Rust/Properties.lean,
  # Rust/Bridge.lean and Rust/Equiv.lean are about definitions that really
  # came from the Rust.
  # DOES NOT PROVE: that the Rust agrees with the TS or with the Lean model
  # (the two documented Rust-vs-TS deviations live inside lib.rs and are
  # invisible here); that the 16-line vendor header is *accurate* (only that
  # it is inert — see splitAssert); that the extraction is axiom-free (that is
  # Rust/Axioms.lean's job); that the proofs over it still go through (that is
  # `nix run .#verify-lean`).
  #
  # NO NORMALISATION, deliberately.  A fresh extraction from the same lib.rs
  # reproduces every `Source: 'src/lib.rs', lines N:C-M:C` comment exactly —
  # this was verified against a real charon+aeneas run.  If this check fails
  # with a uniform line-number shift, the remedy is to re-run the extraction
  # and re-vendor (`nix run .#update-extracted`), NOT to weaken the check.
  #
  # COST: not cheap.  With no charon/aeneas binary cache this pulls in
  # charon's whole cargo tree and aeneas' ocaml5.2.1 tree — a dry run measured
  # ~400 derivations built from source, ~850 MiB fetched.  See flake.nix.
  ##########################################################################
  rust-extraction = runCommand "check-rust-extraction" { } ''
    set -euo pipefail
    ${splitAssert extractedLean 16}
    tail -n +"$body_from" ${extractedLean} > vendored-body.lean
    if ! cmp vendored-body.lean ${lean-from-rust}/MoltPetit.lean; then
      echo "" >&2
      echo "Spec/Rust.lean is NOT what charon+aeneas emit from rust/src/lib.rs." >&2
      echo "Diff (vendored vs freshly extracted):" >&2
      diff -u vendored-body.lean ${lean-from-rust}/MoltPetit.lean >&2 || true
      exit 1
    fi
    echo "OK: Spec/Rust.lean body == fresh charon+aeneas extraction"
    touch "$out"
  '';

  ##########################################################################
  # rust-extraction-modulo-loc — the deliberately weaker sibling.
  #
  # Identical to the above but canonicalises the `Source: '…', lines N:C-M:C`
  # comments.  Kept as a SEPARATE, differently-named check so a reviewer can
  # see which of the two passed: if only this one passes, the vendored file is
  # stale w.r.t. a source edit that moved lines but changed no definition.
  # The line is rewritten rather than deleted because four of them carry the
  # docstring terminator ` -/`.  After this substitution no other
  # line-number-bearing text remains in the emission, so the normalisation is
  # complete.
  ##########################################################################
  rust-extraction-modulo-loc = runCommand "check-rust-extraction-modulo-loc" { } ''
    set -euo pipefail
    ${splitAssert extractedLean 16}
    norm() {
      sed -E "s|^([[:space:]]*Source: '[^']*', lines )[0-9]+:[0-9]+-[0-9]+:[0-9]+|\1<LOC>|" "$1"
    }
    tail -n +"$body_from" ${extractedLean} > vendored-body.lean
    norm vendored-body.lean > a.lean
    norm ${lean-from-rust}/MoltPetit.lean > b.lean
    if ! cmp a.lean b.lean; then
      echo "Spec/Rust.lean differs from a fresh extraction beyond source locations." >&2
      diff -u a.lean b.lean >&2 || true
      exit 1
    fi
    echo "OK: Spec/Rust.lean body == fresh extraction, modulo Source: line numbers"
    touch "$out"
  '';

  ##########################################################################
  # ts-golden-digest — the recorded digest of the golden, on its own.
  #
  # Split out of `ts-emission-golden` so that it runs on every system,
  # including those where `thales` is not expressible and the real comparison
  # therefore cannot run at all.  On such a system this is the ONLY thing
  # standing between a reviewer and a silently rewritten golden.
  #
  # PROVES: nothing about faithfulness.  It is a tripwire (see the note on
  # `goldenDigest` above), and on Lean-capable systems `ts-emission-golden`
  # subsumes it completely.
  ##########################################################################
  ts-golden-digest = runCommand "check-ts-golden-digest" { } ''
    set -euo pipefail
    want=${goldenDigest}
    have=$(sha256sum < ${goldenEmitted} | cut -d' ' -f1)
    if [ "$have" != "$want" ]; then
      echo "tools/thales-reemission/MoltPetit.emitted.lean digest changed." >&2
      echo "  recorded $want" >&2
      echo "  found    $have" >&2
      echo "" >&2
      echo "'nix run .#update-extracted' rewrites this constant for you; if you" >&2
      echo "regenerated the golden some other way, update goldenDigest in" >&2
      echo "nix/checks.nix and pair the bump with a 'nix run .#verify-lean'." >&2
      exit 1
    fi
    echo "OK: golden digest matches the value recorded in nix/checks.nix"
    touch "$out"
  '';

  ##########################################################################
  # ts-emission-golden — byte-exact, no normalisation.
  #
  # PROVES: the pinned+patched thales, applied to the current moltPetit.ts,
  # reproduces tools/thales-reemission/MoltPetit.emitted.lean exactly; the
  # golden is not a hand-edited artefact; moltPetit.ts has not drifted from
  # what was emitted.
  # DOES NOT PROVE: that the emission is *correct* — the emitter has three
  # known semantic bugs (see tools/thales-reemission/README.md) and this check
  # would keep passing if a fourth appeared; nor that the golden is what the
  # Lean build consumes (it is not: that is Spec/TS.lean).
  ##########################################################################
  ts-emission-golden = runCommand "check-ts-emission-golden" { } ''
    set -euo pipefail
    if ! cmp ${goldenEmitted} ${lean-from-ts}/MoltPetit.lean; then
      echo "The checked-in golden is not what thales emits from moltPetit.ts." >&2
      diff -u ${goldenEmitted} ${lean-from-ts}/MoltPetit.lean >&2 || true
      exit 1
    fi
    echo "OK: tools/thales-reemission/MoltPetit.emitted.lean == fresh thales emission"
    touch "$out"
  '';

  ##########################################################################
  # ts-vendored-deviations — vendored == golden + a reviewed, checked-in delta.
  #
  # Spec/TS.lean is NOT the raw emission: it carries three
  # semantic fixes for emitter bugs plus some derive-clause and ordering
  # changes.  This check turns that delta into a machine-enforced ledger:
  # any NEW hand-edit fails until it is written into the patch, i.e. until it
  # is written down.
  #
  # Needs no Thales toolchain — only `patch` and `cmp` — so it is NOT gated on
  # `thales` being expressible.  Gating it there would have meant a green
  # `nix flake check` with zero enforcement on the vendored TS file wherever
  # the Lean binary release is not named.
  #
  # PROVES: byte-for-byte, that the vendored body is the golden with exactly
  # the checked-in patch applied.
  # DOES NOT PROVE: that the deviations are *right* (the patch is a ledger,
  # not a justification — `slot -> slot'` being TS-faithful is established by
  # the bridge lemmas ts_keyMonoOk, ts_validChainK_sound, ts_keyMonoFromTs,
  # ts_validateSuffixK_sound), nor that a reader can SEE all of them in the
  # diff: a moved block renders as delete+insert and hides edits inside
  # itself.  That last gap is what `ts-deviation-sites` covers.
  ##########################################################################
  ts-vendored-deviations =
    if deviationsPatch == null then
      runCommand "check-ts-vendored-deviations-MISSING-ARTEFACT" { } ''
        cat >&2 <<'MSG'
        FAIL: tools/thales-reemission/vendored-deviations.patch does not exist
              (or exists but is not tracked by git — a flake only sees
              git-tracked files, so `git add` it as well as creating it).

        This check compares Spec/TS.lean against
        tools/thales-reemission/MoltPetit.emitted.lean + a reviewed delta, and
        that delta has to be checked in.  Generate it once with:

            nix run .#update-deviations-patch
            git add tools/thales-reemission/vendored-deviations.patch

        then review the result (expect 122 lines / 6 hunks) and commit it.
        MSG
        exit 1
      ''
    else
      runCommand "check-ts-vendored-deviations"
        { nativeBuildInputs = [ gnupatch ]; } ''
        set -euo pipefail
        ${splitAssert emittedLean 57}
        cp ${goldenEmitted} MoltPetit.emitted.lean
        chmod +w MoltPetit.emitted.lean
        patch -p1 --fuzz=0 -i ${deviationsPatch}
        tail -n +"$body_from" ${emittedLean} > expected.lean
        if ! cmp MoltPetit.emitted.lean expected.lean; then
          echo "Spec/TS.lean is not golden + vendored-deviations.patch." >&2
          echo "Undocumented hand-edits (patched-golden vs vendored):" >&2
          diff -u MoltPetit.emitted.lean expected.lean >&2 || true
          exit 1
        fi
        echo "OK: Spec/TS.lean body == golden + vendored-deviations.patch"
        touch "$out"
      '';

  ##########################################################################
  # ts-deviation-sites — WHICH declarations the vendored file deviates at.
  #
  # `ts-vendored-deviations` proves the delta is exactly the checked-in patch.
  # It does not make that delta legible: the vendored file hoists six
  # declarations ~60 lines earlier, and unified diff renders that move as a
  # 32-line deletion plus a 32-line insertion whose halves are NOT identical.
  # Three real edits were hiding in there.
  #
  # So: split both files into top-level declarations, compare name by name,
  # and require that the set of declarations which differ is exactly the list
  # recorded above.  Reordering produces no output at all; a genuinely new
  # deviation site fails here even if someone has faithfully regenerated the
  # patch.  Needs no Thales toolchain.
  #
  # PROVES: the deviations touch exactly nine named declarations, and the
  # declaration NAME SETS of golden and vendored are identical (nothing added,
  # nothing dropped).
  # DOES NOT PROVE: that the edits within those nine are the intended ones —
  # that is the patch's job, and ultimately the bridge lemmas'.
  ##########################################################################
  ts-deviation-sites = runCommand "check-ts-deviation-sites"
    { nativeBuildInputs = [ gawk ]; } ''
    set -euo pipefail
    ${splitAssert emittedLean 57}
    mkdir -p golden vendored
    tail -n +"$body_from" ${emittedLean} > vendored-body.lean
    awk -v dir=golden -f ${declSplitAwk} ${goldenEmitted}
    awk -v dir=vendored -f ${declSplitAwk} vendored-body.lean

    sort ${removedSites} > removed.names
    sort golden/.names > golden-all.names
    if [ -n "$(comm -13 golden-all.names removed.names)" ]; then
      echo "FAIL: a recorded removal is not in the golden:" >&2
      comm -13 golden-all.names removed.names >&2
      exit 1
    fi
    comm -23 golden-all.names removed.names > golden.names
    sort vendored/.names > vendored.names
    if ! cmp -s golden.names vendored.names; then
      echo "FAIL: golden and vendored declare different top-level names." >&2
      echo "      A declaration was added to or removed from the vendored file;" >&2
      echo "      that is never a sanctioned deviation." >&2
      diff -u golden.names vendored.names >&2 || true
      exit 1
    fi

    : > differing.txt
    while read -r name; do
      if ! cmp -s "golden/$name" "vendored/$name"; then
        echo "$name" >> differing.txt
      fi
    done < golden.names

    sort ${deviationSites} > want-sites.txt
    if ! cmp -s differing.txt want-sites.txt; then
      echo "FAIL: Spec/TS.lean deviates from the golden at a" >&2
      echo "      different set of declarations than nix/checks.nix records." >&2
      echo "      (- expected, + actual):" >&2
      diff -u want-sites.txt differing.txt >&2 || true
      echo "" >&2
      echo "A NEW site here is a new sanctioned deviation.  Do not just add the" >&2
      echo "name: write it into the header of Spec/TS.lean, add it" >&2
      echo "to deviationSites in nix/checks.nix, and say why it is TS-faithful." >&2
      exit 1
    fi

    echo "Per-declaration deviations (order-insensitive):"
    while read -r name; do
      echo "--- $name"
      diff -u "golden/$name" "vendored/$name" || true
    done < differing.txt
    echo "OK: deviations confined to the $(wc -l < want-sites.txt) recorded declarations"
    touch "$out"
  '';

  ##########################################################################
  # thales-fixes-patch — the emitter patch is what was reviewed upstream.
  #
  # `nix/thales.nix` applies tools/thales-reemission/thales-fixes.patch to the
  # pinned Thales before building it, so this patch DEFINES the emission that
  # `ts-emission-golden` blesses.  Every other link in the TS chain is pinned
  # by revision; this one is pinned by review, and a fourth hunk in it would
  # change the emitted definitions the bridge lemmas are about while every
  # other check stayed green.
  #
  # Two guards, neither of them a cryptographic pin (this file is as
  # repo-controlled as the patch):
  #   1. the recorded digest, so a change is a two-file diff;
  #   2. the change content must equal the union of the three reviewed
  #      upstream PR patches in tools/thales-reemission/upstream-prs/patches,
  #      so a hunk that was never proposed upstream fails here.
  ##########################################################################
  thales-fixes-patch = runCommand "check-thales-fixes-patch" { } ''
    set -euo pipefail
    want=${thalesFixesDigest}
    have=$(sha256sum < ${thalesFixesPatch} | cut -d' ' -f1)
    if [ "$have" != "$want" ]; then
      echo "tools/thales-reemission/thales-fixes.patch changed." >&2
      echo "  recorded $want" >&2
      echo "  found    $have" >&2
      echo "This patch decides what thales emits.  Bump thalesFixesDigest in" >&2
      echo "nix/checks.nix only together with a re-review of the emission." >&2
      exit 1
    fi

    grep '^[+-][^+-]' ${thalesFixesPatch} | sort > applied.txt
    cat ${upstreamPrPatches}/*.patch | grep '^[+-][^+-]' | sort > proposed.txt
    if ! cmp -s applied.txt proposed.txt; then
      echo "FAIL: thales-fixes.patch does not carry exactly the changes of the" >&2
      echo "      reviewed upstream PR patches in upstream-prs/patches/." >&2
      diff -u proposed.txt applied.txt >&2 || true
      exit 1
    fi

    a=$(grep -c '^@@' ${thalesFixesPatch})
    b=$(cat ${upstreamPrPatches}/*.patch | grep -c '^@@')
    if [ "$a" != "$b" ]; then
      echo "FAIL: thales-fixes.patch has $a hunks, upstream-prs/patches has $b." >&2
      exit 1
    fi

    echo "OK: thales-fixes.patch == the three reviewed upstream PRs ($a hunks)"
    touch "$out"
  '';

  ##########################################################################
  # pin-consistency — the cross-file equalities the comments assert.
  #
  # Five invariants held this flake together as PROSE.  Each is a pure string
  # comparison over already-fetched sources, so this check is free, and each
  # one is a real hazard if it breaks:
  #
  #  1. aeneas' own `charon-pin` == our locked charon rev.  We override aeneas'
  #     charon input with `follows`, so bumping `charon` alone would silently
  #     build aeneas against a charon-ml it was never pinned against — LLBC
  #     skew, surfacing much later as a confusing aeneas failure.
  #  2. lakefile.toml's aeneas rev == our locked aeneas rev.  These are the
  #     extraction BINARY and the Lean LIBRARY it emits against; desyncing
  #     them breaks the proofs while `rust-extraction` still passes.
  #  3. thales' own `lean-toolchain` == the Lean release we build it with.
  #  4/5. thales' lake-manifest revs == our batteries / lean-regex pins.
  ##########################################################################
  pin-consistency = runCommand "check-pin-consistency"
    { nativeBuildInputs = [ jq ]; } ''
    set -euo pipefail
    fail=0
    chk() { # name expected actual
      if [ "$2" != "$3" ]; then
        echo "FAIL: $1" >&2
        echo "   expected: $2" >&2
        echo "   actual:   $3" >&2
        fail=1
      else
        echo "ok: $1 = $2"
      fi
    }

    chk "aeneas charon-pin vs locked charon rev" \
      "${charonRev}" \
      "$(grep -o '[0-9a-f]\{40\}' ${aeneasSrc}/charon-pin | head -1)"

    chk "lakefile.toml aeneas rev vs locked aeneas rev" \
      "${aeneasRev}" \
      "$(sed -n '/name = "aeneas"/,/^$/p' ${lakefileToml} | grep -o '[0-9a-f]\{40\}' | head -1)"

    chk "thales lean-toolchain vs the Lean release we build it with" \
      "leanprover/lean4:v${leanVersion}" \
      "$(tr -d '[:space:]' < ${thalesSrc}/lean-toolchain)"

    chk "thales lake-manifest batteries rev vs our pin" \
      "${batteriesRev}" \
      "$(jq -r '.packages[] | select(.name == "batteries") | .rev' ${thalesSrc}/lake-manifest.json)"

    chk "thales lake-manifest Regex rev vs our lean-regex pin" \
      "${leanRegexRev}" \
      "$(jq -r '.packages[] | select(.name == "Regex") | .rev' ${thalesSrc}/lake-manifest.json)"

    if [ "$fail" != "0" ]; then
      echo "" >&2
      echo "One of the pins the flake's comments assert has drifted.  Fix the" >&2
      echo "input revs in flake.nix; do not relax this check." >&2
      exit 1
    fi
    echo "OK: all cross-file pins agree"
    touch "$out"
  '';

  ##########################################################################
  # tsc — the TypeScript source typechecks under --strict.
  #
  # There is no tsconfig.json in the repo, so every flag is on the command
  # line.  `--target ES2020` is load-bearing, not cosmetic: moltPetit.ts is
  # bigint-only by design and the default ES5 target rejects bigint literals.
  # Hermetic, and cheap: two derivations, nothing fetched.
  ##########################################################################
  tsc = runCommand "check-tsc"
    { nativeBuildInputs = [ typescript nodejs ]; } ''
    set -euo pipefail
    export HOME="$TMPDIR"
    cp ${tsSrc}/moltPetit.ts .
    tsc --strict --noEmit --target ES2020 --lib ES2020 moltPetit.ts
    echo "OK: moltPetit.ts typechecks under --strict"
    touch "$out"
  '';

  ##########################################################################
  # cargo — the Rust crate typechecks.
  #
  # `molt_petit` has zero dependencies and gitignores Cargo.lock, so
  # `--offline` is genuinely sufficient and this is fully hermetic.  This
  # STABLE cargo is for `cargo check` only; it is NOT the toolchain the Charon
  # extraction uses (that is charon's own pinned nightly, supplied by the
  # charon wrapper inside `lean-from-rust`).
  ##########################################################################
  cargo = stdenv.mkDerivation {
    name = "check-cargo";
    src = rustCrateSrc;
    nativeBuildInputs = [ cargo rustc ];
    dontConfigure = true;
    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export CARGO_HOME="$TMPDIR/cargo"
      export CARGO_TARGET_DIR="$TMPDIR/target"
      cargo check --offline
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      echo "OK: cargo check passes"
      touch "$out"
      runHook postInstall
    '';
  };

  ##########################################################################
  # ts-toolchain-unavailable — a visible marker, not a check.
  #
  # Exposed only on systems where `thales` is not expressible (no named Lean
  # 4.29.0 release asset).  Without it `nix flake check` there exits 0 having
  # silently skipped `ts-emission-golden`, and the exit status reads as "all
  # checks passed" for a run that never re-emitted the TypeScript at all.
  ##########################################################################
  ts-toolchain-unavailable = runCommand "check-ts-toolchain-unavailable" { } ''
    cat <<'MSG'
    NOTE: this system has no Lean 4.29.0 binary release named in flake.nix, so
    `thales` cannot be built here and `ts-emission-golden` did NOT run.  The
    TypeScript half was covered only by the toolchain-free checks
    (ts-vendored-deviations, ts-deviation-sites, ts-golden-digest, tsc):
    the vendored file was tied to the checked-in golden, but the golden was
    NOT re-derived from moltPetit.ts.  Run `nix flake check` on x86_64-linux
    for that.
    MSG
    touch "$out"
  '';
}
