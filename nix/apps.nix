# Apps — the deliberately IMPURE half of this flake.
#
# Everything here operates on the user's checkout rather than on a store path,
# because it either needs the network or needs to write files back into the
# tree.  We do not dress these up as derivations: a derivation that needed
# `lake exe cache get` would either fail in the sandbox or silently lie about
# being hermetic.
{ lib
, writeShellApplication
, coreutils
, gnused
, gnugrep
, diffutils
, gnupatch
, elan
, git
, curl
, cacert
, lean-from-rust
, lean-from-ts
}:

let
  # Every app must run at the repo root; refuse politely otherwise.
  atRepoRoot = ''
    if [ ! -f lakefile.toml ] || [ ! -f moltPetit.ts ]; then
      echo "error: run this from the root of the molt-petit checkout" >&2
      exit 1
    fi
  '';

  # A `git+file` flake sees git-TRACKED files only.  So the derivations these
  # apps read from — `lean-from-rust`, `lean-from-ts` — were built from a
  # snapshot that EXCLUDES anything untracked.  Re-vendoring in that state
  # writes an extraction of a source tree that is not the one on disk, and
  # `checks.rust-extraction` then certifies the result as faithful.  Verified:
  # adding an untracked rust/src/*.rs leaves lean-from-rust's drvPath
  # byte-identical, while a tracked edit changes it.
  #
  # Refuse instead.  This is also what catches the bootstrap case where
  # flake.nix and nix/ themselves are still untracked.
  noUntrackedSources = ''
    untracked=$(git ls-files --others --exclude-standard -- \
      flake.nix flake.lock nix rust moltPetit.ts tools/thales-reemission \
      Rust MoltPetit lakefile.toml || true)
    if [ -n "$untracked" ]; then
      echo "error: untracked files are INVISIBLE to the flake — nix builds from" >&2
      echo "       the git-tracked tree only, so re-vendoring now would extract" >&2
      echo "       a source tree that is not the one on disk.  git add these first:" >&2
      while IFS= read -r u; do echo "       $u" >&2; done <<< "$untracked"
      exit 1
    fi
  '';

  # The four Lean libraries.  Named explicitly and NOT left to lake's
  # `defaultTargets`: the axiom guards in Rust/Axioms.lean, Thales and
  # Molt/Axioms.lean only elaborate when their library is built, and
  # `defaultTargets` is exactly the field most likely to drift.
  leanTargets = "MoltPetit Rust Thales Molt";
in
{
  ##########################################################################
  # verify-lean — build the repo's own Lean development (all 4 libs, hence
  # all the axiom guards).
  #
  # This is the SOUNDNESS half of the pairing described at the top of
  # flake.nix.  `nix flake check` proves the vendored Lean is what the pinned
  # toolchains emit; only this proves the theorems still go through over it.
  #
  # IMPURE BY NECESSITY, three separate reasons, none of them fixable here:
  #  1. lean-toolchain pins `leanprover/lean4:v4.30.0-rc2`.  nixpkgs' lean4 is
  #     4.30.0 — a different release, not an rc — so nixpkgs cannot supply it,
  #     and elan needs network + a writable ELAN_HOME on first run.
  #  2. Mathlib's oleans come from `lake exe cache get`, which is ~8300
  #     individually-addressed .ltar fetches with no single upstream archive
  #     and no published aggregate hash.  Building mathlib from source instead
  #     is a multi-hour, ~6 GB derivation.
  #  3. Lake insists on materialising .lake/packages itself for all 10
  #     resolved packages and re-checks the manifest as it goes.
  ##########################################################################
  verify-lean = writeShellApplication {
    name = "verify-lean";
    meta.description = "Build the four Lean libraries of this repo — the soundness half of `nix flake check` (needs network: elan + mathlib olean cache)";
    runtimeInputs = [ elan git curl cacert coreutils gnused gnugrep ];
    text = ''
      ${atRepoRoot}
      export SSL_CERT_FILE="''${SSL_CERT_FILE:-${cacert}/etc/ssl/certs/ca-bundle.crt}"
      export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
      export PATH="$ELAN_HOME/bin:$PATH"

      toolchain=$(cat lean-toolchain)
      echo "==> elan toolchain install $toolchain"
      elan toolchain install "$toolchain"

      echo "==> lake exe cache get   (downloads mathlib oleans; needs network)"
      lake exe cache get

      echo "==> lake build ${leanTargets}"
      lake build ${leanTargets}

      echo "OK: all four Lean libraries built (axiom guards elaborated)"
    '';
  };

  ##########################################################################
  # verify-lean-offline — the same trace check with no network at all.
  #
  # `lake build --no-build` makes lake FAIL rather than compile anything, so
  # exit 0 means every job is trace-current.  Only useful when .lake is
  # already populated, but it is the one form of Lean verification that needs
  # nothing from the outside world.
  ##########################################################################
  verify-lean-offline = writeShellApplication {
    name = "verify-lean-offline";
    meta.description = "Trace-only check that the four Lean libraries are up to date (no network)";
    runtimeInputs = [ elan git coreutils ];
    text = ''
      ${atRepoRoot}
      export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
      export PATH="$ELAN_HOME/bin:$PATH"
      lake build --no-build ${leanTargets}
      echo "OK: all targets trace-current (nothing needed rebuilding)"
    '';
  };

  ##########################################################################
  # update-extracted — regenerate the vendored Lean sources in-tree.
  #
  # The generators themselves are the hermetic derivations; only the writing
  # back into the working tree is impure.  Note that the flake's source is the
  # GIT-TRACKED tree, not the working tree, so this regenerates from what is
  # committed/staged — hence the untracked-file refusal above.
  #
  # It OVERWRITES FOUR TRACKED FILES:
  #   Spec/Rust.lean                              header + fresh aeneas body
  #   tools/thales-reemission/MoltPetit.emitted.lean   fresh thales emission
  #   Spec/TS.lean                        header + (golden + deltas)
  #   nix/checks.nix                                   the goldenDigest constant
  # It refuses if any of them has uncommitted edits, so the regeneration is
  # always a reviewable diff against a known base.  Set
  # UPDATE_EXTRACTED_FORCE=1 to override that.
  #
  # Every precondition is checked BEFORE the first write.  An earlier version
  # rewrote two files and only then discovered vendored-deviations.patch was
  # missing, printed "skipped", and exited 0 — a caller trusting the exit
  # status believed the tree was fully re-vendored when it was two-thirds
  # re-vendored and internally inconsistent.
  ##########################################################################
  update-extracted = writeShellApplication {
    name = "update-extracted";
    meta.description = "Regenerate the vendored Lean sources in-tree from the pinned toolchains (OVERWRITES 4 tracked files)";
    runtimeInputs = [ coreutils gnused gnugrep diffutils gnupatch git ];
    text = ''
      ${atRepoRoot}
      ${noUntrackedSources}

      targets="Spec/Rust.lean Spec/TS.lean \
               tools/thales-reemission/MoltPetit.emitted.lean nix/checks.nix"

      # ---- preconditions, ALL of them, before anything is written ---------
      dev=tools/thales-reemission/vendored-deviations.patch
      if [ ! -f "$dev" ]; then
        echo "error: $dev does not exist." >&2
        echo "  It is the only written-down record of the reviewed hand-edits to" >&2
        echo "  Spec/TS.lean, and this app cannot regenerate that" >&2
        echo "  file without it.  Create it with:" >&2
        echo "      nix run .#update-deviations-patch && git add $dev" >&2
        exit 1
      fi

      for f in $targets; do
        if [ ! -f "$f" ]; then
          echo "error: $f is missing" >&2
          exit 1
        fi
      done

      if [ "''${UPDATE_EXTRACTED_FORCE:-0}" != "1" ]; then
        # shellcheck disable=SC2086
        if ! git diff --quiet -- $targets; then
          echo "error: these files have uncommitted edits; commit or stash first" >&2
          echo "       (or set UPDATE_EXTRACTED_FORCE=1 to overwrite them anyway):" >&2
          # shellcheck disable=SC2086
          git diff --name-only -- $targets | sed 's/^/       /' >&2
          exit 1
        fi
      fi

      n=$(grep -c '^-/$' Spec/Rust.lean || true)
      if [ "$n" != "1" ]; then
        echo "error: Spec/Rust.lean must contain exactly one bare '-/' line (found $n)" >&2
        exit 1
      fi
      m=$(grep -c '^-/$' Spec/TS.lean || true)
      if [ "$m" != "1" ]; then
        echo "error: Spec/TS.lean must contain exactly one bare '-/' line (found $m)" >&2
        exit 1
      fi

      # ---- Rust: keep the vendor header, replace the body -----------------
      { sed -n '1,/^-\/$/p' Spec/Rust.lean
        cat ${lean-from-rust}/MoltPetit.lean
      } > Spec/Rust.lean.new
      mv Spec/Rust.lean.new Spec/Rust.lean
      echo "regenerated Spec/Rust.lean"

      # ---- TS: the raw emission (the golden) ------------------------------
      cp ${lean-from-ts}/MoltPetit.lean tools/thales-reemission/MoltPetit.emitted.lean
      chmod u+w tools/thales-reemission/MoltPetit.emitted.lean
      echo "regenerated tools/thales-reemission/MoltPetit.emitted.lean"

      # ---- the recorded digest of the golden ------------------------------
      # checks.ts-golden-digest pins this value; rewriting it here keeps the
      # bump a reviewable diff hunk instead of a red check plus a manual chore.
      d=$(sha256sum < tools/thales-reemission/MoltPetit.emitted.lean | cut -d' ' -f1)
      sed -i -E "s|^(  goldenDigest = \")[0-9a-f]{64}(\";)$|\1$d\2|" nix/checks.nix
      if ! grep -q "^  goldenDigest = \"$d\";$" nix/checks.nix; then
        echo "error: could not rewrite goldenDigest in nix/checks.nix." >&2
        echo "       Expected a line of the form:  goldenDigest = \"<64 hex>\";" >&2
        echo "       Set it to $d by hand." >&2
        exit 1
      fi
      echo "recorded goldenDigest = $d in nix/checks.nix"

      # ---- TS: the vendored file = header + (golden + reviewed deltas) ----
      root=$PWD
      work=$(mktemp -d)
      trap 'rm -rf "$work"' EXIT
      cp tools/thales-reemission/MoltPetit.emitted.lean "$work/MoltPetit.emitted.lean"
      chmod u+w "$work/MoltPetit.emitted.lean"
      ( cd "$work" && patch -p1 --fuzz=0 -i "$root/$dev" )
      { sed -n '1,/^-\/$/p' Spec/TS.lean
        cat "$work/MoltPetit.emitted.lean"
      } > Spec/TS.lean.new
      mv Spec/TS.lean.new Spec/TS.lean
      echo "regenerated Spec/TS.lean"

      echo ""
      echo "Now review the diff, then run 'nix flake check' AND 'nix run .#verify-lean':"
      echo "the checks prove the vendored Lean is what the toolchains emit; only"
      echo "verify-lean proves the theorems still hold over it."
    '';
  };

  ##########################################################################
  # update-deviations-patch — (re)generate the ledger of reviewed hand-edits
  # to Spec/TS.lean.
  #
  # The explicit -L labels are load-bearing: without them `diff -u` writes
  # mtimes into the patch header and the checked-in file churns on every
  # regeneration.
  #
  # The header/body split is DERIVED, not hardcoded.  A hardcoded `tail -n
  # +54` here (while the checking side only *asserted* 53) would, after any
  # legitimate header edit, silently write a patch containing header prose and
  # then fail the check with a confusing diff.
  ##########################################################################
  update-deviations-patch = writeShellApplication {
    name = "update-deviations-patch";
    meta.description = "Regenerate the ledger of reviewed hand-edits to Spec/TS.lean";
    runtimeInputs = [ coreutils gnused gnugrep diffutils ];
    text = ''
      ${atRepoRoot}
      m=$(grep -c '^-/$' Spec/TS.lean || true)
      if [ "$m" != "1" ]; then
        echo "error: Spec/TS.lean must contain exactly one bare '-/' line (found $m)" >&2
        exit 1
      fi
      out=tools/thales-reemission/vendored-deviations.patch
      set +e
      diff -u -L a/MoltPetit.emitted.lean -L b/MoltPetit.emitted.lean \
        tools/thales-reemission/MoltPetit.emitted.lean \
        <(sed '1,/^-\/$/d' Spec/TS.lean) > "$out"
      rc=$?
      set -e
      if [ "$rc" -gt 1 ]; then
        echo "error: diff failed with status $rc" >&2
        exit "$rc"
      fi
      echo "wrote $out ($(wc -l < "$out") lines) — review every hunk before committing"
      echo ""
      echo "REMEMBER: 'git add $out'.  A flake only sees git-tracked files, so an"
      echo "untracked ledger leaves checks.ts-vendored-deviations in its"
      echo "MISSING-ARTEFACT form and nix flake check stays red."
      echo ""
      echo "Note that a unified diff renders a moved declaration as delete+insert"
      echo "and can hide real edits inside it.  checks.ts-deviation-sites is the"
      echo "order-insensitive companion; if it fails, a NEW declaration deviates."
    '';
  };
}
