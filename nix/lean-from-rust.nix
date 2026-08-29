# `rust/src/lib.rs`  --charon-->  molt_petit.llbc  --aeneas-->  MoltPetit.lean
#
# This is exactly what `rust/extract.sh` does, minus the in-tree vendoring step
# (see the `update-extracted` app for that).  Output: `$out/MoltPetit.lean`,
# the 995-line Aeneas emission that `Rust/Extracted.lean` carries below its
# 16-line vendor header.
#
# HERMETICITY: fully offline and fully pinned.  `charon` here is the *wrapped*
# binary from the upstream charon flake at 9dd7f23c… (= charon 0.1.212); its
# wrapper already puts charon's own pinned rust toolchain
# (nightly-2026-06-01 with rustc-dev) on PATH and sets
# CHARON_TOOLCHAIN_IS_IN_PATH, so we must NOT add a second toolchain here.
# `aeneas` is the upstream aeneas flake's package at bf13c42e… — the same rev
# the repo's `lakefile.toml` requires for the Lean-side runtime model.
#
# The crate has zero dependencies and no committed Cargo.lock, so
# `cargo` needs no registry access; CARGO_NET_OFFLINE makes that a hard
# guarantee rather than an assumption.  (This is also why charon's own
# `extractCrateWithCharon` helper is not used: it goes through `crane`, which
# requires a Cargo.lock that this crate deliberately gitignores.)
#
# NOT REPRODUCIBLE BIT-FOR-BIT: the intermediate `.llbc` differs run to run
# (embedded paths/ordering).  The *Lean* output is stable — that is the
# property `checks.rust-extraction` pins.
{ lib
, stdenv
, charon
, aeneas
, rustCrateSrc
}:

stdenv.mkDerivation {
  pname = "molt-petit-lean-from-rust";
  version = "0.1.0";

  src = rustCrateSrc;

  nativeBuildInputs = [ charon aeneas ];

  dontConfigure = true;

  buildPhase = ''
    runHook preBuild

    export HOME="$TMPDIR"
    export CARGO_HOME="$TMPDIR/cargo"
    export CARGO_TARGET_DIR="$TMPDIR/target"
    export CARGO_NET_OFFLINE=true

    # Rust -> LLBC.  `--preset=aeneas` is the option set Aeneas expects.
    charon cargo --preset=aeneas

    # LLBC -> Lean.  Flags are single-dash at this Aeneas rev.
    mkdir -p lean-out
    aeneas molt_petit.llbc -backend lean -dest lean-out -no-progress-bar

    runHook postBuild
  '';

  # Assert the emitted SET, not just the one file we want.  Aeneas splits its
  # output when the crate demands it — an opaque function makes it emit a
  # `FunsExternal_Template.lean` as well, and Types/Funs can split too.  Any
  # such file would be generated Lean that no check covers, while
  # `checks.rust-extraction` went on passing on MoltPetit.lean alone.
  installPhase = ''
    runHook preInstall
    emitted=$(cd lean-out && ls | sort | tr '\n' ' ')
    if [ "$emitted" != "MoltPetit.lean " ]; then
      echo "aeneas emitted more than MoltPetit.lean: $emitted" >&2
      echo "Every emitted file is generated Lean and needs a check; add one" >&2
      echo "in nix/checks.nix before widening this assertion." >&2
      exit 1
    fi
    mkdir -p "$out"
    cp lean-out/MoltPetit.lean "$out/MoltPetit.lean"
    runHook postInstall
  '';

  meta = with lib; {
    description = "Charon+Aeneas extraction of the molt_petit Rust crate to Lean 4";
  };
}
