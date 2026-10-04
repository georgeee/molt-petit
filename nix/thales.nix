# Thales — the TypeScript-subset -> Lean 4 emitter that produced
# `Spec/TS.lean`.
#
# Pinned at 55b03fb3fbbcca615cb438b2492d6a1c115d0394 (a Lean 4 / Lake project;
# it has NO flake.nix of its own, hence `flake = false` on the input) and built
# with the repo's own `tools/thales-reemission/thales-fixes.patch` applied.
# Without that patch `moltPetit.ts` does not even parse — see the patch's three
# hunks and `tools/thales-reemission/README.md`.
#
# HERMETICITY: fully offline.  Lake normally materialises `require`d packages by
# cloning them, which needs the network.  We bypass that with Lake's
# `--packages=<file>` override (documented in `lake --help` as "JSON file of
# package entries that override the manifest"): entries of `type: "path"` take a
# branch in `Lake/Load/Materialize.lean` that performs no git operations at all.
#
# DO NOT "vendor" the deps into `.lake/packages` instead — that path is verified
# broken AND destructive: with no `.git` in the copied tree Lake decides the
# remote URL changed, `removeDirAll`s the vendored directory, and then fails
# trying to clone.  (`lake check-build` still exits 0 in that broken state, so it
# is not a valid smoke test.)
#
# Note: `dir` on a path entry has no `subDir` field, so the Regex entry must
# point at `<lean-regex>/regex`, the directory that actually holds its
# `lakefile.toml`.  Neither dep is ever compiled — Thales imports only `Std.*`
# (core Lean) and its own modules — they only have to be *resolvable*.
{ lib
, stdenv
, autoPatchelfHook
, git
, lean4
, thalesSrc
, batteriesSrc
, leanRegexSrc
, thalesFixesPatch
}:

stdenv.mkDerivation {
  pname = "thales";
  version = "unstable-2026-06-30-55b03fb";

  src = thalesSrc;
  patches = [ thalesFixesPatch ];

  nativeBuildInputs = [ lean4 git autoPatchelfHook ];
  # What the built `thales` ACTUALLY needs at runtime: `readelf -d` on the
  # binary produced by this exact recipe lists only libm, libdl, libgcc_s,
  # libpthread, libc and the loader — Lean is linked STATICALLY into the
  # emitter, so there is no libleanshared.so dependency.  `stdenv.cc.cc.lib`
  # supplies libgcc_s; stdenv supplies the rest.  `lean4` stays here because
  # autoPatchelfHook is cheap and a future Lean release could go back to
  # shared linking, not because anything links against it today.
  buildInputs = [ lean4 stdenv.cc.cc.lib ];

  # Lake consults elan when it is on PATH; point it at nothing so it uses the
  # `lean`/`leanc` we put on PATH instead.  (The toolchain we supply is exactly
  # the `leanprover/lean4:v4.29.0` named by Thales' own `lean-toolchain`.)
  ELAN_HOME = "/no-elan-here";

  buildPhase = ''
    runHook preBuild

    export HOME="$TMPDIR"

    # Package-entry overrides.  Schema is Lake's own `Manifest.saveEntries`
    # format; revs here are the ones pinned in Thales' lake-manifest.json.
    cat > packages-override.json <<EOF
    {"schemaVersion": "1.1.0",
     "packages":
     [{"name": "batteries", "scope": "", "inherited": false,
       "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
       "type": "path", "dir": "${batteriesSrc}"},
      {"name": "Regex", "scope": "", "inherited": false,
       "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
       "type": "path", "dir": "${leanRegexSrc}/regex"}]}
    EOF

    # --no-cache: never try to download a Reservoir build cache.
    lake --no-cache --packages=packages-override.json build

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 .lake/build/bin/thales "$out/bin/thales"
    runHook postInstall
  '';

  meta = with lib; {
    description = "TypeScript-subset to Lean 4 emitter (patched, pinned)";
    homepage = "https://github.com/jessealama/thales";
    platforms = [ "x86_64-linux" "aarch64-linux" ];
    mainProgram = "thales";
  };
}
