# The official leanprover/lean4 *binary release*, unpacked and patchelf'd.
#
# WHY A BINARY RELEASE AND NOT nixpkgs' `lean4`:
#   * Thales pins `leanprover/lean4:v4.29.0` in its `lean-toolchain`, and
#     nixpkgs' `lean4` is 4.30.0.  A nixpkgs rev that carries exactly 4.29.0
#     does exist (`23c1607..062cd7a`, i.e. 2026-03-28..2026-04-18) but it is a
#     from-source CMake build of Lean with nixpkgs-specific patches, it costs
#     hours of compute, and it drags a second nixpkgs closure into this flake.
#   * The release tarball is the *same artifact* elan installs, which is what
#     produced the reference emission we compare against.  Using it keeps the
#     nix build bit-comparable with the elan build.
#
# TRUST: fixed-output derivation, hash pinned below.  Fully hermetic.
{ lib
, stdenv
, fetchzip
, autoPatchelfHook
, zstd
, version
, url
, hash
}:

stdenv.mkDerivation {
  pname = "lean4-bin";
  inherit version;

  # `fetchzip` strips the single `lean-<version>-<platform>/` top-level
  # directory, so `$src/bin/lean` is the interpreter.  Upstream ships
  # `.tar.zst`, hence `zstd` in the unpacker's nativeBuildInputs.
  #
  # The `name` is deliberate: an unnamed fetchzip lands in the store as plain
  # `source`, so a wrong hash reports "hash mismatch in fixed-output
  # derivation ...-source.drv" with nothing pointing back at flake.nix.
  src = fetchzip {
    name = "lean-${version}-release";
    inherit url hash;
    nativeBuildInputs = [ zstd ];
  };

  # Upstream ships plain ELF executables with interpreter
  # /lib64/ld-linux-x86-64.so.2 and no wrappers.  autoPatchelfHook rewrites
  # the interpreter and RPATHs; `stdenv.cc.cc.lib` supplies libstdc++/libgcc
  # for the bundled clang/lld that `leanc` shells out to.
  nativeBuildInputs = [ autoPatchelfHook ];
  buildInputs = [ stdenv.cc.cc.lib ];

  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -r ./* "$out/"
    runHook postInstall
  '';

  meta = with lib; {
    description = "Lean 4 ${version} official binary release";
    homepage = "https://github.com/leanprover/lean4";
    license = licenses.asl20;
    platforms = [ "x86_64-linux" "aarch64-linux" ];
    mainProgram = "lean";
  };
}
