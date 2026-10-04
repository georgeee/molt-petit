{
  description = "MoltPetit: pinned Rust->Lean (Charon+Aeneas) and TypeScript->Lean (Thales) extraction toolchains, plus the faithfulness checks that tie the vendored Lean sources to them.";

  ############################################################################
  # READ FIRST — three things that are easy to get wrong.
  #
  # 1. WHAT `nix flake check` PROVES.  Faithfulness only: the vendored Lean
  #    files are what the pinned toolchains emit from the current sources.  It
  #    says NOTHING about the proofs.  A semantics-altering edit to
  #    rust/src/lib.rs or moltPetit.ts followed by `nix run .#update-extracted`
  #    passes every check here.  Pair it with `nix run .#verify-lean`, which
  #    re-elaborates the four Lean libraries and their axiom guards but needs
  #    the network and therefore cannot be a check.
  #
  # 2. WHAT IT COSTS.  Not a smoke test.  `checks.rust-extraction` alone builds
  #    charon's cargo tree and aeneas' ocaml 5.2.1 tree — a `--dry-run`
  #    measured ~400 derivations from source, ~850 MiB fetched / ~4 GiB
  #    unpacked, because neither upstream flake declares a public substituter.
  #    `checks.thales`-side work adds a 537 MB Lean release download.  The
  #    cheap ones (`tsc`, `cargo`, `pin-consistency`, the three TS ledger
  #    checks) are two derivations and no fetch; run those alone with
  #    `nix build .#checks.x86_64-linux.{tsc,cargo,ts-deviation-sites,...}`.
  #
  # 3. THE LOCK IS PART OF THE PIN.  The inputs below are rev-pinned, but they
  #    drag in 10 transitive lock nodes (16 in all: crane, fstar, rust-overlay,
  #    flake-utils, two more nixpkgs, ...) of which several float in their
  #    `original` ref and are resolved ONLY by flake.lock.  `flake.lock` must
  #    be committed alongside this file, and so must everything under `nix/`:
  #    a `git+file` flake sees git-TRACKED files only, so an untracked
  #    nix/*.nix or an untracked generated artefact is invisible to nix and
  #    silently takes the "missing" branch.
  ############################################################################

  ############################################################################
  # INPUTS — every direct input is pinned by revision.
  #
  # We do NOT make charon/aeneas follow our nixpkgs: each upstream flake locks
  # a nixpkgs it was tested against, and overriding it would both deviate from
  # the combination upstream CI exercises and throw away binary-cache hits.
  # Our own nixpkgs is used only for the small stuff (tsc, cargo, elan, patch).
  ############################################################################
  inputs = {
    # nixos-unstable channel commit, 2026-08-27.  Pinned by rev, not a branch.
    nixpkgs.url = "github:NixOS/nixpkgs/c27cdad491a991b11ed731760aa2ef8db0cb0410";

    # Charon 0.1.212 — the rev `rust/extract.sh` names and the rev Aeneas'
    # own `charon-pin` file records.
    charon = {
      url = "github:AeneasVerif/charon/9dd7f23c8458b2366ce0b5ca7529c5ad4c5fb350";
    };

    # Aeneas at the rev `lakefile.toml` requires for the Lean-side runtime
    # model, so one rev pins both halves of the Rust path.
    #
    # About the `follows`: Aeneas' *lock* already pins charon at exactly
    # 9dd7f23c…, the same rev as ours — it is only the `original` URL that has
    # no rev (`github:aeneasverif/charon`).  So this override is a no-op today
    # and is kept for a different reason: without it, `charon` (the binary that
    # writes the .llbc) and the charon-ml inside `aeneas` (which reads it)
    # would be two independently-updatable pins, and LLBC skew between them is
    # silent.  With it they are one pin — and because the override can now
    # disagree with what Aeneas was tested against, `checks.pin-consistency`
    # asserts `${aeneas}/charon-pin == charon.rev` so bumping one without the
    # other fails loudly instead of drifting.
    aeneas = {
      url = "github:AeneasVerif/aeneas/bf13c42e7c34d07fc396baffad39c93023b12914";
      inputs.charon.follows = "charon";
    };

    # Thales is a Lean 4 / Lake project with no flake.nix of its own
    # (verified: `<thales>/flake.nix` does not exist at this rev), so it comes
    # in as a plain source tree.
    thales-src = {
      url = "github:jessealama/thales/55b03fb3fbbcca615cb438b2492d6a1c115d0394";
      flake = false;
    };

    # Thales' two Lake dependencies, at the revs its lake-manifest.json pins
    # (asserted by `checks.pin-consistency`).  Neither is ever compiled —
    # Thales imports only `Std.*` and its own modules — but Lake still insists
    # they be resolvable.  See nix/thales.nix.
    batteries-src = {
      url = "github:leanprover-community/batteries/756e3321fd3b02a85ffda19fef789916223e578c";
      flake = false;
    };
    lean-regex-src = {
      url = "github:pandaman64/lean-regex/cdfe4c8469625510e0e4d5b3d2af51e6acd8e100";
      flake = false;
    };
  };

  outputs =
    { self
    , nixpkgs
    , charon
    , aeneas
    , thales-src
    , batteries-src
    , lean-regex-src
    }:
    let
      inherit (nixpkgs) lib;

      # Systems on which everything except the Thales half is expressible.
      # charon and aeneas both use flake-utils' eachDefaultSystem, so they offer
      # packages for all of these.  x86_64-darwin is deliberately absent: the
      # pinned nixpkgs (26.11) has dropped support for it.
      allSystems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];

      # Systems for which we can name AND hash a Lean 4.29.0 release tarball,
      # i.e. the systems on which `thales` and `lean-from-ts` exist.
      #
      # Only x86_64-linux.  Darwin is absent because the v4.29.0 macOS asset
      # names were never verified.  aarch64-linux is absent because its hash
      # was never computed (see `leanRelease` below): advertising it would have
      # meant `packages.aarch64-linux.thales` evaluating fine and then failing,
      # after a 537 MB download, on a fixed-output hash mismatch.  This flake
      # does not claim support it cannot express.
      leanSystems = [ "x86_64-linux" ];

      # A system in leanSystems but not in allSystems would be dropped silently
      # by mergeSystems below, taking the whole Thales half with it and quietly
      # routing every `c ? thales` guard to the no-Thales branch.
      _leanSystemsSubset =
        lib.assertMsg (lib.subtractLists allSystems leanSystems == [ ])
          "leanSystems must be a subset of allSystems; offenders: ${
            toString (lib.subtractLists allSystems leanSystems)
          }";

      eachSystem = systems: f:
        lib.genAttrs systems (system: f system);

      # Merge two per-system attrsets (the wide one and the Lean-only one).
      # Iterates over `a`, hence the assertion above.
      mergeSystems = a: b:
        assert _leanSystemsSubset;
        lib.mapAttrs (system: v: v // (b.${system} or { })) a;

      ######################################################################
      # The Lean 4.29.0 binary release, per system.
      #
      # v4.29.0 ships `.tar.zst` and `.zip` only (there is no `.tar.gz`), and
      # the unsuffixed `linux` asset IS the x86_64 one.
      #
      # The aarch64-linux entry below is recorded but NOT usable: its hash was
      # never computed, so `hash` is a `throw` rather than `lib.fakeHash`.  A
      # fake hash would have downloaded 537 MB and then died with a bare "hash
      # mismatch in fixed-output derivation …-source.drv"; the throw fails in
      # 0 s and names itself.  To enable aarch64-linux: compute the hash with
      #
      #     TMPDIR=<dir with 3GB free> nix store prefetch-file --unpack --json \
      #       https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux_aarch64.tar.zst
      #
      # replace the throw, and add "aarch64-linux" back to `leanSystems`.
      ######################################################################
      leanRelease = {
        version = "4.29.0";
        perSystem = {
          x86_64-linux = {
            url = "https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux.tar.zst";
            # Verified: unpacked/stripped-root hash, cross-checked between
            # `nix store prefetch-file --unpack` and `nix flake prefetch`.
            hash = "sha256-83gQ0VNh1jIpaBzH7FNO8aMXBNQySxDokkGD7Zl6/Vc=";
          };
          aarch64-linux = {
            url = "https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux_aarch64.tar.zst";
            hash = throw ''
              flake.nix: the sha256 of lean-4.29.0-linux_aarch64.tar.zst has never
              been computed, so aarch64-linux is not in `leanSystems`.  See the
              comment above `leanRelease` for the one command that computes it.
            '';
          };
        };
      };

      ######################################################################
      # Narrow source trees.  Each derivation gets only the files it needs:
      # smaller closures, and — crucially — no accidental dependency on the
      # 7.6 GB `.lake` directory or on the paper sources.
      ######################################################################
      fs = lib.fileset;

      rustCrateSrc = fs.toSource {
        root = ./rust;
        fileset = fs.unions [ ./rust/Cargo.toml ./rust/src ];
      };

      tsSrc = fs.toSource {
        root = ./.;
        fileset = fs.unions [ ./moltPetit.ts ];
      };

      extractedLean = ./Spec/Rust.lean;
      emittedLean = ./Spec/TS.lean;
      goldenEmitted = ./tools/thales-reemission/MoltPetit.emitted.lean;
      thalesFixesPatch = ./tools/thales-reemission/thales-fixes.patch;
      upstreamPrPatches = ./tools/thales-reemission/upstream-prs/patches;
      lakefileToml = ./lakefile.toml;

      # The reviewed-deviations ledger.  `checks.ts-vendored-deviations`
      # degrades to an explanatory failure when it is absent rather than
      # silently skipping — but note that `pathExists` is evaluated against
      # the flake SOURCE, i.e. the git-tracked tree, so creating the file is
      # not enough: it has to be `git add`ed too.  See
      # `apps.update-deviations-patch`.
      deviationsPatchPath = ./tools/thales-reemission/vendored-deviations.patch;
      deviationsPatch =
        if builtins.pathExists deviationsPatchPath then deviationsPatchPath else null;

      ######################################################################
      # Per-system assembly.
      ######################################################################
      wide = eachSystem allSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};

          charonPkg = charon.packages.${system}.charon;
          aeneasPkg = aeneas.packages.${system}.aeneas;

          lean-from-rust = pkgs.callPackage ./nix/lean-from-rust.nix {
            charon = charonPkg;
            aeneas = aeneasPkg;
            inherit rustCrateSrc;
          };
        in
        {
          inherit pkgs charonPkg aeneasPkg lean-from-rust;
        });

      narrow = eachSystem leanSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};

          lean4 = pkgs.callPackage ./nix/lean4-bin.nix {
            inherit (leanRelease) version;
            inherit (leanRelease.perSystem.${system}) url hash;
          };

          thales = pkgs.callPackage ./nix/thales.nix {
            inherit lean4 thalesFixesPatch;
            thalesSrc = thales-src;
            batteriesSrc = batteries-src;
            leanRegexSrc = lean-regex-src;
          };

          lean-from-ts = pkgs.callPackage ./nix/lean-from-ts.nix {
            inherit thales tsSrc;
          };
        in
        {
          inherit lean4 thales lean-from-ts;
        });

      per = mergeSystems wide narrow;
    in
    {
      ####################################################################
      # packages
      ####################################################################
      packages = lib.mapAttrs
        (system: c:
          let pkgs = c.pkgs; in
          {
            # The two extraction toolchains, taken straight from upstream's
            # own flakes rather than rebuilt by hand.  Hermetic.
            charon = c.charonPkg;
            aeneas = c.aeneasPkg;

            # Rust -> Lean.  `$out/MoltPetit.lean` is the aeneas emission,
            # i.e. the body of Spec/Rust.lean below its vendor header.
            lean-from-rust = c.lean-from-rust;

            # The same on every system, with or without thales.
            default = c.lean-from-rust;
          }
          // lib.optionalAttrs (c ? thales) {
            # The pinned + patched TypeScript->Lean emitter.  Hermetic.
            thales = c.thales;

            # The Lean 4.29.0 toolchain thales is built with.  Exposed mostly
            # for debugging; do NOT put it on PATH alongside elan when working
            # on this repo, whose own toolchain is v4.30.0-rc2.
            lean4-4_29 = c.lean4;

            # TypeScript -> Lean.  `$out/MoltPetit.lean` is the raw emission.
            lean-from-ts = c.lean-from-ts;

            # Both generated files side by side; what `update-extracted` reads.
            generated = pkgs.runCommand "molt-petit-generated" { } ''
              mkdir -p "$out/rust" "$out/ts"
              cp ${c.lean-from-rust}/MoltPetit.lean "$out/rust/MoltPetit.lean"
              cp ${c.lean-from-ts}/MoltPetit.lean "$out/ts/MoltPetit.lean"
            '';
          })
        per;

      ####################################################################
      # checks — `nix flake check` runs these.  See the cost note at the top.
      ####################################################################
      checks = lib.mapAttrs
        (system: c:
          let
            all = c.pkgs.callPackage ./nix/checks.nix {
              inherit (c) lean-from-rust;
              lean-from-ts = c.lean-from-ts or null;
              inherit extractedLean emittedLean goldenEmitted deviationsPatch
                thalesFixesPatch upstreamPrPatches tsSrc rustCrateSrc
                lakefileToml;
              charonRev = charon.rev;
              aeneasSrc = aeneas;
              aeneasRev = aeneas.rev;
              thalesSrc = thales-src;
              leanVersion = leanRelease.version;
              batteriesRev = batteries-src.rev;
              leanRegexRev = lean-regex-src.rev;
            };
          in
          {
            # Vendored Rust extraction == fresh charon+aeneas output, byte-exact.
            rust-extraction = all.rust-extraction;
            # Same, tolerating only `Source:` line-number drift.
            rust-extraction-modulo-loc = all.rust-extraction-modulo-loc;

            # The TS ledger checks.  NONE of these needs the Thales toolchain —
            # they only read checked-in files — so they run on every system.
            # Gating them on `thales` would have meant a green `nix flake
            # check` with zero enforcement on Spec/TS.lean
            # wherever the Lean release is not named.
            ts-vendored-deviations = all.ts-vendored-deviations;
            ts-deviation-sites = all.ts-deviation-sites;
            ts-golden-digest = all.ts-golden-digest;

            # The emitter patch is the one link in the TS chain not pinned by
            # a revision; pin it by digest and by the reviewed upstream PRs.
            thales-fixes-patch = all.thales-fixes-patch;

            # The cross-file equalities the comments assert, machine-checked.
            pin-consistency = all.pin-consistency;

            # moltPetit.ts typechecks under --strict (bigint => ES2020).
            tsc = all.tsc;
            # The molt_petit crate typechecks, fully offline.
            cargo = all.cargo;
          }
          // lib.optionalAttrs (c ? thales) {
            # Checked-in golden == fresh thales emission, byte-exact.
            # The only check that genuinely needs the emitter.
            ts-emission-golden = all.ts-emission-golden;
          }
          // lib.optionalAttrs (!(c ? thales)) {
            # Not a check: a marker, so the missing half is visible in the
            # check list and the log rather than only to someone who counts
            # the attributes.
            ts-toolchain-unavailable = all.ts-toolchain-unavailable;
          })
        per;

      ####################################################################
      # apps — impure by nature; see nix/apps.nix for why each one has to be.
      ####################################################################
      apps = lib.mapAttrs
        (system: c:
          let
            mk = c.pkgs.callPackage ./nix/apps.nix {
              inherit (c) lean-from-rust;
              lean-from-ts = c.lean-from-ts or null;
            };
            app = drv: { type = "app"; program = lib.getExe drv; inherit (drv) meta; };
          in
          {
            # Build the repo's own Lean development, all four libraries.
            # Needs the network (elan + mathlib olean cache).
            verify-lean = app mk.verify-lean;
            # Trace-only check of the same four libraries; no network.
            verify-lean-offline = app mk.verify-lean-offline;
            # The soundness half of the pairing; see the note at the top.
            default = app mk.verify-lean;
          }
          // lib.optionalAttrs (c ? thales) {
            # Re-vendor the generated Lean sources from the pinned toolchains.
            # Overwrites tracked files; refuses on a dirty tree.
            update-extracted = app mk.update-extracted;
            # Regenerate the ledger of reviewed hand-edits to Spec/TS.lean.
            update-deviations-patch = app mk.update-deviations-patch;
          })
        per;

      ####################################################################
      # devShells
      ####################################################################
      devShells = lib.mapAttrs
        (system: c:
          let pkgs = c.pkgs; in
          {
            # Day-to-day shell for this repo.
            #
            # NOTE the deliberate omission: the Lean 4.29.0 toolchain that
            # `thales` is built with is NOT here, because it would shadow the
            # v4.30.0-rc2 `lean`/`lake` that elan installs for this project.
            # Use `nix develop .#thales` if you need to hack on the emitter.
            default = pkgs.mkShell {
              name = "molt-petit";
              packages = [
                pkgs.elan # supplies lean/lake for lean-toolchain (v4.30.0-rc2)
                pkgs.git
                pkgs.curl
                pkgs.cacert
                pkgs.typescript # tsc 5.9.x, for moltPetit.ts
                pkgs.nodejs # tsc is a node script
                pkgs.cargo # `cargo check` only; NOT charon's nightly
                pkgs.rustc
                pkgs.gnupatch
                c.charonPkg
                c.aeneasPkg
              ] ++ lib.optionals (c ? thales) [ c.thales ];
              shellHook = ''
                export SSL_CERT_FILE="''${SSL_CERT_FILE:-${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt}"
                echo "molt-petit dev shell: elan, charon, aeneas${lib.optionalString (c ? thales) ", thales"}, tsc, cargo"
              '';
            };
          }
          // lib.optionalAttrs (c ? thales) {
            # For working on the Thales emitter itself: Lean 4.29.0 on PATH.
            thales = pkgs.mkShell {
              name = "thales-dev";
              packages = [ c.lean4 pkgs.git ];
            };
          })
        per;

      formatter = lib.mapAttrs (system: c: c.pkgs.nixpkgs-fmt) per;
    };
}
