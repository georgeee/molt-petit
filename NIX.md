# The nix flake

Pinned toolchains for the two extraction paths (Rust → Lean via Charon+Aeneas,
TypeScript → Lean via Thales), plus the *faithfulness* checks that tie the
vendored Lean sources to them.

**Read the header comment of `flake.nix` first** — it states the one thing that
is easiest to get wrong: `nix flake check` proves **faithfulness** (the vendored
Lean is what the pinned toolchains emit from the current sources), never
**soundness** (that the proofs still go through). The soundness half is
`nix run .#verify-lean`, which needs the network and therefore cannot be a
check. Run both, or you have gated on half the claim.

## Status of this document and of the flake

The flake was authored and validated **by evaluation and instantiation only**:
`nix flake show`, `nix eval`, `nix derivation show`, and `nix build --dry-run`
all succeed and produce the outputs listed below. **No derivation was ever
realized** — the environment it was written in cannot run builders at all. So:

- Every output below is known to *evaluate* and to *instantiate*.
- No output below is known to *build*. Nothing here is a reported build result.
- A first real `nix build` on a normal machine is the first true test. Budget
  for build-time breakage in the two from-source halves (charon's cargo tree,
  aeneas' OCaml tree) — both are upstream's own derivations, so a failure there
  is most likely an upstream/nixpkgs-rev interaction, not this flake.

Two independent confirmations that the *recipes* are right, from a from-scratch
non-nix bootstrap of the same pins: the Charon+Aeneas emission is byte-identical
to the vendored body of `Rust/Extracted.lean`, and the Thales emission is
byte-identical to `tools/thales-reemission/MoltPetit.emitted.lean`. The flake
encodes those same two comparisons as `checks.rust-extraction` and
`checks.ts-emission-golden`.

## Before anything works: the files must be git-tracked

A `git+file` flake sees **git-tracked files only**. `flake.nix`, `flake.lock`,
everything under `nix/`, and `tools/thales-reemission/vendored-deviations.patch`
must be `git add`ed or nix cannot see them — an untracked `nix/*.nix` makes the
whole flake fail to load, and an untracked `vendored-deviations.patch` silently
routes `checks.ts-vendored-deviations` into its "missing artefact" branch.

`nix flake show` will tell you exactly which path it cannot see.

## Outputs

All commands run from the repo root. Substitute your own system for
`x86_64-linux` where an attribute path is spelled out.

### Packages

| Command | What it produces | Purity | Cost |
|---|---|---|---|
| `nix build .#lean-from-rust` (= `.#default`) | `result/MoltPetit.lean`: the Aeneas emission from `rust/src/lib.rs`, i.e. the body of `Rust/Extracted.lean` below its 16-line vendor header | **hermetic**, fully offline (`CARGO_NET_OFFLINE=1`; the crate has no dependencies) | the expensive one — see below |
| `nix build .#lean-from-ts` | `result/MoltPetit.lean`: the raw Thales emission from `moltPetit.ts` | **hermetic**, fully offline | Lean 4.29.0 release tarball, 537 MB, + a Lake build of Thales |
| `nix build .#generated` | both of the above side by side (`result/rust/`, `result/ts/`); what `update-extracted` reads | hermetic | union of the two |
| `nix build .#charon` / `.#aeneas` | the pinned extraction binaries, straight from upstream's own flakes | hermetic | as `lean-from-rust` |
| `nix build .#thales` | the pinned + patched TypeScript→Lean emitter | hermetic | as `lean-from-ts` |
| `nix build .#lean4-4_29` | the Lean 4.29.0 binary release Thales is built with. Debug aid only — do **not** put it on PATH next to elan, this repo is on v4.30.0-rc2 | hermetic (fixed-output, hash pinned) | 537 MB download |

`lean-from-rust` and `lean-from-ts` are *not* bit-reproducible end to end: the
intermediate `molt_petit.llbc` differs run to run (embedded paths/ordering).
The **Lean** output is stable — that is the property the checks pin.

`charon`, `aeneas`, `lean-from-rust` and `default` exist on `x86_64-linux`,
`aarch64-linux` and `aarch64-darwin`. Everything Thales-flavoured
(`thales`, `lean4-4_29`, `lean-from-ts`, `generated`) exists on **x86_64-linux
only**, because that is the only system for which the flake can both name and
hash a Lean 4.29.0 release tarball. See "Placeholder hashes" below.

### Checks

```bash
nix flake check                  # everything (expensive — read the cost note)
nix build .#checks.x86_64-linux.tsc \
          .#checks.x86_64-linux.cargo \
          .#checks.x86_64-linux.pin-consistency \
          .#checks.x86_64-linux.ts-golden-digest \
          .#checks.x86_64-linux.ts-deviation-sites \
          .#checks.x86_64-linux.ts-vendored-deviations \
          .#checks.x86_64-linux.thales-fixes-patch   # the cheap subset
```

All checks are **hermetic**. What each one pins:

- `rust-extraction` — the body of `Rust/Extracted.lean` is byte-exactly what
  pinned charon+aeneas emit from the current `rust/src/lib.rs`. No
  normalisation: every `Source: 'src/lib.rs', lines N:C-M:C` comment must match,
  so a *comment-only* edit to `lib.rs` that shifts line numbers fails this check
  until you re-vendor.
- `rust-extraction-modulo-loc` — the same, tolerating only `Source:` line-number
  drift. Use it to tell "line numbers moved" apart from "a definition changed".
- `ts-emission-golden` — `tools/thales-reemission/MoltPetit.emitted.lean` is
  byte-exactly what the pinned+patched Thales emits from `moltPetit.ts`. The
  only check that actually needs the emitter, hence x86_64-linux only.
- `ts-vendored-deviations` — `MoltPetit/TS/Emitted.lean` is that golden plus
  exactly the reviewed delta in `vendored-deviations.patch`, byte for byte.
- `ts-deviation-sites` — *which* declarations deviate: exactly the nine named in
  `nix/checks.nix`. Order-insensitive, so a block move is not mistaken for an
  edit (and cannot hide one).
- `ts-golden-digest`, `thales-fixes-patch` — recorded digests. Tripwires, not
  cryptographic pins: they turn a silent regeneration into a two-file diff a
  reviewer cannot miss. `thales-fixes.patch` matters most — it is the one link
  in the TS chain pinned only by review, and it *defines* what "faithful" means
  for the TypeScript path.
- `pin-consistency` — the cross-file equalities the comments assert, machine-checked
  (aeneas' `charon-pin` == our charon rev; Thales' `lake-manifest.json` revs ==
  our `batteries-src`/`lean-regex-src`; Thales' `lean-toolchain` == 4.29.0; the
  aeneas rev in `lakefile.toml` == our `aeneas` input).
- `tsc` — `moltPetit.ts` typechecks under `--strict`.
- `cargo` — the `molt_petit` crate typechecks, fully offline.

On systems without Thales you get a `ts-toolchain-unavailable` marker instead of
`ts-emission-golden`, so the missing half is visible in the check list rather
than only to someone counting attributes. The other TS checks read checked-in
files only and run everywhere.

**Cost.** `nix flake check` is not a smoke test. Measured with
`nix build --dry-run` (on a host with a warm nixpkgs store, so the *fetch*
figures are a lower bound; the *build* count is the from-source part and is
what dominates):

| target | derivations to build | to fetch |
|---|---|---|
| `packages.lean-from-rust` (and so `checks.rust-extraction`, and `devShells.default`) | **405** | 852 MiB down / 4.1 GiB unpacked |
| `packages.thales` | 3 | 8 MiB (+ the 537 MB Lean tarball, which is *built*, not fetched) |
| `checks.ts-emission-golden` | 5 | 8 MiB |
| `checks.tsc`, `.cargo`, `.pin-consistency`, `.ts-*` | 1–2 each | ~nothing |

The 405 are charon's cargo tree and aeneas' OCaml 5.2.1 tree, from source,
because neither upstream flake declares a public substituter. Expect tens of
minutes on a fast machine. (A hand bootstrap of the same two at these revs took
~2m for charon and ~7m for aeneas *after* ~20m of toolchain/opam setup, so the
order of magnitude is right.)

### Apps

| Command | What it does | Purity |
|---|---|---|
| `nix run .#verify-lean` (= `.#default`) | `elan toolchain install` + `lake exe cache get` + `lake build MoltPetit Rust Thales Molt` — all four libraries, hence all four axiom-guard files | **impure, needs the network** |
| `nix run .#verify-lean-offline` | `lake build --no-build` on the same four targets: exit 0 means every job is trace-current | impure (touches your `.lake`), but **no network** |
| `nix run .#update-extracted` | re-vendors the generated Lean sources — see below | impure: writes into your working tree |
| `nix run .#update-deviations-patch` | regenerates `vendored-deviations.patch` from the current `MoltPetit/TS/Emitted.lean` | impure: writes into your working tree |

`verify-lean` **cannot** be a derivation, for three reasons that are not fixable
here: `lean-toolchain` pins `leanprover/lean4:v4.30.0-rc2` and nixpkgs' `lean4`
is 4.30.0 (a different release, not an rc), so elan must fetch it; Mathlib's
oleans come from `lake exe cache get`, ~8300 individually-addressed `.ltar`
fetches with no aggregate hash (building Mathlib from source instead is a
multi-hour, ~6 GB derivation); and Lake insists on materialising
`.lake/packages` itself. A derivation that pretended otherwise would either fail
in the sandbox or lie about being hermetic.

`update-extracted` and `update-deviations-patch` exist on x86_64-linux only
(they need the Thales half).

### Dev shells

```bash
nix develop            # elan, git, curl, cacert, tsc, node, cargo, rustc, patch,
                       # charon, aeneas (+ thales on x86_64-linux)
nix develop .#thales   # Lean 4.29.0 on PATH, for hacking on the emitter itself
```

The default shell deliberately **omits** Lean 4.29.0: it would shadow the
v4.30.0-rc2 `lean`/`lake` that elan installs for this project. Note that
entering it costs the same 405 derivations as `lean-from-rust`, since charon and
aeneas are in it.

`nix fmt` runs `nixpkgs-fmt` over the flake.

## Regenerating the vendored Lean sources

```bash
nix run .#update-extracted
git diff            # review every hunk
nix flake check && nix run .#verify-lean
```

It **overwrites four tracked files**:

| file | new content |
|---|---|
| `Rust/Extracted.lean` | existing vendor header + fresh Aeneas body |
| `tools/thales-reemission/MoltPetit.emitted.lean` | fresh Thales emission (the golden) |
| `MoltPetit/TS/Emitted.lean` | existing header + (golden + the reviewed deltas from `vendored-deviations.patch`) |
| `nix/checks.nix` | the `goldenDigest` constant, rewritten to match the new golden |

It refuses to run if any of those has uncommitted edits (override with
`UPDATE_EXTRACTED_FORCE=1`), if `vendored-deviations.patch` is missing, or if any
of the flake's source files are untracked — because nix builds from the
git-tracked tree, so re-vendoring with untracked edits on disk would write an
extraction of a source tree that is not the one you are looking at, and
`checks.rust-extraction` would then certify it as faithful. All preconditions
are checked before the first write.

Re-vendoring is **mandatory after any edit to `rust/src/lib.rs`, including a
comment-only one**: Aeneas emits a `Source:` provenance comment per definition,
so anything that shifts line counts shifts every one of its `Source:` comments (79 today) and fails
`rust-extraction`. Use `rust-extraction-modulo-loc` to confirm that line numbers
are all that moved.

If your hand-edits to `MoltPetit/TS/Emitted.lean` changed, regenerate the ledger
first with `nix run .#update-deviations-patch`, review it, and `git add` it — an
untracked ledger is invisible to the flake and leaves the check red.

**The faithfulness checks are what keep the vendored files honest.** They are
the only thing standing between "these Lean definitions came out of the Rust/TS"
and "someone edited generated code by hand". `update-extracted` blesses whatever
the current sources produce — running it is not evidence of anything. The
evidence is `nix flake check` passing afterwards on a diff a human read, paired
with `nix run .#verify-lean` proving the theorems still go through over the new
bodies. `rust/extract.sh` remains the equivalent by-hand route.

## Placeholder hashes

**There is no `lib.fakeHash` anywhere in this flake.** The one hash that was
never computed is the aarch64-linux Lean 4.29.0 tarball, and it is written as a
`throw` rather than a fake hash on purpose: a fake hash would download 537 MB and
then die with a bare "hash mismatch in fixed-output derivation …-source.drv",
whereas the throw fails in 0 s and names itself. That is also why
`leanSystems = [ "x86_64-linux" ]` — the flake does not advertise support it
cannot express.

To enable aarch64-linux:

```bash
TMPDIR=<dir with 3GB free> nix store prefetch-file --unpack --json \
  https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux_aarch64.tar.zst
```

replace the `throw` in `flake.nix` with the resulting hash, and add
`"aarch64-linux"` back to `leanSystems`. Darwin is absent for a different
reason: the v4.29.0 macOS asset *names* were never verified.

Because no derivation has ever been realized here, a first real build could
still surface a hash that needs correcting — most plausibly the x86_64-linux
tarball (recorded as `sha256-83gQ0VNh1jIpaBzH7FNO8aMXBNQySxDokkGD7Zl6/Vc=`,
cross-checked between `nix store prefetch-file --unpack` and `nix flake
prefetch`, but never consumed by an actual `fetchzip`). If it mismatches, the
error names the expected and actual hashes; take the actual one.

## Why these pins

```
charon        9dd7f23c8458b2366ce0b5ca7529c5ad4c5fb350   (= charon 0.1.212)
aeneas        bf13c42e7c34d07fc396baffad39c93023b12914
thales        55b03fb3fbbcca615cb438b2492d6a1c115d0394   (+ tools/thales-reemission/thales-fixes.patch)
lean (thales) v4.29.0 binary release
nixpkgs       c27cdad491a991b11ed731760aa2ef8db0cb0410   (nixos-unstable, 2026-08-27)
```

The aeneas rev is the one `lakefile.toml` requires for the **Lean-side runtime
model** — the `Aeneas` library the extracted code imports. The Aeneas *binary*
that emits that code and the Aeneas *Lean library* the emitted code is elaborated
against are two halves of one interface; if they drift, the extraction still
"succeeds" and the Lean fails to elaborate, or worse, elaborates against a
different model than the emitter assumed. So one rev pins both halves, and
`checks.pin-consistency` asserts the `lakefile.toml` rev equals the flake input.

The charon rev is what `rust/extract.sh` names and what aeneas' own `charon-pin`
file records at that aeneas rev. `aeneas.inputs.charon.follows = "charon"` makes
the `charon` binary (which writes the `.llbc`) and the charon-ml inside `aeneas`
(which reads it) a single pin, because LLBC skew between them is silent; since
that override could then disagree with what upstream tested,
`checks.pin-consistency` asserts `${aeneas}/charon-pin == charon.rev` so a
one-sided bump fails loudly instead of drifting.

Thales' pin comes with two extras that are part of it: `thales-fixes.patch`
(without which `moltPetit.ts` does not parse) and Lean **4.29.0**, which is what
Thales' own `lean-toolchain` names — *not* this repo's v4.30.0-rc2, and not
nixpkgs' 4.30.0. The 4.29.0 binary release is the same artifact elan installs,
which is what produced the reference emission the golden was taken from.

charon and aeneas deliberately do **not** follow our nixpkgs: each upstream flake
locks a nixpkgs it was tested against, and overriding it would both deviate from
what upstream CI exercises and throw away binary-cache hits. Our nixpkgs is used
only for the small stuff (tsc, cargo, elan, patch).

Finally: **`flake.lock` is part of the pin.** The direct inputs are rev-pinned,
but they drag in 10 transitive nodes (16 lock nodes in all: crane, fstar, rust-overlay, flake-utils,
two more nixpkgs, …), several of which float in their `original` ref and are
resolved only by the lock. Commit it.
