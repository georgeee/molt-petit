import Spec
import Paper.Proofs

/-!
Run by `tools/paper-check.sh`, which writes the paper's `\code{}` tokens to
`.lake/paper-check/cited.txt`. Fails unless
* every cited name that is a theorem of the development is `MoltPaper.xxx`
  with statement `MoltPaper.thm_xxx` (in `Spec/Statements.lean`);
* every cited definition is declared in `Spec/`;
* every `MoltPaper` theorem depends on no axiom beyond `propext`,
  `Classical.choice` and `Quot.sound`.
-/

open Lean Elab Command

def thmName : Name → Name
  | .str p s => .str p ("thm_" ++ s)
  | n => n

elab "#paper_check" : command => do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    match env.getModuleIdxFor? c with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  let toks := (← IO.FS.readFile ".lake/paper-check/cited.txt").splitOn "\n" |>.filter (· ≠ "")
  for t in toks do
    let b := t.toName
    let ours (c : Name) := [`Spec, `Molt, `MoltPetit, `Rust].any (·.isPrefixOf (modOf c))
    let dev := [`Molt ++ b, `MoltPetit.Model ++ b, b, `Rust ++ b, `MoltPetit ++ b].filter
      fun c => env.contains c && ours c
    let isThm := dev.any fun c => (env.find? c).any (·.isTheorem) && !env.isProjectionFn c
    if isThm then
      unless (env.find? (`MoltPaper ++ b)).any (·.isTheorem) &&
          modOf (`MoltPaper ++ thmName b) == `Spec.Statements do
        logError m!"paper cites theorem `{t}`: needs MoltPaper.{thmName b} in Spec/Statements.lean and MoltPaper.{t} in Paper/Proofs.lean"
    else if let some c := dev.head? then
      unless (`Spec).isPrefixOf (modOf c) do
        logError m!"paper cites `{t}` = {c}, declared in {modOf c}, not in Spec/"
  for (n, ci) in env.constants.map₁.toList do
    if ci.isTheorem && modOf n == `Paper.Proofs then
      for a in ← liftCoreM (collectAxioms n) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          logError m!"{n} depends on axiom {a}"

#paper_check
