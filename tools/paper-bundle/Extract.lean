import Molt
import Rust
import Paper.Proofs

/-!
Run by `tools/paper-bundle.sh`. Reads the paper's `\code{}` tokens from
`.lake/paper-bundle/cited.txt` and

* fails unless every cited name that is a theorem of the development is a
  `MoltPaper.xxx` with statement `thm_xxx`, and every `MoltPaper` theorem
  depends on no axiom beyond `propext`, `Classical.choice`, `Quot.sound`;
* writes `.lake/paper-bundle/closure.tsv` (module, first line, last line, name):
  every declaration of this repository that the `thm_xxx` statements and the
  cited definitions reach, with its source range.
-/

open Lean Elab Command

namespace PaperBundle

def ours (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i => [`MoltPetit, `Molt, `Rust, `Thales].any (·.isPrefixOf env.header.moduleNames[i.toNat]!)

def closure (env : Environment) (seeds : List Name) : NameSet := Id.run do
  let mut todo := seeds
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n || !ours env n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants.toList
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants.toList
    match ci with
    | .inductInfo ii => cs := cs ++ ii.ctors
    | .ctorInfo c => cs := cs ++ [c.induct]
    | _ => pure ()
    todo := cs ++ todo
  return seen

def thmName (n : Name) : Name :=
  match n with
  | .str p s => .str p ("thm_" ++ s)
  | _ => n

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#paper_bundle" : command => do
  let env ← getEnv
  let dir := ".lake/paper-bundle"
  let toks := (← IO.FS.readFile s!"{dir}/cited.txt").splitOn "\n" |>.filter (· ≠ "")
  let mut seeds : List Name := []
  let mut bad := 0
  for t in toks do
    let b := t.toName
    let paper := `MoltPaper ++ b
    let dev := [`Molt ++ b, `MoltPetit.Model ++ b, b, `Rust ++ b, `MoltPetit ++ b].filter env.contains
    let isThm := dev.any fun c => (env.find? c).any (·.isTheorem) && !env.isProjectionFn c
    if isThm then
      unless (env.find? paper).any (·.isTheorem) && env.contains (`MoltPaper ++ thmName b) do
        logError m!"paper cites theorem `{t}` but there is no MoltPaper.{t} : MoltPaper.{thmName b}"
        bad := bad + 1
    else if let some c := dev.head? then
      seeds := c :: seeds
  -- statements and axioms
  for (n, ci) in env.constants.toList do
    unless (`MoltPaper).isPrefixOf n && ours env n == false do continue
    match ci with
    | .defnInfo d =>
      if n.lastComponentAsString.startsWith "thm_" then
        seeds := d.value.getUsedConstants.toList ++ seeds
    | .thmInfo _ =>
      let axs ← liftCoreM (collectAxioms n)
      for a in axs do
        unless allowed.contains a do
          logError m!"{n} depends on axiom {a}"
          bad := bad + 1
    | _ => pure ()
  let s := closure env seeds
  let mut out := ""
  for n in s.toList do
    let mod := env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!
    let mut m := n
    let mut rng : Option DeclarationRanges := none
    repeat
      rng ← liftCoreM <| findDeclarationRanges? m
      if rng.isSome || m.isAnonymous then break
      m := m.getPrefix
    if let some r := rng then
      out := out ++ s!"{mod}\t{r.range.pos.line}\t{r.range.endPos.line}\t{n}\n"
  IO.FS.writeFile s!"{dir}/closure.tsv" out
  if bad == 0 then logInfo m!"paper-bundle: {s.size} declarations"

end PaperBundle

#paper_bundle
