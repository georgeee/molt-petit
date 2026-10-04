import Lean
/-!
`#paper_hashes "file"`: for each declaration listed in
`.lake/paper-bundle/closure.tsv`, and every `MoltPaper.thm_xxx`, record a hash
of its elaborated type and, for definitions, its value. `tools/paper-bundle.sh`
runs this in the development and at the end of the bundle and requires the two
records to agree. Auxiliary declarations (matchers, `_proof_n`, private names)
are named differently in the two places, because Lean shares them within a
module; a reference to one is hashed by its content, not its name.
-/
open Lean Elab Command

namespace PaperHashes

def aux (env : Environment) (n : Name) : Bool :=
  n.isInternal || isPrivateName n || Meta.isMatcherCore env n

partial def hashE (env : Environment) (e : Expr) : StateM (Std.HashMap Name UInt64) UInt64 := do
  let mut cs : Array (Name × UInt64) := #[]
  for c in e.getUsedConstants do
    if aux env c then cs := cs.push (c, ← hashC env c)
  let e' := e.replace fun x => match x with
    | .const c ls => (cs.find? (·.1 == c)).map fun (_, h) => .const (.mkSimple s!"aux{h}") ls
    | _ => none
  return e'.hash
where
  hashC (env : Environment) (c : Name) : StateM (Std.HashMap Name UInt64) UInt64 := do
    if let some h := (← get)[c]? then return h
    modify (·.insert c 0)  -- cut cycles
    let some ci := env.find? c | return 1
    let h := mixHash (← hashE env ci.type) (← match ci.value? (allowOpaque := true) with
      | some v => if ci.isTheorem then pure 0 else hashE env v
      | none => pure 0)
    modify (·.insert c h)
    return h

end PaperHashes

elab "#paper_hashes " f:str : command => do
  let env ← getEnv
  let rows := (← IO.FS.readFile ".lake/paper-bundle/closure.tsv").splitOn "\n"
  let mut names := rows.filterMap fun r =>
    match r.splitOn "\t" with
    | [_, _, _, n] => some n.toName
    | _ => none
  for (n, _) in env.constants.toList do
    if (`MoltPaper).isPrefixOf n && n.lastComponentAsString.startsWith "thm_" then
      names := n :: names
  let mut out := ""
  let mut st : Std.HashMap Name UInt64 := {}
  for n in names.toArray.qsort Name.lt do
    if PaperHashes.aux env n || n.lastComponentAsString.startsWith "match_" then continue
    let some ci := env.find? n | out := out ++ s!"{n}\tMISSING\n"; continue
    let (t, st') := (PaperHashes.hashE env ci.type).run st
    st := st'
    let (v, st') := (match ci with
      | .defnInfo d => PaperHashes.hashE env d.value
      | _ => pure 0).run st
    st := st'
    out := out ++ s!"{n}\t{t}\t{v}\n"
  IO.FS.writeFile f.getString out
