import Lean
import Lean.Util.CollectAxioms
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr

/-! Verification infrastructure, not an additional mathematical assumption.
The driver imports the freshly compiled root at private visibility and selects
ALL constants by their defining module, independent of declaration namespace. -/
open Lean

private def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def posJson (p : Position) : Json :=
  Json.mkObj [("line", toJson p.line), ("column", toJson p.column)]

private def rangeJson (r : DeclarationRange) : Json :=
  Json.mkObj [("start", posJson r.pos), ("end", posJson r.endPos)]

private def parseJsonFile (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError e)

private def stringField (j : Json) (key : String) : IO String := do
  match j.getObjValAs? String key with
  | .ok s => pure s
  | .error e => throw (IO.userError e)

private def audit (modules : Array String) : CoreM Json := do
  let env ← getEnv
  let mut declarations := #[]
  let entries := env.constants.toList.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  for (name, ci) in entries do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx.toNat]!.toString
    unless modules.contains origin do continue
    let axioms ← collectAxioms name
    let ranges ← findDeclarationRanges? name
    let mut refs := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      refs := refs ++ value.getUsedConstants
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson origin),
      ("kind", toJson (kind ci)), ("private", toJson (isPrivateName name)),
      ("internal", toJson name.isInternal), ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial),
      ("extern", toJson (isExtern env name)),
      ("implemented_by", toJson ((Compiler.getImplementedBy? env name).map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("references", toJson (refs.map Name.toString)),
      ("range", ranges.map (rangeJson ·.range) |>.getD Json.null),
      ("selection", ranges.map (rangeJson ·.selectionRange) |>.getD Json.null)]
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("root", toJson env.header.imports[0]!.module.toString),
    ("visibility", toJson "private"),
    ("imported_modules", toJson (env.header.moduleNames.map Name.toString)),
    ("declarations", Json.arr declarations)]

/-- Parse imports using Lean's parser; Python does not guess module syntax. -/
private def importsReport (manifest : Json) : IO Json := do
  let .ok entries := manifest.getArr? | throw (IO.userError "Expected module array")
  let mut result := #[]
  for entry in entries do
    let name ← stringField entry "module"
    let path ← stringField entry "path"
    let (imports, _, messages) ← Lean.Elab.parseImports (← IO.FS.readFile path) (some path)
    if messages.hasErrors then throw (IO.userError s!"Import parse failed: {path}")
    result := result.push <| Json.mkObj [
      ("module", toJson name), ("imports", toJson (imports.map (·.module.toString)))]
  return Json.arr result

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["imports", manifestPath, output] =>
      let report ← importsReport (← parseJsonFile manifestPath)
      IO.FS.writeFile output (report.pretty ++ "\n")
    | ["audit", root, manifestPath, output] =>
      initSearchPath (← findSysroot)
      enableInitializersExecution
      let .ok entries := (← parseJsonFile manifestPath).getArr? |
        throw (IO.userError "Expected module array")
      let modules ← entries.mapM (fun e => stringField e "module")
      let env ← importModules #[{module := root.toName}] {}
        (trustLevel := 0) (loadExts := true) (level := .private)
      let opts := (({} : Options).set `maxRecDepth (10000 : Nat)).set `maxHeartbeats (0 : Nat)
      let report ← (audit modules).toIO'
        {fileName := "<project-axiom-audit>", fileMap := default, options := opts}
        {env := env}
      IO.FS.writeFile output (report.pretty ++ "\n")
    | _ => throw (IO.userError "usage: AxiomAudit.lean imports MANIFEST OUT | audit ROOT MANIFEST OUT")
    return 0
  catch e =>
    IO.eprintln s!"Environment audit failed: {e}"
    return 1
