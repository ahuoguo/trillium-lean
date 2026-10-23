/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Lean
import Iris.Std.RocqPorting

/-!
# Dump Trillium porting data

Adapted from iris-lean's `scripts/DumpPortingData.lean`. Loads every `Trillium.*`
module and writes all `@[rocq_alias trillium.…]`, `#rocq_ignore trillium.…` and
`#rocq_ignore_file trillium.…` entries to a JSON file, together with the Lean module
defining each alias target and whether the target depends on `sorryAx`.

Usage: `lake exe dumpPortingData [output-path]` (default `.lake/porting_data.json`).
-/

open Lean

def isTrillium (n : Name) : Bool := n.getRoot == `trillium

partial def discoverModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      out := out ++ (← discoverModules entry.path (pre ++ entry.fileName.toName))
    else if entry.fileName.endsWith ".lean" then
      let mod := pre ++ (entry.fileName.dropEnd 5).toString.toName
      -- Skip modules that are not built (e.g. still being written).
      if (← (System.FilePath.mk ".lake/build/lib/lean" / modToFilePath "." mod "olean").pathExists) then
        out := out.push mod
  return out

unsafe def main (args : List String) : IO Unit := do
  let outputPath := args.head? |>.getD ".lake/porting_data.json"
  Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let modules ← discoverModules "Trillium" `Trillium
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<dump>", fileMap := default }
  let st : Core.State := { env }
  let mut aliases : Array Json := #[]
  for (name, info) in env.constants.toList do
    unless name.getRoot == `Rocq do continue
    let rocq := name.replacePrefix `Rocq .anonymous
    unless isTrillium rocq do continue
    let target? := match info with
      | .thmInfo v => v.value.constName?
      | .defnInfo v => v.value.constName?
      | _ => none
    let some target := target? | continue
    let (axs, _) ← (Lean.collectAxioms (m := CoreM) target).toIO ctx st
    let modName := match env.getModuleIdxFor? target with
      | some idx => (env.header.moduleNames[idx.toNat]?).getD .anonymous
      | none => .anonymous
    aliases := aliases.push <| Json.mkObj [
      ("rocq", rocq.toString (escape := false)), ("lean", target.toString),
      ("module", modName.toString), ("sorry", axs.contains ``sorryAx)]
  let ignores := (rocqIgnoreExt.getState env).filter (isTrillium ·.1) |>.map fun (r, why) =>
    Json.mkObj [("rocq", r.toString (escape := false)), ("reason", why)]
  let files := (rocqIgnoreFileExt.getState env).filter (·.1.startsWith "trillium") |>.map
    fun (folder, file, why) => Json.mkObj [("folder", folder), ("file", file), ("reason", why)]
  let json := Json.mkObj [("aliases", Json.arr aliases), ("ignores", Json.arr ignores),
    ("ignored_files", Json.arr files)]
  IO.FS.writeFile outputPath (json.pretty ++ "\n")
  IO.println s!"Wrote {aliases.size} aliases, {ignores.size} ignores, {files.size} ignored files to {outputPath}"
