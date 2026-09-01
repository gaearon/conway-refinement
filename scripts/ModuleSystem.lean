/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
/-
Adapted and modified from TauCeti's Apache-2.0-licensed `scripts/ModuleSystem.lean`:
https://github.com/TauCetiProject/TauCeti/blob/main/scripts/ModuleSystem.lean
-/
module

import Lean

/-!
# Audit use of Lean's module system

This executable reads each compiled ConwayRefinement and project-tooling module and checks its
`ModuleData.isModule` flag. Thus it checks actual elaboration under Lean's module system, rather
than searching source text for the `module` command.
-/

open Lean

private def auditedRoot : Name := `ConwayRefinement

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private partial def collectLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      modules := modules ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

private def auditedModules : IO (Array Name) :=
  return #[auditedRoot] ++
    (← collectLeanModules (auditedRoot.toString : System.FilePath)) ++
    (← collectLeanModules "scripts")

@[noinline] private def getIsModule (moduleData : ModuleData) : BaseIO Bool :=
  return moduleData.isModule

private def moduleIsOptedIn (name : Name) : IO (Option Bool) := do
  let olean ← findOLean name
  if !(← olean.pathExists) then
    return none
  let (moduleData, region) ← readModuleData olean
  let isModule ← getIsModule moduleData
  unsafe region.free
  return some isModule

public def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules ← auditedModules
  let mut violations := #[]
  for name in modules do
    match ← moduleIsOptedIn name with
    | some true => pure ()
    | some false => violations := violations.push name
    | none =>
        IO.eprintln s!"module-system: no compiled artifact for {name}; run `lake build` first."
        violations := violations.push name
  if modules.isEmpty then
    IO.eprintln s!"module-system: found no modules under {auditedRoot}."
    return 1
  if violations.isEmpty then
    IO.println s!"module-system: all {modules.size} project modules use the module system."
    return 0
  IO.eprintln s!"module-system: {violations.size} module(s) failed the audit:"
  for name in violations do
    IO.eprintln s!"  {name}"
  return 1
