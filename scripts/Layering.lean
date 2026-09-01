/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit the mathematical order of the source tree

General mathematics does not import the Hahn-series or surreal-number modules, and the Hahn-series
modules do not import the surreal-number modules. Examples, standalone entry points, and local test
modules are leaves. Imports are read from compiled artifacts.
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

private def generalRoots : Array Name := #[
  `ConwayRefinement.Algebra,
  `ConwayRefinement.Data,
  `ConwayRefinement.FieldTheory,
  `ConwayRefinement.LinearAlgebra,
  `ConwayRefinement.Order,
  `ConwayRefinement.RingTheory,
  `ConwayRefinement.SetTheory,
  `ConwayRefinement.Topology,
]

private def leafRoots : Array Name := #[
  `ConwayRefinement.Examples,
  `ConwayRefinement.Standalone,
]

private def isLocalTest (name : Name) : Bool :=
  name.components.contains `Tests

private def leafRank? (name : Name) : Option Nat :=
  if isLocalTest name then
    some leafRoots.size
  else
    leafRoots.findIdx? (·.isPrefixOf name)

private def layerOf? (name : Name) : Option (Nat × String) :=
  if (leafRank? name).isSome then
    none
  else if generalRoots.any (·.isPrefixOf name) then
    some (0, "general mathematics")
  else if (`ConwayRefinement.HahnSeries).isPrefixOf name then
    some (1, "Hahn series")
  else if (`ConwayRefinement.Surreal).isPrefixOf name then
    some (2, "surreal numbers")
  else
    none

/-- The forbidden direction, if this import crosses a stage boundary backwards. -/
private def crossesLayer (importer imported : Name) : Option String := do
  let (importerRank, importerLayer) ← layerOf? importer
  let (importedRank, importedLayer) ← layerOf? imported
  if importerRank < importedRank then
    some s!"{importerLayer} imports later stage {importedLayer}"
  else
    none

private def moduleImports (name : Name) : IO (Array Name) := do
  let olean ← findOLean name
  if !(← olean.pathExists) then
    throw <| IO.userError s!"layering: no compiled artifact for {name}; run `lake build` first."
  let (moduleData, _region) ← readModuleData olean
  return moduleData.imports.map (·.module)

public def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules ← collectLeanModules (auditedRoot.toString : System.FilePath)
  let mut violations := #[]
  let mut edges := 0
  for importer in modules do
    for imported in ← moduleImports importer do
      if !auditedRoot.isPrefixOf imported then
        continue
      edges := edges + 1
      if let some direction := crossesLayer importer imported then
        violations := violations.push s!"  {direction}: {importer} imports {imported}"
      if let some importedRank := leafRank? imported then
        if !(leafRank? importer).any (importedRank ≤ ·) then
          violations := violations.push
            s!"  leaf modules are imported backwards: {importer} imports {imported}"
  if modules.isEmpty then
    IO.eprintln "layering: no modules found."
    return 1
  if violations.isEmpty then
    IO.println s!"layering: {edges} project import(s) across {modules.size} modules \
      respect mathematical ownership; examples, standalone modules, and tests are leaves."
    return 0
  IO.eprintln s!"layering: {violations.size} violation(s):"
  for violation in violations do
    IO.eprintln violation
  return 1
