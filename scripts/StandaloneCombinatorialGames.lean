/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit standalone CombinatorialGames modules

Every reader-facing module under `ConwayRefinement.Standalone.CombinatorialGames` may import
Mathlib and the pinned external dependencies, including CombinatorialGames, but no module from
this project. Sibling modules ending in `Proof` and modules under `Support/` are proof plumbing and
are excluded as audit roots, but a reader-facing module may not import them. This executable walks
compiled import closures, so the boundary is checked transitively rather than inferred from
source-text imports.
-/

open Lean

private def standaloneCombinatorialGamesDir : System.FilePath :=
  "ConwayRefinement" / "Standalone" / "CombinatorialGames"

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private def collectTopLevelLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if !(← entry.path.isDir) && entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

private def standaloneCombinatorialGamesRootsIO : IO (Array Name) :=
  collectTopLevelLeanModules standaloneCombinatorialGamesDir

private def isProofModule (name : Name) : Bool := name.getString!.endsWith "Proof"

private def forbiddenRoots : Array Name := #[`ConwayRefinement, `scripts]

/-- The region is retained because the returned names point into its compacted module data. -/
private def moduleImports (name : Name) : IO (Option (Array Name)) := do
  let olean ← findOLean name
  if !(← olean.pathExists) then
    return none
  let (moduleData, _region) ← readModuleData olean
  return some (moduleData.imports.map (·.module))

private partial def walk (root : Name) (pending : List Name) (seen : Std.HashSet Name)
    (violations : Array Name) : IO (Std.HashSet Name × Array Name) := do
  match pending with
  | [] => return (seen, violations)
  | name :: rest =>
    if seen.contains name then
      walk root rest seen violations
    else if name != root && forbiddenRoots.any (·.isPrefixOf name) then
      walk root rest (seen.insert name) (violations.push name)
    else
      match ← moduleImports name with
      | none =>
        throw <| IO.userError
          s!"standalone-combinatorial-games: no compiled artifact for {name}; \
            run `lake build` first."
      | some imports => walk root (imports.toList ++ rest) (seen.insert name) violations

public def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let roots := (← standaloneCombinatorialGamesRootsIO).filter fun name => !isProofModule name
  let mut violations := #[]
  let mut audited := 0
  for root in roots do
    let (closure, bad) ← walk root [root] {} #[]
    audited := audited + closure.size
    for name in bad do
      violations := violations.push (root, name)
  if roots.isEmpty then
    IO.eprintln "standalone-combinatorial-games: no roots configured."
    return 1
  if violations.isEmpty then
    IO.println s!"standalone-combinatorial-games: {roots.size} module(s) import only \
      CombinatorialGames and Mathlib \
      ({audited} modules in their import closures)."
    return 0
  IO.eprintln s!"standalone-combinatorial-games: {violations.size} forbidden import(s):"
  for (root, name) in violations do
    IO.eprintln s!"  {root} transitively imports {name}"
  return 1
