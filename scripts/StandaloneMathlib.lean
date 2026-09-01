/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit standalone Mathlib modules

Reader-facing modules in `ConwayRefinement.Standalone.Mathlib` state results so that a reader can
check them knowing only Mathlib, and compile them against a bare Mathlib. Sibling modules ending
in `Proof` and modules under `Support/` are proof plumbing and are excluded as audit roots, but a
reader-facing module may not import them.

This executable walks the transitive imports recorded in the compiled artifacts and rejects any
module under a forbidden root. It reads oleans rather than source text, so it sees what was
actually elaborated. Run it after `lake build`.
-/

open Lean

/-- The directory whose non-proof modules must rest on Mathlib alone. -/
private def standaloneMathlibDir : System.FilePath := "ConwayRefinement" / "Standalone" / "Mathlib"

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private def collectTopLevelLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if !(← entry.path.isDir) && entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

private def standaloneMathlibRootsIO : IO (Array Name) :=
  collectTopLevelLeanModules standaloneMathlibDir

private def isProofModule (name : Name) : Bool := name.getString!.endsWith "Proof"

/-- Roots that must not appear in a Mathlib-only module's import closure: this project itself,
and the dependencies Mathlib does not carry. -/
private def forbiddenRoots : Array Name := #[`ConwayRefinement, `scripts, `CombinatorialGames]

/-- The region backing a compacted `ModuleData` is deliberately not freed: the `Name`s returned
here point into it, unlike the scalar that `module-system` reads. This is a short-lived audit. -/
private def moduleImports (name : Name) : IO (Option (Array Name)) := do
  let olean ← findOLean name
  if !(← olean.pathExists) then
    return none
  let (moduleData, _region) ← readModuleData olean
  return some (moduleData.imports.map (·.module))

/-- Walk the import closure of `root`, recording forbidden modules rather than descending into
them. Not descending is what keeps this audit independent of the state of the project's own
build: a forbidden import is reported from the importing side, using only artifacts that a
Mathlib-only closure is expected to contain. -/
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
          s!"standalone-mathlib: no compiled artifact for {name}; run `lake build` first."
      | some imports => walk root (imports.toList ++ rest) (seen.insert name) violations

public def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mathlibOnlyRoots := (← standaloneMathlibRootsIO).filter fun name => !isProofModule name
  let mut violations := #[]
  let mut audited := 0
  for root in mathlibOnlyRoots do
    let (closure, bad) ← walk root [root] {} #[]
    audited := audited + closure.size
    for name in bad do
      violations := violations.push (root, name)
  if mathlibOnlyRoots.isEmpty then
    IO.eprintln "standalone-mathlib: no roots configured."
    return 1
  if violations.isEmpty then
    IO.println s!"standalone-mathlib: {mathlibOnlyRoots.size} module(s) rest on Mathlib alone \
      ({audited} modules in their import closures)."
    return 0
  IO.eprintln s!"standalone-mathlib: {violations.size} forbidden import(s):"
  for (root, name) in violations do
    IO.eprintln s!"  {root} transitively imports {name}"
  return 1
