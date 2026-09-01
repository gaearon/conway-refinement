/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
/-
Adapted and modified from TauCeti's Apache-2.0-licensed `scripts/Axioms.lean`:
https://github.com/TauCetiProject/TauCeti/blob/main/scripts/Axioms.lean
-/
module

import ImportGraph.Lean.WithImportModules
import Lean.Util.CollectAxioms

/-!
# Audit the axioms used by every declaration

This executable checks every declaration compiled from the project module root and rejects any
transitive axiom dependency other than `propext`, `Classical.choice`, or `Quot.sound`. `sorry`
is forbidden everywhere, in a declaration's type and in its proof, directly and transitively.

Modules are enumerated from the source tree rather than reached through imports, so a module that
nothing imports is audited too. Run this after `lake build`; it audits the resulting artifacts.
-/

open Lean

private def auditedRoot : Name := `ConwayRefinement

private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

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
  return #[auditedRoot] ++ (← collectLeanModules (auditedRoot.toString : System.FilePath))

private def withImportedEnv {α} (modules : Array Name) (action : CoreM α) : IO α := do
  Core.withImportModules modules action

private def inAuditedLibrary (moduleName : Name) : Bool :=
  moduleName == auditedRoot || auditedRoot.isPrefixOf moduleName

private def declarationType : ConstantInfo → Expr
  | .axiomInfo value | .defnInfo value | .thmInfo value | .opaqueInfo value |
      .ctorInfo value | .recInfo value | .inductInfo value => value.type
  | .quotInfo value => value.type

private def declarationValue? : ConstantInfo → Option Expr
  | .defnInfo value | .thmInfo value | .opaqueInfo value => some value.value
  | _ => none

private def directlyUsesSorry (expression : Expr) : Bool :=
  expression.getUsedConstants.contains ``sorryAx

private structure AxiomReachability where
  reachesSorry : Bool := false
  reachesForbidden : Bool := false
deriving BEq

private def AxiomReachability.merge
    (left right : AxiomReachability) : AxiomReachability where
  reachesSorry := left.reachesSorry || right.reachesSorry
  reachesForbidden := left.reachesForbidden || right.reachesForbidden

private def expressionDependencies (expression : Expr) : Array Name :=
  expression.getUsedConstants

private def declarationDependencies : ConstantInfo → Array Name
  | .axiomInfo value => expressionDependencies value.type
  | .defnInfo value =>
      expressionDependencies value.type ++ expressionDependencies value.value
  | .thmInfo value =>
      expressionDependencies value.type ++ expressionDependencies value.value
  | .opaqueInfo value =>
      expressionDependencies value.type ++ expressionDependencies value.value
  | .quotInfo _ => #[]
  | .ctorInfo value => expressionDependencies value.type
  | .recInfo value => expressionDependencies value.type
  | .inductInfo value => expressionDependencies value.type ++ value.ctors

private def axiomReachability (name : Name) : AxiomReachability :=
  if name == ``sorryAx then
    { reachesSorry := true }
  else if allowedAxioms.contains name then
    {}
  else
    { reachesForbidden := true }

/-- Compute exact reachability of `sorryAx` and non-allowlisted axioms for all constants reachable
from `roots`. A reverse-graph worklist propagates both flags to a fixed point, so recursive
declaration clusters cannot be misclassified by a provisional depth-first-search cache entry. -/
private def buildAxiomReachability
    (environment : Environment) (roots : Array Name) : NameMap AxiomReachability := Id.run do
  let mut seen : NameSet := {}
  let mut reverseDependencies : NameMap (Array Name) := {}
  let mut discoveryQueue := roots
  let mut discoveryIndex := 0
  while h : discoveryIndex < discoveryQueue.size do
    let name := discoveryQueue[discoveryIndex]
    discoveryIndex := discoveryIndex + 1
    if !seen.contains name then
      seen := seen.insert name
      if let some declarationInfo := environment.checked.get.find? name then
        for dependency in declarationDependencies declarationInfo do
          let dependents := reverseDependencies.find? dependency |>.getD #[]
          reverseDependencies := reverseDependencies.insert dependency (dependents.push name)
          if !seen.contains dependency then
            discoveryQueue := discoveryQueue.push dependency

  let mut result : NameMap AxiomReachability := {}
  let mut propagationQueue := #[]
  for name in seen do
    if let some (.axiomInfo _) := environment.checked.get.find? name then
      let reachability := axiomReachability name
      if reachability != {} then
        result := result.insert name reachability
        propagationQueue := propagationQueue.push name

  let mut propagationIndex := 0
  while h : propagationIndex < propagationQueue.size do
    let name := propagationQueue[propagationIndex]
    propagationIndex := propagationIndex + 1
    let reachability := result.find? name |>.getD {}
    for dependent in reverseDependencies.find? name |>.getD #[] do
      let previous := result.find? dependent |>.getD {}
      let updated := previous.merge reachability
      if updated != previous then
        result := result.insert dependent updated
        propagationQueue := propagationQueue.push dependent
  return result

private def expressionReachability
    (reachability : NameMap AxiomReachability) (expression : Expr) : AxiomReachability :=
  expression.getUsedConstants.foldl (init := {}) fun result dependency ↦
    result.merge (reachability.find? dependency |>.getD {})

private structure AuditResult where
  audited : Nat
  violations : Array String

private def audit : CoreM AuditResult := do
  let environment ← getEnv
  let moduleNames := environment.allImportedModuleNames
  let candidates := environment.constants.fold (init := #[]) fun names declarationName _ =>
    match environment.getModuleIdxFor? declarationName with
    | some index =>
        match moduleNames[index.toNat]? with
        | some moduleName =>
            if inAuditedLibrary moduleName then
              names.push declarationName
            else
              names
        | none => names
    | none => names
  let mut violations := #[]
  let reachability := buildAxiomReachability environment candidates
  for declarationName in candidates do
    let some declarationInfo := environment.checked.get.find? declarationName
      | violations := violations.push s!"  {declarationName} → missing constant information"
        continue
    let typeReachability :=
      expressionReachability reachability (declarationType declarationInfo)
    let valueReachability :=
      (declarationValue? declarationInfo).map (expressionReachability reachability) |>.getD {}
    let declarationReachability := reachability.find? declarationName |>.getD {}
    let proofUsesSorryDirectly :=
      (declarationValue? declarationInfo).any directlyUsesSorry

    if declarationReachability.reachesForbidden then
      let axioms ← collectAxioms declarationName
      let forbiddenAxioms := axioms.filter fun name ↦
        name != ``sorryAx && !allowedAxioms.contains name
      violations := violations.push
        s!"  {declarationName} → forbidden axioms {forbiddenAxioms.toList}"
    if typeReachability.reachesSorry then
      violations := violations.push
        s!"  {declarationName} → transitive `sorry` dependency in its type"
    if proofUsesSorryDirectly then
      violations := violations.push s!"  {declarationName} → uses `sorry`"
    else if valueReachability.reachesSorry then
      violations := violations.push
        s!"  {declarationName} → transitive `sorry` dependency in its proof"

  return { audited := candidates.size, violations }

public def main : IO UInt32 := do
  let modules ← auditedModules
  let result ← withImportedEnv modules audit
  if result.audited == 0 then
    IO.eprintln s!"axioms: audited no declarations under {auditedRoot}."
    return 1
  if result.violations.isEmpty then
    IO.println (s!"axioms: audited {result.audited} ConwayRefinement declarations; " ++
      s!"every declaration reduces to {allowedAxioms}.")
    return 0
  IO.eprintln s!"axioms: {result.violations.size} proof-trust violation(s):"
  for violation in result.violations do
    IO.eprintln violation
  IO.eprintln s!"globally allowed axioms: {allowedAxioms}"
  return 1
