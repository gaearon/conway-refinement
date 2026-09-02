/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import ImportGraph.Lean.WithImportModules

/-!
# Audit Palomar statement compatibility

Palomar compiles `Challenge.lean` and `Solution.lean` as different modules, then compares every
constant reachable from the advertised statement. A compiler-generated module-private constant
has a different name in those two modules even when their source text is identical.

This executable rejects module-private constants in the project declaration closure reachable
from Conway's refinement conjecture. Run it after `lake build`.
-/

open Lean

private structure AuditConfig where
  moduleName : Name
  root : Name

private def defaultConfig : AuditConfig where
  moduleName := `ConwayRefinement.Standalone.Mathlib.InlineConwayRefinement
  root := `ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture

private def AuditConfig.privatePrefix (config : AuditConfig) : Name :=
  ("_private." ++ config.moduleName.toString).toName

private def parseConfig : List String → Except String AuditConfig
  | [] => .ok defaultConfig
  | [moduleName, root] =>
      .ok {
        moduleName := moduleName.toName
        root := root.toName
      }
  | _ => .error
      "usage: lake exe palomar-compatibility [MODULE ROOT]"

private def declarationDependencies : ConstantInfo → Array Name
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors

private structure AuditResult where
  audited : Nat
  missing : Array String
  violations : Array String

private def declaredInModule
    (environment : Environment) (moduleName declarationName : Name) : Bool :=
  match environment.getModuleIdxFor? declarationName with
  | some index => environment.allImportedModuleNames[index.toNat]? == some moduleName
  | none => false

private def audit (config : AuditConfig) : CoreM AuditResult := do
  let environment ← getEnv
  let mut pending := #[config.root]
  let mut seen : NameSet := {}
  let mut missing := #[]
  let mut violations := #[]
  while !pending.isEmpty do
    let declarationName := pending.back!
    pending := pending.pop
    if !seen.contains declarationName then
      seen := seen.insert declarationName
      match environment.find? declarationName with
      | none => missing := missing.push declarationName.toString
      | some declarationInfo =>
          for dependency in declarationDependencies declarationInfo do
            if config.privatePrefix.isPrefixOf dependency then
              violations := violations.push s!"  {declarationName} → {dependency}"
            else if declaredInModule environment config.moduleName dependency &&
                !seen.contains dependency then
              pending := pending.push dependency
  return { audited := seen.size, missing, violations }

private def runAudit (config : AuditConfig) : IO AuditResult :=
  Core.withImportModules #[config.moduleName] (audit config)

public def main (args : List String) : IO UInt32 :=
  match parseConfig args with
  | .error message => do
      IO.eprintln message
      return (2 : UInt32)
  | .ok config => do
      try
        let result ← runAudit config
        if !result.missing.isEmpty then
          IO.eprintln s!"palomar-compatibility: missing {result.missing.size} declaration(s):"
          for declarationName in result.missing do
            IO.eprintln s!"  {declarationName}"
          return (1 : UInt32)
        if !result.violations.isEmpty then
          IO.eprintln (s!"palomar-compatibility: {result.violations.size} module-private " ++
            "dependency violation(s):")
          for violation in result.violations do
            IO.eprintln violation
          return (1 : UInt32)
        IO.println (s!"palomar-compatibility: checked {result.audited} declarations; the " ++
          "statement closure is portable between the Challenge and Solution modules.")
        return (0 : UInt32)
      catch error =>
        IO.eprintln s!"palomar-compatibility: {error}"
        return (1 : UInt32)
