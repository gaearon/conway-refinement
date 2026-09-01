/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit proofs of reader-facing standalone claims

The Mathlib-only and dependency-only statement modules at the roots of their trees and under
`Examples/` deliberately define propositions without importing their proofs. This audit discovers
every closed proposition in those modules and requires an exact entry in the module's final
formal-proof block and a theorem named `Claim.proof` in the sibling `FooProof` module. It also
checks that the kernel-checked theorem concludes with exactly that proposition applied to the same
parameters. Files under `Support/` are proof plumbing and are deliberately excluded.

Consequently, adding or removing an isolated claim without updating its proof block, or deleting or
renaming its proof, fails the audit. Predicate definitions with a mathematical input, such as
`IsReduced x`, are terminology rather than closed claims and are not selected. Run this executable
after `lake build`.
-/

open Lean

private structure ClaimFamily where
  statementModule : Name
  statementFile : System.FilePath
  proofModule : Name
  proofExists : Bool

private def isolatedDirs : Array System.FilePath := #[
  "ConwayRefinement/Standalone/Mathlib",
  "ConwayRefinement/Standalone/CombinatorialGames"
]

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private partial def collectLeanFiles
    (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      if !entry.path.components.contains "Support" then
        files := files ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

private def isProofFile (path : System.FilePath) : Bool :=
  path.toString.endsWith "Proof.lean"

private def discoverClaimFamilies : IO
    (Array ClaimFamily × Array Name × Array Name) := do
  let mut files := #[]
  for directory in isolatedDirs do
    files := files ++ (← collectLeanFiles directory)
  let modules := files.map pathToModule
  let proofModules := (files.filter isProofFile).map pathToModule
  let statementFiles := files.filter (!isProofFile ·)
  let families := statementFiles.map fun statementFile =>
    let statementModule := pathToModule statementFile
    let proofModule := Name.mkStr statementModule.getPrefix
      (statementModule.getString! ++ "Proof")
    {
      statementModule
      statementFile
      proofModule
      proofExists := proofModules.contains proofModule
    }
  let orphanProofs := proofModules.filter fun proofModule =>
    !families.any (·.proofModule == proofModule)
  return (families, modules, orphanProofs)

private def declarationType : ConstantInfo → Expr
  | .axiomInfo value | .defnInfo value | .thmInfo value | .opaqueInfo value |
      .ctorInfo value | .recInfo value | .inductInfo value => value.type
  | .quotInfo value => value.type

/-- A closed proposition may quantify over types and typeclass instances, but has no mathematical
input such as a series or an omnific integer. -/
private def isClosedProposition : Expr → Bool
  | .forallE _ domain body binderInfo =>
      (domain.isSort || binderInfo.isInstImplicit) && isClosedProposition body
  | .sort .zero => true
  | _ => false

private def expectedProofName (claim : Name) : Name := Name.mkStr claim "proof"

private def proofLine (claim proof : Name) : String :=
  s!"* `{claim.getString!}` → `{claim.getString!}.{proof.getString!}`"

private def containsText (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def forallArity : Expr → Nat
  | .forallE _ _ body _ => forallArity body + 1
  | _ => 0

private def forallBody : Expr → Expr
  | .forallE _ _ body _ => forallBody body
  | body => body

/-- The proof type must end in the claim applied to exactly the variables bound by the claim
definition's own parameter telescope, in the same order. -/
private def isExactProofType (claim : Name) (claimType proofType : Expr) : Bool :=
  let arity := forallArity claimType
  if forallArity proofType != arity then
    false
  else
    let result := forallBody proofType
    let arguments := result.getAppArgs
    result.getAppFn.constName? == some claim &&
      arguments.size == arity &&
      arguments.zipIdx.all fun (argument, index) =>
        argument == .bvar (arity - index - 1)

private def audit (families : Array ClaimFamily) (orphanProofs : Array Name) :
    CoreM (Array (Name × Name) × Array String) := do
  let environment ← getEnv
  let moduleNames := environment.allImportedModuleNames
  let mut links := #[]
  let mut violations := orphanProofs.map fun proofModule =>
    s!"{proofModule} has no `Foo` statement sibling"
  for family in families do
    let claims := environment.constants.fold (init := #[]) fun claims claim info => Id.run do
      let some checkedInfo := environment.checked.get.find? claim | claims
      let isClaimDeclaration := match checkedInfo with
        | .defnInfo _ | .inductInfo _ => true
        | _ => false
      if !isClaimDeclaration then
        return claims
      let some index := environment.getModuleIdxFor? claim | claims
      let some moduleName := moduleNames[index.toNat]? | claims
      if moduleName == family.statementModule &&
          isClosedProposition (declarationType info) then
        claims.push claim
      else
        claims
    if claims.isEmpty then
      violations := violations.push
        s!"{family.statementModule} is reader-facing but states no closed proposition"
      continue
    if !family.proofExists then
      violations := violations.push
        s!"{family.statementModule} has closed claims but no sibling {family.proofModule}"
    let source ← IO.FS.readFile family.statementFile
    let proofBlock := source.splitOn "## Formal proof"
    let expectedLines := claims.map fun claim =>
      proofLine claim (expectedProofName claim)
    match proofBlock with
    | [_before, block] =>
        if !containsText block s!"`{family.proofModule.getString!}`" then
          violations := violations.push
            s!"{family.statementFile}: formal-proof block omits sibling {family.proofModule}"
        for expected in expectedLines do
          if !containsText block expected then
            violations := violations.push
              s!"{family.statementFile}: formal-proof block omits `{expected}`"
        for line in block.splitOn "\n" do
          if line.startsWith "* `" && !expectedLines.contains line then
            violations := violations.push
              s!"{family.statementFile}: stale formal-proof line `{line}`"
    | _ =>
        violations := violations.push
          s!"{family.statementFile}: expected exactly one `## Formal proof` block"
    for claim in claims do
      let some info := environment.checked.get.find? claim | continue
      let proof := expectedProofName claim
      let some proofInfo := environment.checked.get.find? proof
        | violations := violations.push s!"{claim} has no proof {proof}"
          continue
      if isExactProofType claim (declarationType info) (declarationType proofInfo) then
        links := links.push (claim, proof)
      else
        violations := violations.push s!"{proof} does not prove {claim}"
  return (links, violations)

/-- Import the proof modules with environment extensions initialized. The resulting environment is
kept until this short-lived process exits, as initializer results may point into its regions. -/
private unsafe def withImportedEnv {α} (modules : Array Name) (action : CoreM α) : IO α := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let imports := modules.map fun module => ({ module } : Import)
  let environment ← importModules imports {} (trustLevel := 1024)
    (leakEnv := true) (loadExts := true)
  Prod.fst <$> Core.CoreM.toIO
    (ctx := { fileName := "<proof-links>", fileMap := default })
    (s := { env := environment }) action

public unsafe def main : IO UInt32 := do
  let (families, modules, orphanProofs) ← discoverClaimFamilies
  let (links, violations) ← withImportedEnv modules (audit families orphanProofs)
  if links.isEmpty then
    IO.eprintln "proof-links: discovered no isolated claims."
    return 1
  if !violations.isEmpty then
    IO.eprintln s!"proof-links: {violations.size} violation(s):"
    for violation in violations do
      IO.eprintln s!"  {violation}"
    return 1
  for (claim, proof) in links do
    IO.println s!"{claim} ← {proof}"
  IO.println s!"proof-links: verified {links.size} automatically discovered isolated claims."
  return 0
