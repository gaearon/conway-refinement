/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit documentation vocabulary

Documentation in the mathematical source layers should describe objects, hypotheses, theorems,
and public interfaces. Source modules may record provenance and precise differences from printed
statements. Editorial labels and development-status prose do not belong in those descriptions.
This audit rejects a small set of phrases that have repeatedly marked such comments.

The check is deliberately lexical and narrow. It prevents known failure modes; mathematical
accuracy and clarity still require review.
-/

private structure ForbiddenPhrase where
  text : String
  explanation : String

private def statusPhrases : Array ForbiddenPhrase := #[
  ⟨"manuscript", "describe the present mathematics, not an external document"⟩,
  ⟨"paper-facing", "use a mathematical description of the statement"⟩,
  ⟨"source-facing", "use a mathematical description of the statement"⟩,
  ⟨"project-facing", "name the mathematical construction directly"⟩,
  ⟨"draft", "remove development or editorial status"⟩,
  ⟨"frozen", "remove temporary API or proof status"⟩,
  ⟨"single remaining input", "state the actual hypothesis"⟩,
  ⟨"lands it", "remove branch or integration status"⟩,
  ⟨"previously uncheckable", "describe the current interface"⟩,
  ⟨"deduplicated at integration", "remove integration history"⟩,
  ⟨"until the in-tree", "describe the current dependency"⟩,
  ⟨"project audit", "state the mathematical defect directly"⟩,
  ⟨"this project", "name the mathematical construction directly"⟩,
  ⟨"project's", "name the mathematical construction directly"⟩,
  ⟨"repository", "omit repository-state prose from mathematical sources"⟩,
  ⟨"implementation", "state the mathematical construction or property directly"⟩,
  ⟨"source-unverified", "verify the source or omit the claim"⟩,
  ⟨"available transcription", "cite the checked mathematical source"⟩,
  ⟨"first paper consumer", "describe the mathematical use directly"⟩,
  ⟨"first consumer", "describe the mathematical use directly"⟩,
  ⟨"first concrete client", "omit implementation chronology"⟩,
  ⟨"outstanding prerequisite", "state the present hypothesis"⟩,
  ⟨"future work", "omit dependency-roadmap status"⟩,
  ⟨"future universe", "state the missing mathematical implication directly"⟩,
  ⟨"fidelity:", "state the mathematical property without an editorial label"⟩
]

private def terminologyPhrases : Array ForbiddenPhrase := #[
  ⟨"principal ring",
    "write `P̂`, or say `the subring of principal elements of RV̂` at first use"⟩,
  ⟨"principal layer",
    "write `P_α`, or say `the K-vector space of principal RV-elements of degree α`"⟩,
  ⟨"principal-layer",
    "write `P_α`, or say `the K-vector space of principal RV-elements of degree α`"⟩,
  ⟨"principal rv-space",
    "write `P_α`, or say `the K-vector space of principal RV-elements of degree α`"⟩,
  ⟨"successor layer",
    "write `P_α` for successor `α`, or say `homogeneous component of successor degree`"⟩,
  ⟨"successor-layer",
    "write `P_α` for successor `α`, or say `homogeneous component of successor degree`"⟩,
  ⟨"fixed layer", "say `homogeneous component` and specify its degree when needed"⟩,
  ⟨"fixed-layer", "say `homogeneous component` and specify its degree when needed"⟩,
  ⟨"degree layer", "say `homogeneous component of degree α`"⟩,
  ⟨"degree-layer", "say `homogeneous component of degree α`"⟩,
  ⟨"source layer", "say `source homogeneous component`"⟩,
  ⟨"source-layer", "say `source homogeneous component`"⟩,
  ⟨"layer `p_", "write `P_α`, or say `homogeneous component P_α`"⟩,
  ⟨"layers `p_", "write `P_α`, or say `homogeneous components P_α`"⟩,
  ⟨"layer base change", "say `base change on a homogeneous component`"⟩,
  ⟨"layer map", "say `map on a homogeneous component`"⟩,
  ⟨"shell assembler",
    "state the theorem integrating prescribed homogeneous classes on a discrete cutoff set"⟩,
  ⟨"assembler", "state the mathematical interpolation or summation theorem directly"⟩,
  ⟨"shell", "say `translated strict upper truncation` or name the interval-supported series"⟩,
  ⟨"principal lift", "say `principal series representing ...` or state the exact truncation bound"⟩,
  ⟨"principallift",
    "rename the declaration after the exact principal-series or truncation property"⟩,
  ⟨"support rank",
    "say `Cantor–Bendixson rank of the closed support` and specify the point when needed"⟩,
  ⟨"support-rank",
    "name the Cantor–Bendixson rank, value, valuation, or associated graded ring exactly"⟩,
  ⟨"supportrank", "rename the declaration after the Cantor–Bendixson rank it computes"⟩,
  ⟨"limit degree", "say that the degree is a limit ordinal"⟩,
  ⟨"limit-degree", "say that the degree is a limit ordinal"⟩,
  ⟨"limitdegree", "rename the declaration to say that the degree is a limit ordinal"⟩,
  ⟨"limit relation", "say `relation whose degree is a limit ordinal`"⟩,
  ⟨"limit-relation", "say `relation whose degree is a limit ordinal`"⟩,
  ⟨"limitrelation", "rename the declaration to describe a relation of limit-ordinal degree"⟩,
  ⟨"limit correction", "name the cofactor construction and its induction directly"⟩,
  ⟨"limit-correction", "name the cofactor construction and its induction directly"⟩,
  ⟨"limitcorrection", "rename the declaration after the cofactor construction"⟩,
  ⟨"principal piece", "say `disjoint convex piece` and state the rank property"⟩,
  ⟨"principal-piece", "say `disjoint convex piece` and state the rank property"⟩,
  ⟨"principalpiece", "rename the declaration after the disjoint convex cover"⟩,
  ⟨"summand low degree", "state the algebraic-order relation between the low-degree parts"⟩,
  ⟨"summand-low-degree", "state the algebraic-order relation between the low-degree parts"⟩,
  ⟨"summandlowdegree", "rename the declaration after the exact algebraic-order predicate"⟩,
  ⟨"full low degree", "state that the low-degree part equals the specified ordinal"⟩,
  ⟨"fulllowdegree", "rename the declaration after the low-degree-part equality"⟩,
  ⟨"nonsummand", "state the failure of the algebraic-order relation"⟩,
  ⟨"partial generator", "say which variables contribute to the partial derivative"⟩,
  ⟨"partialgenerator", "rename the declaration after contribution to the partial derivative"⟩,
  ⟨"patching", "describe the sum or the construction from local cofactors"⟩,
  ⟨"patched", "describe the sum or the construction from local cofactors"⟩,
  ⟨"cofactor patch", "describe the sum or the construction from local cofactors"⟩,
  ⟨"natural summand",
    "use the algebraic order for Hessenberg addition, or state `∃ γ, α ⊕ γ = β`"⟩,
  ⟨"naturalsummand",
    "rename the declaration after the algebraic order or the displayed Hessenberg decomposition"⟩,
  ⟨"hessenberg summand",
    "use the algebraic order for Hessenberg addition, or state `∃ γ, α ⊕ γ = β`"⟩,
  ⟨"hessenbergsummand",
    "rename the declaration after the algebraic order or the displayed Hessenberg decomposition"⟩,
  ⟨"non-summand", "state that no ordinal `γ` satisfies `α ⊕ γ = β`"⟩,
  ⟨"no greatest nonzero archimedean class",
    "say `no least nonzero Archimedean class in the magnitude order`"⟩,
  ⟨"archimedean classes have no greatest",
    "say `Archimedean classes have no least element in the magnitude order`"⟩,
  ⟨"archimedean classes with no greatest",
    "say `Archimedean classes with no least member in the magnitude order`"⟩,
  ⟨"archimedean classes having no greatest",
    "say `Archimedean classes having no least member in the magnitude order`"⟩,
  ⟨"archimedean classes has no greatest",
    "say `Archimedean classes have no least member in the magnitude order`"⟩,
  ⟨"cofinal in the original class order",
    "say `coinitial in the magnitude order` when describing arbitrarily small classes"⟩,
  ⟨"complete ordered abelian group",
    "say explicitly that the additive uniformity is Cauchy complete"⟩,
  ⟨"complete ordered exponent group",
    "say `ordered exponent group that is Cauchy complete`"⟩,
  ⟨"complete ordered rational vector space",
    "say `ordered rational vector space that is Cauchy complete`"⟩,
  ⟨"complete ordered uniform additive group",
    "say explicitly that the ordered uniform additive group is Cauchy complete"⟩,
  ⟨"complete ordered uniform exponent group",
    "say explicitly that the ordered uniform exponent group is Cauchy complete"⟩
]

private def statusDirectories : Array System.FilePath :=
  #["ConwayRefinement"]

private def terminologyDirectories : Array System.FilePath :=
  #["ConwayRefinement"]

private partial def collectLeanFiles (directory : System.FilePath) :
    IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      files := files ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

private def isStandaloneSupportFile (file : System.FilePath) : Bool :=
  let path := "/" ++ file.toString.replace "\\" "/"
  path.contains "/Standalone/" && path.contains "/Support/"

private def leanFilesIn (directories : Array System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for directory in directories do
    let directoryFiles ← collectLeanFiles directory
    files := files ++ directoryFiles.filter (!isStandaloneSupportFile ·)
  return files

private def checkFile (file : System.FilePath) (phrases : Array ForbiddenPhrase) :
    IO (Array String) := do
  let mut violations := #[]
  let mut lineNumber := 0
  for line in (← IO.FS.lines file) do
    lineNumber := lineNumber + 1
    let lower := line.toLower
    for phrase in phrases do
      if lower.contains phrase.text then
        violations := violations.push
          s!"  {file}:{lineNumber}: `{phrase.text}`: {phrase.explanation}"
  return violations

public def main : IO UInt32 := do
  let statusFiles ← leanFilesIn statusDirectories
  let terminologyFiles ← leanFilesIn terminologyDirectories
  if statusFiles.isEmpty || terminologyFiles.isEmpty then
    IO.eprintln "documentation: no source files found."
    return 1
  let mut violations := #[]
  for file in statusFiles do
    violations := violations ++ (← checkFile file statusPhrases)
  for file in terminologyFiles do
    violations := violations ++ (← checkFile file terminologyPhrases)
  if violations.isEmpty then
    IO.println s!"documentation: {statusFiles.size} mathematical source file(s) contain no \
      unstable labels or development-status phrases; {terminologyFiles.size} project source \
      file(s) use the required terminology."
    return 0
  IO.eprintln s!"documentation: {violations.size} documentation phrase violation(s):"
  for violation in violations do
    IO.eprintln violation
  return 1
