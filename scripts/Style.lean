/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit source formatting

Mathlib enforces line length and trailing whitespace with its text-based linter, which runs as a
separate executable over source text rather than during elaboration. So
`weak.linter.mathlibStandardSet` does not bring those rules with it, and `lake build` accepts a
200-character line. This executable reads the source tree and applies them.

Length is counted in characters, not bytes, so the mathematical symbols this development is written
in cost what they look like they cost.

Run `lake exe style --fix` to apply conservative fixes before reporting anything that still needs
manual judgment.
-/

private def maxLineLength : Nat := 100

private def auditedDirectories : Array System.FilePath := #["ConwayRefinement", "scripts"]

private partial def collectLeanFiles (directory : System.FilePath) :
    IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      files := files ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

/-- The audited files: everything under the audited directories, plus the library roots beside
them, which a directory walk alone would miss. -/
private def auditedFiles : IO (Array System.FilePath) := do
  let mut files := #[]
  for directory in auditedDirectories do
    files := files ++ (← collectLeanFiles directory)
    let root : System.FilePath := System.FilePath.mk (directory.toString ++ ".lean")
    if ← root.pathExists then
      files := files.push root
  return files

private def checkFile (file : System.FilePath) : IO (Array String) := do
  let mut violations := #[]
  let contents ← IO.FS.readFile file
  if !contents.isEmpty && !contents.endsWith "\n" then
    violations := violations.push s!"  {file}: no final newline"
  let mut lineNumber := 0
  for line in (← IO.FS.lines file) do
    lineNumber := lineNumber + 1
    if line.length > maxLineLength then
      violations := violations.push
        s!"  {file}:{lineNumber}: {line.length} characters, limit {maxLineLength}"
    if line.endsWith " " || line.endsWith "\t" then
      violations := violations.push s!"  {file}:{lineNumber}: trailing whitespace"
  return violations

private def runFixer (paths : List String) : IO UInt32 := do
  let output ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/fix-style.py"] ++ paths.toArray
  }
  unless output.stdout.isEmpty do
    IO.print output.stdout
    (← IO.getStdout).flush
  unless output.stderr.isEmpty do
    IO.eprint output.stderr
    (← IO.getStderr).flush
  return output.exitCode

public def main (args : List String) : IO UInt32 := do
  let fix := args.head? == some "--fix"
  unless args.isEmpty || fix do
    IO.eprintln "usage: lake exe style [--fix [PATH...]]"
    return 2
  if fix then
    let exitCode ← runFixer args.tail
    if exitCode != 0 then
      return exitCode
  let files ← auditedFiles
  if files.isEmpty then
    IO.eprintln "style: no source files found."
    return 1
  let mut violations := #[]
  for file in files do
    violations := violations ++ (← checkFile file)
  if violations.isEmpty then
    IO.println s!"style: {files.size} source file(s) within {maxLineLength} characters, \
      no trailing whitespace, final newline present."
    return 0
  IO.eprintln s!"style: {violations.size} formatting violation(s):"
  for violation in violations do
    IO.eprintln violation
  return 1
