#!/usr/bin/env bash

set -euo pipefail

audit_repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
audit_logs=$(mktemp -d "${TMPDIR:-/tmp}/conway-refinement-audit-probes.XXXXXX")
audit_probe=""
audit_proof_source="$audit_repo_root/ConwayRefinement/Standalone/Mathlib/HahnSeriesGCD.lean"
audit_proof_backup="$audit_logs/HahnSeriesGCD.lean"
audit_proof_changed=false
audit_blueprint_data_source="$audit_repo_root/.lake/build/blueprint/nodes.json"
audit_blueprint_data_backup="$audit_logs/nodes.json"
audit_blueprint_data_changed=false
audit_blueprint_phases_source="$audit_repo_root/blueprint/phases.json"
audit_blueprint_phases_backup="$audit_logs/phases.json"
audit_blueprint_phases_changed=false
audit_blueprint_reference_lean_source="$audit_repo_root/ConwayRefinement/Algebra/GradedRing"
audit_blueprint_reference_lean_source+="/OrdinalGenerators.lean"
audit_blueprint_reference_lean_backup="$audit_logs/OrdinalGenerators.lean"
audit_blueprint_reference_lean_changed=false

audit_cleanup() {
  if [[ "$audit_proof_changed" == true ]]; then
    cp "$audit_proof_backup" "$audit_proof_source"
  fi
  if [[ "$audit_blueprint_data_changed" == true ]]; then
    cp "$audit_blueprint_data_backup" "$audit_blueprint_data_source"
  fi
  if [[ "$audit_blueprint_phases_changed" == true ]]; then
    cp "$audit_blueprint_phases_backup" "$audit_blueprint_phases_source"
  fi
  if [[ "$audit_blueprint_reference_lean_changed" == true ]]; then
    cp "$audit_blueprint_reference_lean_backup" "$audit_blueprint_reference_lean_source"
  fi
  if [[ -f "$audit_logs/content.tex" ]]; then
    cp "$audit_logs/content.tex" blueprint/src/content.tex
  fi
  if [[ -n "$audit_probe" ]]; then
    rm -f -- "$audit_repo_root/$audit_probe"
  fi
  rm -rf -- "$audit_logs"
}
trap audit_cleanup EXIT

audit_fail() {
  echo "audit-probes: $1" >&2
  exit 1
}

audit_require_absent() {
  if [[ -e "$audit_repo_root/$1" ]]; then
    audit_fail "refusing to overwrite existing probe path $1"
  fi
}

audit_expect_rejection() {
  local name=$1
  local expected=$2
  shift 2
  if "$@" > "$audit_logs/$name.log" 2>&1; then
    audit_fail "$name accepted its negative control"
  fi
  if ! grep -q "$expected" "$audit_logs/$name.log"; then
    audit_fail "$name failed, but did not identify its negative control"
  fi
}

cd "$audit_repo_root"

if ! git diff --quiet || ! git diff --cached --quiet; then
  audit_fail "tracked files must be clean before mutation probes"
fi

# Palomar Challenge: the checked-in statement copy must not drift from its source and footer.
audit_probe=ProbePalomarChallenge.lean
audit_require_absent "$audit_probe"
cp Challenge.lean "$audit_probe"
printf '%s\n' '' '-- negative-control drift' >> "$audit_probe"
audit_expect_rejection palomar-challenge 'has drifted' \
  scripts/check-palomar-challenge.sh "$audit_repo_root" "$audit_repo_root/$audit_probe"
rm -f -- "$audit_probe"
audit_probe=""

# Palomar compatibility: a reachable module-private helper changes name when the statement is
# compiled under the Challenge module name.
audit_probe=ConwayRefinement/ProbePalomarCompatibility.lean
audit_require_absent "$audit_probe"
printf '%s\n' \
  '/-' \
  'Copyright (c) 2026 Dan Abramov. All rights reserved.' \
  'Released under Apache 2.0 license as described in the file LICENSE.' \
  'Authors: Dan Abramov' \
  '-/' \
  'module' \
  '' \
  '/-! # Palomar-compatibility negative control -/' \
  '' \
  'private def hiddenPalomarStatement : Prop := True' \
  '' \
  'public def probePalomarStatement : Prop := hiddenPalomarStatement' \
  > "$audit_probe"
lake build ConwayRefinement.ProbePalomarCompatibility
audit_expect_rejection palomar-compatibility \
  '_private.ConwayRefinement.ProbePalomarCompatibility' \
  lake exe palomar-compatibility \
    ConwayRefinement.ProbePalomarCompatibility \
    probePalomarStatement
rm -f -- "$audit_probe"
audit_probe=""

# Style: conservative fixes repair prose, comma-separated code, whitespace, and the final newline.
audit_probe=ConwayRefinement/ProbeStyleFix.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module  ' '' \
  '/-! This deliberately overlong prose comment contains enough ordinary words for the style fixer to wrap it safely without changing Lean syntax or mathematical notation. -/' \
  '' > "$audit_probe"
printf '%s' \
  '#check (Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add, Nat.add)' \
  >> "$audit_probe"
if ! lake exe style --fix "$audit_probe" > "$audit_logs/style-fix.log" 2>&1; then
  audit_fail "style --fix did not repair its positive control"
fi
if ! lake exe style >> "$audit_logs/style-fix.log" 2>&1; then
  audit_fail "style --fix left a formatting violation in its positive control"
fi
if ! lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false "$audit_probe" \
    >> "$audit_logs/style-fix.log" 2>&1; then
  audit_fail "style --fix did not preserve valid Lean syntax"
fi
rm -f -- "$audit_probe"
audit_probe=""

# Style: an overlong token has no safe automatic line break.
audit_probe=ConwayRefinement/ProbeStyle.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' "/-! # $(printf 'a%.0s' $(seq 1 110)) -/" > "$audit_probe"
audit_expect_rejection style ProbeStyle.lean lake exe style
audit_expect_rejection style-fix-unfixable ProbeStyle.lean \
  lake exe style --fix "$audit_probe"
rm -f -- "$audit_probe"
audit_probe=""

# Blueprint: generated navigation cannot drift from the inline Lean annotations.
cp blueprint/src/content.tex "$audit_logs/content.tex"
printf '%s\n' '% negative-control drift' >> blueprint/src/content.tex
audit_expect_rejection blueprint 'generated file is stale' \
  scripts/blueprint.sh check
cp "$audit_logs/content.tex" blueprint/src/content.tex

# Blueprint: all formats share one generated immutable source revision.
cp blueprint/src/revision.tex "$audit_logs/revision.tex"
printf '%s\n' '% negative-control drift' >> blueprint/src/revision.tex
audit_expect_rejection blueprint-revision 'generated file is stale' \
  scripts/blueprint.sh check
cp "$audit_logs/revision.tex" blueprint/src/revision.tex

# Blueprint: every selected node carries readable proof prose.
cp "$audit_blueprint_data_source" "$audit_blueprint_data_backup"
audit_blueprint_data_changed=true
python3 - "$audit_blueprint_data_source" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
records = json.loads(path.read_text())
record = next(record for record in records if record["label"] == "lem:generate")
record["proof"] = ""
path.write_text(json.dumps(records))
PY
audit_expect_rejection blueprint-proof 'nodes have no proof prose: lem:generate' \
  scripts/blueprint.sh check
cp "$audit_blueprint_data_backup" "$audit_blueprint_data_source"
audit_blueprint_data_changed=false

# Blueprint: every visible dependency is cited in the corresponding proof prose.
cp "$audit_blueprint_data_source" "$audit_blueprint_data_backup"
audit_blueprint_data_changed=true
cp "$audit_blueprint_reference_lean_source" "$audit_blueprint_reference_lean_backup"
audit_blueprint_reference_lean_changed=true
python3 - "$audit_blueprint_data_source" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
records = json.loads(path.read_text())
record = next(
    record
    for record in records
    if record["label"] == "lem:variables-of-homogeneous-relation-have-smaller-degree"
)
needle = r"\ref{lem:minimal-generators-relation-has-no-linear-term}"
if needle not in record["proof"]:
    raise SystemExit("blueprint reference probe could not find its proof reference")
record["proof"] = record["proof"].replace(needle, "the preceding theorem", 1)
path.write_text(json.dumps(records))
PY
audit_expect_rejection blueprint-reference-write \
  'proof references must equal shallow blueprint dependencies' \
  scripts/blueprint.sh check
if ! grep -Fq \
    'FIXME_blueprint_review_why_does_proof_depend_on := ' \
    "$audit_blueprint_reference_lean_source"; then
  audit_fail "blueprint-reference did not record its missing dependency in the Lean source"
fi
audit_expect_rejection blueprint-reference-lean 'unexpected identifier' \
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
    "$audit_blueprint_reference_lean_source"
audit_expect_rejection blueprint-reference 'unresolved dependency TODO parameters' \
  scripts/blueprint.sh check
cp "$audit_blueprint_reference_lean_backup" "$audit_blueprint_reference_lean_source"
audit_blueprint_reference_lean_changed=false
cp "$audit_blueprint_data_backup" "$audit_blueprint_data_source"
audit_blueprint_data_changed=false

# Blueprint: selected labels are unique.
cp "$audit_blueprint_data_source" "$audit_blueprint_data_backup"
audit_blueprint_data_changed=true
python3 - "$audit_blueprint_data_source" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
records = json.loads(path.read_text())
records.append(next(record for record in records if record["label"] == "lem:generate"))
path.write_text(json.dumps(records))
PY
audit_expect_rejection blueprint-declaration \
  'duplicate label' scripts/blueprint.sh check
cp "$audit_blueprint_data_backup" "$audit_blueprint_data_source"
audit_blueprint_data_changed=false

# Blueprint: the phase manifest includes the Highlights metadata.
cp "$audit_blueprint_phases_source" "$audit_blueprint_phases_backup"
audit_blueprint_phases_changed=true
python3 - "$audit_blueprint_phases_source" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
payload = json.loads(path.read_text())
del payload["highlights"]
path.write_text(json.dumps(payload))
PY
audit_expect_rejection blueprint-highlights-manifest \
  'manifest root must contain exactly' scripts/blueprint.sh check
cp "$audit_blueprint_phases_backup" "$audit_blueprint_phases_source"
audit_blueprint_phases_changed=false

# Blueprint: the phase manifest has unique stable slugs.
cp "$audit_blueprint_phases_source" "$audit_blueprint_phases_backup"
audit_blueprint_phases_changed=true
python3 - "$audit_blueprint_phases_source" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
payload = json.loads(path.read_text())
payload["phases"][1]["slug"] = payload["phases"][0]["slug"]
path.write_text(json.dumps(payload))
PY
audit_expect_rejection blueprint-phase-manifest \
  'duplicate slug' scripts/blueprint.sh check
cp "$audit_blueprint_phases_backup" "$audit_blueprint_phases_source"
audit_blueprint_phases_changed=false

# Blueprint: phase assignments cover a forward mathematical reading order.
cp "$audit_blueprint_data_source" "$audit_blueprint_data_backup"
audit_blueprint_data_changed=true
python3 - "$audit_blueprint_data_source" <<'PY'
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

path = Path(sys.argv[1])
records = json.loads(path.read_text())
sys.path.insert(0, str(Path.cwd() / "scripts"))
from _blueprint import PHASES

phase_counts = Counter(record["phase"] for record in records)
records_by_name = {record["name"]: record for record in records}
records_by_module = defaultdict(list)
for record in records:
    records_by_module[record["module"]].append(record)
for target in records:
    dependencies = target["statementDependencies"] + target["proofDependencies"]
    for dependency in dependencies:
        source = records_by_name[dependency]
        source_records = records_by_module[source["module"]]
        source_phase = source["phase"]
        if source["module"] == target["module"]:
            continue
        if target["phase"] == PHASES[-1] or source_phase == PHASES[-1]:
            continue
        if phase_counts[source_phase] == len(source_records):
            continue
        for source_record in source_records:
            source_record["phase"] = PHASES[-1]
        path.write_text(json.dumps(records))
        raise SystemExit(0)
raise SystemExit("blueprint phase probe could not find a movable dependency")
PY
audit_expect_rejection blueprint-phase \
  'dependencies run backwards between phases' scripts/blueprint.sh check
cp "$audit_blueprint_data_backup" "$audit_blueprint_data_source"
audit_blueprint_data_changed=false
cp "$audit_blueprint_reference_lean_backup" "$audit_blueprint_reference_lean_source"
audit_blueprint_reference_lean_changed=false

# Documentation: editorial state in a core module comment.
audit_probe=ConwayRefinement/HahnSeries/Germ/AlgebraicIndependence/ProbeDocumentation.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' '/-! Temporary manuscript correspondence. -/' > "$audit_probe"
audit_expect_rejection documentation ProbeDocumentation.lean lake exe documentation
rm -f -- "$audit_probe"
audit_probe=""

# Documentation: repository status in a published-source module comment.
audit_probe=ConwayRefinement/HahnSeries/Factorization/ProbeDocumentation.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' '/-! This statement is source-unverified. -/' > "$audit_probe"
audit_expect_rejection documentation ProbeDocumentation.lean lake exe documentation
rm -f -- "$audit_probe"
audit_probe=""

# Documentation: project coinage in mathematical prose.
audit_probe=ConwayRefinement/Algebra/ProbeDocumentation.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' '/-! A principal layer of the associated graded ring. -/' > "$audit_probe"
audit_expect_rejection documentation ProbeDocumentation.lean lake exe documentation
rm -f -- "$audit_probe"
audit_probe=""

# Documentation: forbidden ordinal coinages are rejected case-insensitively.
audit_probe=ConwayRefinement/Algebra/ProbeDocumentation.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' '/-! A NON-SUMMAND in the Hessenberg summands. -/' > "$audit_probe"
audit_expect_rejection documentation-ordinal-coinage ProbeDocumentation.lean lake exe documentation
rm -f -- "$audit_probe"
audit_probe=""

# Documentation: project coinages are rejected throughout the source tree.
audit_probe=ConwayRefinement/Standalone/ProbeDocumentation.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' '/-! A principal RV-space of the associated graded ring. -/' > "$audit_probe"
audit_expect_rejection documentation-project-wide ProbeDocumentation.lean lake exe documentation
rm -f -- "$audit_probe"
audit_probe=""

# Documentation: standalone proof plumbing under Support is intentionally outside the prose audit.
audit_probe=ConwayRefinement/Standalone/Mathlib/Support/ProbeDocumentation.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' '/-! A principal RV-space used only inside a proof. -/' > "$audit_probe"
lake exe documentation > "$audit_logs/documentation-standalone-support.log" 2>&1
rm -f -- "$audit_probe"
audit_probe=""

# Module system: a source file that compiles without opting into the module system.
audit_probe=ConwayRefinement/ProbeModuleSystem.lean
audit_require_absent "$audit_probe"
printf '%s\n' \
  '/-' \
  'Copyright (c) 2026 Dan Abramov. All rights reserved.' \
  'Released under Apache 2.0 license as described in the file LICENSE.' \
  'Authors: Dan Abramov' \
  '-/' \
  '' \
  '/-! # Module-system negative control -/' \
  '' \
  'public theorem moduleSystemProbe : True := True.intro' \
  > "$audit_probe"
lake build ConwayRefinement.ProbeModuleSystem
audit_expect_rejection module-system ProbeModuleSystem lake exe module-system
rm -f -- "$audit_probe"
audit_probe=""

# Standalone Mathlib: a statement reaching into a non-Mathlib dependency.
audit_probe=ConwayRefinement/Standalone/Mathlib/Probe.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' 'import CombinatorialGames.Surreal.Basic' > "$audit_probe"
lake build ConwayRefinement.Standalone.Mathlib.Probe
audit_expect_rejection standalone-mathlib Standalone.Mathlib.Probe lake exe standalone-mathlib
rm -f -- "$audit_probe"
audit_probe=""

# Standalone Mathlib: a statement may not import project-local Support plumbing.
audit_probe=ConwayRefinement/Standalone/Mathlib/Probe.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' \
  'import ConwayRefinement.Standalone.Mathlib.Support.OrderedAddGroup' > "$audit_probe"
lake build ConwayRefinement.Standalone.Mathlib.Probe
audit_expect_rejection standalone-mathlib Standalone.Mathlib.Probe lake exe standalone-mathlib
rm -f -- "$audit_probe"
audit_probe=""

# Standalone Mathlib: proof plumbing under Support is intentionally outside the statement audit.
audit_probe=ConwayRefinement/Standalone/Mathlib/Support/Probe.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' 'import ConwayRefinement.HahnSeries.OrderType' > "$audit_probe"
lake build ConwayRefinement.Standalone.Mathlib.Support.Probe
lake exe standalone-mathlib > "$audit_logs/standalone-mathlib-support.log" 2>&1
rm -f -- "$audit_probe"
audit_probe=""

# Standalone CombinatorialGames: a statement reaching into the development.
audit_probe=ConwayRefinement/Standalone/CombinatorialGames/Probe.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' 'import ConwayRefinement.HahnSeries.OrderType' > "$audit_probe"
lake build ConwayRefinement.Standalone.CombinatorialGames.Probe
audit_expect_rejection standalone-combinatorial-games Standalone.CombinatorialGames.Probe \
  lake exe standalone-combinatorial-games
rm -f -- "$audit_probe"
audit_probe=""

# Standalone CombinatorialGames: a statement may not import project-local Support plumbing.
audit_probe=ConwayRefinement/Standalone/CombinatorialGames/Probe.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' \
  'import ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificIntegers' > "$audit_probe"
lake build ConwayRefinement.Standalone.CombinatorialGames.Probe
audit_expect_rejection standalone-combinatorial-games Standalone.CombinatorialGames.Probe \
  lake exe standalone-combinatorial-games
rm -f -- "$audit_probe"
audit_probe=""

# Standalone CombinatorialGames: proof plumbing under Support may import the main proof.
audit_probe=ConwayRefinement/Standalone/CombinatorialGames/Support/Probe.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' 'import ConwayRefinement.HahnSeries.OrderType' > "$audit_probe"
lake build ConwayRefinement.Standalone.CombinatorialGames.Support.Probe
lake exe standalone-combinatorial-games \
  > "$audit_logs/standalone-combinatorial-games-support.log" 2>&1
rm -f -- "$audit_probe"
audit_probe=""

# Layering: a general algebra module reaching into the surreal-number modules.
audit_probe=ConwayRefinement/Algebra/ProbeLayering.lean
audit_require_absent "$audit_probe"
printf '%s\n' 'module' '' 'import ConwayRefinement.Surreal.OmnificInteger.Basic' > "$audit_probe"
lake build ConwayRefinement.Algebra.ProbeLayering
audit_expect_rejection layering ProbeLayering lake exe layering
rm -f -- "$audit_probe"
audit_probe=""

# Axioms: a custom axiom. A `sorry` would be rejected during the build and would not exercise
# the axiom auditor itself.
audit_probe=ConwayRefinement/ProbeAxiom.lean
audit_require_absent "$audit_probe"
printf '%s\n' \
  '/-' \
  'Copyright (c) 2026 Dan Abramov. All rights reserved.' \
  'Released under Apache 2.0 license as described in the file LICENSE.' \
  'Authors: Dan Abramov' \
  '-/' \
  'module' \
  '' \
  '/-! # Axiom negative control -/' \
  '' \
  'public axiom probeAxiom : True' \
  > "$audit_probe"
lake build ConwayRefinement.ProbeAxiom
audit_expect_rejection axioms probeAxiom lake exe axioms
rm -f -- "$audit_probe"
audit_probe=""

# Proof links: a new closed proposition in an isolated statement module must have a matching
# theorem in the proof sibling.
cp "$audit_proof_source" "$audit_proof_backup"
audit_proof_changed=true
printf '%s\n' \
  '' \
  'namespace ConwayRefinement' \
  '/-- Negative control: an isolated claim with no proof. -/' \
  'def ProbeUnprovedClaim : Prop := True' \
  'end ConwayRefinement' \
  >> "$audit_proof_source"
lake build ConwayRefinement.Standalone.Mathlib.HahnSeriesGCDProof
audit_expect_rejection proof-links 'ProbeUnprovedClaim has no proof' lake exe proof-links
cp "$audit_proof_backup" "$audit_proof_source"
audit_proof_changed=false
lake build ConwayRefinement.Standalone.Mathlib.HahnSeriesGCDProof

# Environment lint: a simp lemma that simp can already prove. The driver is generated from the
# source tree, so a fresh module is linted without registration anywhere.
audit_probe=ConwayRefinement/ProbeLintEnv.lean
audit_require_absent "$audit_probe"
printf '%s\n' \
  '/-' \
  'Copyright (c) 2026 Dan Abramov. All rights reserved.' \
  'Released under Apache 2.0 license as described in the file LICENSE.' \
  'Authors: Dan Abramov' \
  '-/' \
  'module' \
  '' \
  '/-! # Environment-lint negative control -/' \
  '' \
  '/-- Negative control: simp proves this, so it is not in simp-normal form. -/' \
  '@[simp] public theorem probeLintEnvSimpNF (n : Nat) : n * 1 + 0 = n := by simp' \
  > "$audit_probe"
lake build ConwayRefinement.ProbeLintEnv
audit_expect_rejection lint-env 'simpNF probeLintEnvSimpNF' scripts/lint-env.sh
rm -f -- "$audit_probe"
audit_probe=""

# Environment lint: a `@[nolint]` that is not in the allowlist must not silence the gate.
audit_probe=ConwayRefinement/ProbeLintEnv.lean
audit_require_absent "$audit_probe"
printf '%s\n' \
  '/-' \
  'Copyright (c) 2026 Dan Abramov. All rights reserved.' \
  'Released under Apache 2.0 license as described in the file LICENSE.' \
  'Authors: Dan Abramov' \
  '-/' \
  'module' \
  '' \
  'public import Batteries.Tactic.Lint' \
  '' \
  '/-! # Environment-lint negative control -/' \
  '' \
  '/-- Negative control: an unaccounted nolint. -/' \
  '@[nolint simpNF] public theorem probeLintEnvNolint (n : Nat) : n = n := rfl' \
  > "$audit_probe"
lake build ConwayRefinement.ProbeLintEnv
audit_expect_rejection lint-env 'simpNF probeLintEnvNolint' scripts/lint-env.sh
rm -f -- "$audit_probe"
audit_probe=""

# Environment lint: an initializer that prints a forged passing report header at import time.
# The linted code runs inside the driver, so its output must not be able to pass for the report.
audit_probe=ConwayRefinement/ProbeLintEnv.lean
audit_require_absent "$audit_probe"
printf '%s\n' \
  '/-' \
  'Copyright (c) 2026 Dan Abramov. All rights reserved.' \
  'Released under Apache 2.0 license as described in the file LICENSE.' \
  'Authors: Dan Abramov' \
  '-/' \
  'module' \
  '' \
  '/-! # Environment-lint negative control -/' \
  '' \
  '/-- Negative control: a forged report header printed at import time. -/' \
  '@[init] public def probeLintEnvForge : IO Unit :=' \
  '  IO.println ("-- Found 0 errors in 1 declarations (plus 0 automatically generated ones) " ++' \
  '    "in ConwayRefinement with 15 linters")' \
  > "$audit_probe"
lake build ConwayRefinement.ProbeLintEnv
audit_expect_rejection lint-env 'possible forged report' scripts/lint-env.sh
rm -f -- "$audit_probe"
audit_probe=""

if ! git diff --quiet || ! git diff --cached --quiet; then
  audit_fail "mutation probes did not restore the tracked tree"
fi

echo "audit-probes: every audit rejected its negative control"
