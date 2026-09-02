#!/usr/bin/env bash

set -euo pipefail

publication_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
publication_mode=full

if [[ $# -gt 1 || (${1:-} != "" && ${1:-} != "--quick") ]]; then
  echo "usage: scripts/publish-blueprint.sh [--quick]" >&2
  exit 2
fi
if [[ ${1:-} == --quick ]]; then
  publication_mode=quick
fi

cd "$publication_root"

if ! git diff --quiet || ! git diff --cached --quiet || \
    [[ -n $(git ls-files --others --exclude-standard) ]]; then
  echo "publish-blueprint: commit or discard every source change before publishing" >&2
  git status --short >&2
  exit 1
fi

publication_source=$(git rev-parse HEAD)
echo "publish-blueprint: checking source commit $publication_source"

scripts/check-palomar-challenge.sh
lake build

publication_audits=(
  palomar-compatibility
  axioms
  module-system
  standalone-mathlib
  standalone-combinatorial-games
  proof-links
  style
  documentation
  layering
)
for publication_audit in "${publication_audits[@]}"; do
  lake exe "$publication_audit"
done
scripts/lint-env.sh

echo "publish-blueprint: generating immutable links to ${publication_source:0:12}"
CONWAY_REFINEMENT_BLUEPRINT_SOURCE_REVISION="$publication_source" \
  CONWAY_REFINEMENT_BLUEPRINT_PUBLISHED=1 scripts/blueprint.sh build

if [[ "$publication_mode" == full ]]; then
  scripts/audit-probes.sh
fi

if [[ $(git rev-parse HEAD) != "$publication_source" ]] || \
    ! git diff --quiet || ! git diff --cached --quiet || \
    [[ -n $(git ls-files --others --exclude-standard) ]]; then
  echo "publish-blueprint: source changed while the checks ran" >&2
  git status --short >&2
  exit 1
fi

CONWAY_REFINEMENT_BLUEPRINT_SOURCE_REVISION="$publication_source" \
  scripts/check-blueprint-publication.sh

echo "publish-blueprint: web guide is in blueprint/web"
echo "publish-blueprint: PDF is blueprint/blueprint.pdf"
