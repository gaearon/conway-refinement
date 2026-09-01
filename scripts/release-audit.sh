#!/usr/bin/env bash

set -euo pipefail

release_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
release_mode=full

if [[ $# -gt 1 || (${1:-} != "" && ${1:-} != "--quick") ]]; then
  echo "usage: scripts/release-audit.sh [--quick]" >&2
  exit 2
fi
if [[ ${1:-} == --quick ]]; then
  release_mode=quick
fi

cd "$release_root"
release_source=$(git rev-parse HEAD)

if [[ "$release_mode" == full ]]; then
  echo "release-audit: removing project build artifacts"
  lake clean ConwayRefinement
  scripts/publish-blueprint.sh
else
  scripts/publish-blueprint.sh --quick
fi

echo "release-audit: blueprint and dependency blob identifiers"
git hash-object \
  blueprint/src/content.tex \
  blueprint/src/revision.tex \
  blueprint/source-revision.json \
  blueprint/blueprint.pdf \
  lean-toolchain \
  lake-manifest.json
echo "release-audit: all automated release gates passed for $release_source"
