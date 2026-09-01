#!/usr/bin/env bash

set -euo pipefail

blueprint_repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$blueprint_repo_root"

blueprint_action=${1:-build}
if [[ $# -gt 1 ]]; then
  echo "usage: scripts/blueprint.sh [build|render|check]" >&2
  exit 2
fi

blueprint_revision=${CONWAY_REFINEMENT_BLUEPRINT_SOURCE_REVISION:-$(git rev-parse HEAD)}
blueprint_revision_args=(--revision "$blueprint_revision")
if [[ ${CONWAY_REFINEMENT_BLUEPRINT_PUBLISHED:-0} == 1 ]]; then
  blueprint_revision_args+=(--published)
fi

case "$blueprint_action" in
  check)
    python3 scripts/_blueprint_revision.py --check
    python3 scripts/_blueprint.py --check
    exit
    ;;
  build)
    ;;
  render)
    if [[ ! -f .lake/build/blueprint/nodes.json ]]; then
      echo "blueprint: no cached node data; run scripts/blueprint.sh build first" >&2
      exit 1
    fi
    ;;
  *)
    echo "usage: scripts/blueprint.sh [build|render|check]" >&2
    exit 2
    ;;
esac

export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-946684800}"

python3 scripts/_blueprint_revision.py "${blueprint_revision_args[@]}"

if [[ "$blueprint_action" == build ]]; then
  python3 scripts/export-blueprint-data.py
fi
python3 scripts/_blueprint.py

python3 scripts/generate-blueprint-web.py
scripts/build-blueprint-reader.sh
node blueprint/src/web-reader/scripts/export-blueprint-source.mjs

if command -v tectonic >/dev/null 2>&1; then
  mkdir -p blueprint/print
  (
    cd blueprint/src
    tectonic --outdir ../print print.tex
  )
elif command -v latexmk >/dev/null 2>&1; then
  (cd blueprint/src && latexmk -pdf -outdir=../print print.tex)
else
  echo "blueprint: install Tectonic or latexmk to build the PDF" >&2
  exit 1
fi

cp blueprint/print/print.pdf blueprint/blueprint.pdf
cp blueprint/blueprint.pdf blueprint/web/blueprint.pdf

echo "blueprint: wrote blueprint/web/index.html"
echo "blueprint: wrote blueprint/web/dependency-graph.mmd"
echo "blueprint: wrote blueprint/web/dependency-graph.md"
echo "blueprint: wrote blueprint/web/dependency-graph-overview.mmd"
echo "blueprint: wrote blueprint/web/dependency-graph-*.mmd"
echo "blueprint: wrote blueprint/web/dependency-graph-*.md"
echo "blueprint: wrote blueprint/blueprint.pdf"
