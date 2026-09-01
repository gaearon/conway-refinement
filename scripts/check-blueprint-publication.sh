#!/usr/bin/env bash

set -euo pipefail

publication_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$publication_root"

if [[ $# -ne 0 ]]; then
  echo "usage: scripts/check-blueprint-publication.sh" >&2
  exit 2
fi

publication_expected=${CONWAY_REFINEMENT_BLUEPRINT_SOURCE_REVISION:-$(git rev-parse HEAD)}
python3 scripts/_blueprint_revision.py --check

publication_source=$(python3 -c \
  'import json; print(json.load(open("blueprint/source-revision.json"))["revision"])')
publication_status=$(python3 -c \
  'import json; print(json.load(open("blueprint/source-revision.json"))["published"])')

if [[ "$publication_status" != True ]]; then
  echo "blueprint-publication: source revision is marked as an unpublished preview" >&2
  exit 1
fi
if [[ "$publication_source" != "$publication_expected" ]]; then
  echo "blueprint-publication: generated guide records the wrong source revision" >&2
  echo "  recorded: $publication_source" >&2
  echo "  expected: $publication_expected" >&2
  exit 1
fi

publication_outputs=(
  blueprint/blueprint.pdf
  blueprint/web/blueprint.pdf
  blueprint/web/data.json
  blueprint/web/index.html
)
for publication_output in "${publication_outputs[@]}"; do
  if [[ ! -f "$publication_output" ]]; then
    echo "blueprint-publication: missing generated output $publication_output" >&2
    exit 1
  fi
done
cmp -s blueprint/blueprint.pdf blueprint/web/blueprint.pdf

python3 - "$publication_source" <<'PY'
import json
import sys

source = json.load(open("blueprint/source-revision.json"))
web = json.load(open("blueprint/web/data.json"))
if web.get("source") != source:
    raise SystemExit("blueprint-publication: web guide records different source metadata")
if source["revision"] != sys.argv[1]:
    raise SystemExit("blueprint-publication: inconsistent source revision")
PY

if rg -F 'github.com/gaearon/conway-refinement/blob/main/' blueprint/web README.md >/dev/null; then
  echo "blueprint-publication: generated guide contains a mutable blob/main source link" >&2
  exit 1
fi
if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "blueprint-publication: generation changed tracked source files" >&2
  git status --short >&2
  exit 1
fi

echo "blueprint-publication: generated guide documents passing source $publication_source"
