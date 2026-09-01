#!/usr/bin/env bash

set -euo pipefail

reader_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
reader_source="$reader_root/blueprint/src/web-reader"
cd "$reader_source"

if [[ -x node_modules/.bin/vite ]] && command -v node >/dev/null 2>&1; then
  node scripts/typeset-blueprint-data.mjs
  node_modules/.bin/vite build
elif command -v node >/dev/null 2>&1 && command -v pnpm >/dev/null 2>&1; then
  node scripts/typeset-blueprint-data.mjs
  pnpm exec vite build
elif command -v node >/dev/null 2>&1 && command -v corepack >/dev/null 2>&1; then
  node scripts/typeset-blueprint-data.mjs
  corepack pnpm exec vite build
else
  echo "blueprint reader: install Node.js and pnpm, then run pnpm install in $reader_source" >&2
  exit 1
fi

cp "$reader_root/blueprint/web/index.html" "$reader_root/blueprint/web/index.template.html"
mkdir -p "$reader_root/blueprint/web/mathjax/fonts"
cp -R node_modules/mathjax/es5/output/chtml/fonts/woff-v2 \
  "$reader_root/blueprint/web/mathjax/fonts/"
if [[ -f "$reader_root/blueprint/web/data.json" ]]; then
  node scripts/embed-blueprint-reader.mjs
fi
