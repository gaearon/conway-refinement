#!/usr/bin/env bash
# Adapted and modified from TauCeti's Apache-2.0-licensed scripts/source-modules.sh:
# https://github.com/TauCetiProject/TauCeti/blob/main/scripts/source-modules.sh
# Shared, fail-closed discovery of the Lean modules under ConwayRefinement/.
#
# primal_source_modules FILES MODULES writes the validated source paths as a NUL-delimited
# list to FILES and the corresponding Lean module names, one per line and LC_ALL=C sorted, to
# MODULES. Callers choose their own temporary destinations.
#
# The lakefile glob `ConwayRefinement.*` is authoritative for what is built; this function is the
# matching authority for what is linted, so the two cannot drift apart through a hand-edited
# import list. It refuses symlinks (a symlinked path could smuggle a file from outside the tree
# into the linted set, or duplicate a module under a second name) and refuses any path that is
# not a well-formed module path, so the derived module names are exactly those Lake builds.

primal_source_modules() {
  local files_out="$1"
  local modules_out="$2"
  local symlinks_out="${files_out}.symlinks"
  local module_path_re="^ConwayRefinement(/[A-Za-z_][A-Za-z0-9_']*)+\.lean$"
  local file module

  # Portable across bash 3.2 (macOS) and 4+: no mapfile, no associative arrays. Module paths
  # are validated below to contain no whitespace or newlines, so a newline-delimited
  # intermediate is safe once validated; the NUL-delimited FILES output is still produced for
  # callers that want it.
  find ConwayRefinement -type f -name '*.lean' -print0 | LC_ALL=C sort -z > "$files_out"
  find ConwayRefinement -type l -print0 | LC_ALL=C sort -z > "$symlinks_out"
  if [ -s "$symlinks_out" ]; then
    printf 'source-modules: refusing symlinked source path %q\n' \
      "$(tr '\0' '\n' < "$symlinks_out" | head -n 1)" >&2
    return 1
  fi
  if [ ! -s "$files_out" ]; then
    echo 'source-modules: found no ConwayRefinement source files; the audit is miswired.' >&2
    return 1
  fi

  : > "$modules_out"
  # A NUL inside a path would split it here, producing a fragment that fails the regex below.
  while IFS= read -r -d '' file; do
    if [[ ! $file =~ $module_path_re ]]; then
      printf 'source-modules: refusing non-module source path %q\n' "$file" >&2
      return 1
    fi
    module="${file%.lean}"
    printf '%s\n' "${module//\//.}" >> "$modules_out"
  done < "$files_out"
}
