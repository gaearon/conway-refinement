#!/usr/bin/env bash
set -euo pipefail

mode=check
if [[ ${1:-} == --update ]]; then
  mode=update
  shift
elif [[ ${1:-} == -* ]]; then
  echo "usage: scripts/check-palomar-challenge.sh [--update] [REPO [CHALLENGE [FOOTER]]]" >&2
  exit 2
fi
if [[ $# -gt 3 ]]; then
  echo "usage: scripts/check-palomar-challenge.sh [--update] [REPO [CHALLENGE [FOOTER]]]" >&2
  exit 2
fi

repo_root="${1:-$(git rev-parse --show-toplevel)}"
source_file="$repo_root/ConwayRefinement/Standalone/Mathlib/InlineConwayRefinement.lean"
challenge_file="${2:-$repo_root/Challenge.lean}"
footer_file="${3:-$repo_root/scripts/palomar-challenge-footer.txt}"

proof_marker=$(awk '$0 == "## Formal proof" { count += 1; line = NR }
  END { printf "%d:%d\n", count, line }' "$source_file")
proof_marker_count=${proof_marker%%:*}
proof_marker_line=${proof_marker#*:}
if [[ $proof_marker_count -ne 1 ]]; then
  echo "Expected exactly one final '## Formal proof' note in $source_file." >&2
  exit 1
fi

proof_opening_line=$((proof_marker_line - 1))
proof_separator_line=$((proof_marker_line - 2))
if [[ $(sed -n "${proof_opening_line}p" "$source_file") != '/-!' ]] ||
    [[ -n $(sed -n "${proof_separator_line}p" "$source_file") ]] ||
    [[ $(tail -n 1 "$source_file") != '-/' ]]; then
  echo "The final proof-link note in $source_file has an unexpected shape." >&2
  exit 1
fi

source_prefix_lines=$((proof_marker_line - 3))
render_challenge() {
  head -n "$source_prefix_lines" "$source_file"
  command cat "$footer_file"
}

if [[ $mode == update ]]; then
  palomar_tmp=$(mktemp "${TMPDIR:-/tmp}/palomar-challenge.XXXXXX")
  trap 'rm -f -- "$palomar_tmp"' EXIT
  render_challenge > "$palomar_tmp"
  chmod 0644 "$palomar_tmp"
  mv "$palomar_tmp" "$challenge_file"
  trap - EXIT
  echo "Updated Challenge.lean from the statement source and Palomar footer."
  exit 0
fi

if ! cmp -s "$challenge_file" <(render_challenge); then
  echo "Challenge.lean has drifted from the Mathlib-only statement or Palomar footer." >&2
  echo "Regenerate it with scripts/check-palomar-challenge.sh --update." >&2
  exit 1
fi

echo "Challenge.lean matches the statement source (without its proof-link note) and footer."
