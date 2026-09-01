#!/usr/bin/env bash
# Adapted and modified from TauCeti's Apache-2.0-licensed scripts/lint-env.sh:
# https://github.com/TauCetiProject/TauCeti/blob/main/scripts/lint-env.sh
# Run Mathlib's default environment linters over every project declaration.
# The generated driver is deliberately not a module, so the linters can see private declarations.
# `docBlame` is excluded because imported docstrings are not present in the main olean.
# The report parser fails closed because imported initializers can print arbitrary output.
#
#   scripts/lint-env.sh            # check against the baseline
#   scripts/lint-env.sh --update   # rewrite the baseline from the current state
set -euo pipefail

cd "$(dirname "$0")/.."
BASELINE="scripts/lint-baseline.txt"
ALLOWLIST="scripts/lint-nolints-allowlist.txt"
UPDATE=0
[ "${1:-}" = "--update" ] && UPDATE=1

fail() { echo "::error::lint-env: $*"; echo "LINT-ENV: FAIL — $*"; exit 1; }

TMP="$(mktemp -d)" || fail "mktemp failed"
trap 'rm -rf "$TMP"' EXIT
DRIVER="$TMP/LintEnvDriver.lean"

# --- 0. validate the checked-in lists before spending time on elaboration ---------
[ -f "$ALLOWLIST" ] || fail "allowlist $ALLOWLIST not found — it must be checked in (empty is fine)"
LC_ALL=C sort -cu "$ALLOWLIST" 2>/dev/null \
  || fail "$ALLOWLIST is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $ALLOWLIST $ALLOWLIST"
if [ "$UPDATE" != 1 ]; then
  [ -f "$BASELINE" ] || fail "baseline $BASELINE not found — run scripts/lint-env.sh --update to create it"
  LC_ALL=C sort -cu "$BASELINE" 2>/dev/null \
    || fail "$BASELINE is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $BASELINE $BASELINE"
fi

NONCE="$(od -An -N16 -tx8 /dev/urandom | tr -d ' \n')" || fail "nonce generation failed"
MARKER="LINTENV-DRIVER-COMPLETE-$NONCE"

# The default environment-linter set minus docBlame (see the header), LC_ALL=C sorted. The driver
# verifies this against the environment and fails if the defaults have changed.
LINTERS="checkUnivs defLemma defsWithUnderscore deprecatedNoSince dupNamespace impossibleInstance nonClassInstance simpComm simpNF simpVarHead structureInType synTaut tacticDocs unusedArguments unusedHavesSuffices"
LINTERS_LEAN=$(printf '"%s", ' $LINTERS | sed 's/, $//')

MODULE_LIST="$TMP/modules.txt"
. scripts/source-modules.sh
primal_source_modules "$TMP/source-files" "$MODULE_LIST"
mods=$(wc -l < "$MODULE_LIST")
[ "${mods:-0}" -gt 0 ] || fail "found no ConwayRefinement/*.lean modules — the lint is miswired"

# --- 1. generate the legacy driver ---------------------------------------------------
# Order: freshness guard and nolint enumeration first (they run regardless of the lint's
# outcome), then the lint, then the nonce marker that proves the process survived the lint.
{
  echo "import Batteries.Tactic.Lint"
  sed 's/^/import /' "$MODULE_LIST"
  cat <<EOF

open Lean in
run_meta do
  let env ← getEnv
  let expected : Array String := #[$LINTERS_LEAN]
  let mut actual : Array String := #[]
  for (name, _, dflt) in Batteries.Tactic.Lint.batteriesLinterExt.getState env do
    if dflt && name != \`docBlame then actual := actual.push s!"{name}"
  actual := actual.qsort (· < ·)
  unless actual == expected do
    throwError "the default env-linter set changed: scripts/lint-env.sh runs {expected} \
      but the environment's defaults minus docBlame are {actual}; update LINTERS in \
      scripts/lint-env.sh and triage any new linter's findings"
  -- Report every project-local \`@[nolint]\`. Seeing none anywhere means this API moved.
  let modNames := env.allImportedModuleNames
  let mut nolints := 0
  let mut importedNolintEntries := 0
  for idx in [0:modNames.size] do
    let midx : ModuleIdx := idx
    let entries := Batteries.Tactic.Lint.nolintAttr.ext.getModuleEntries env midx
    importedNolintEntries := importedNolintEntries + entries.size
    if let some m := modNames[idx]? then
      if m == \`ConwayRefinement || (\`ConwayRefinement).isPrefixOf m then
        for (decl, linterNames) in entries do
          for l in linterNames do
            IO.println s!"NOLINT {l} {decl}"
            nolints := nolints + 1
  if importedNolintEntries == 0 then
    throwError "the @[nolint] enumeration is blind: no persistent nolint entries are visible \
      in ANY imported module, yet Batteries/Mathlib carry some — the attribute-extension API \
      moved; fix the enumeration in scripts/lint-env.sh, do not allowlist around this"
  IO.println s!"NOLINT-SUMMARY {nolints} $MARKER"

set_option linter.hashCommand false in
#lint only $LINTERS in ConwayRefinement

set_option linter.hashCommand false in
#eval IO.println "$MARKER"
EOF
} > "$DRIVER"

# --- 2. elaborate it (exit 1 from lean is EXPECTED when the linters report) --------
if lake env lean "$DRIVER" > "$TMP/out.txt" 2>&1; then
  status=0
else
  status=$?
fi

# --- 3. the nolint enumeration must have run and its tally must match its lines -----
nsummary=$(grep -c "^NOLINT-SUMMARY [0-9]* $MARKER\$" "$TMP/out.txt" || true)
[ "${nsummary:-0}" -eq 1 ] || { cat "$TMP/out.txt"; fail "driver failure: expected exactly one nonce-bearing NOLINT-SUMMARY line, found ${nsummary:-0} (lean exit $status)"; }
nolints=$(sed -n "s/^NOLINT-SUMMARY \([0-9]*\) $MARKER\$/\1/p" "$TMP/out.txt")
nnolint=$(grep -c '^NOLINT ' "$TMP/out.txt" || true)
[ "${nnolint:-0}" -eq "${nolints:-0}" ] \
  || { cat "$TMP/out.txt"; fail "driver failure: NOLINT-SUMMARY claims $nolints entr(y/ies) but ${nnolint:-0} NOLINT line(s) parsed"; }
LC_ALL=C sed -n 's/^NOLINT //p' "$TMP/out.txt" | LC_ALL=C sort -u > "$TMP/nolints.txt"
LC_ALL=C comm -23 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-new.txt"
if [ -s "$TMP/nolints-new.txt" ]; then
  echo "lint-env: @[nolint <linter>] application(s) under ConwayRefinement/ not accounted for in $ALLOWLIST (as '<linter> <declaration>'):"
  sed 's/^/  /' "$TMP/nolints-new.txt"
  echo "Silencing an environment linter bypasses the baseline. If a @[nolint <linter>] is truly"
  echo "warranted, add the '<linter> <declName>' line to $ALLOWLIST (LC_ALL=C sorted) in the"
  echo "same PR; that file, like this script, only changes through human-reviewed PRs."
  fail "unaccounted '@[nolint]' application(s); see the list above"
fi
LC_ALL=C comm -13 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-fixed.txt"
if [ -s "$TMP/nolints-fixed.txt" ]; then
  echo "lint-env: RATCHET — allowlist entr(y/ies) in $ALLOWLIST no longer correspond to a"
  echo "@[nolint] application; please delete these lines (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/nolints-fixed.txt"
fi

# --- 4. locate the lint report header, exactly once, of the shape matching the exit -
awk -v pfx="$DRIVER:" '
  BEGIN { hdr = "-- Found [0-9]+ errors? in [0-9]+ declarations \\(plus [0-9]+ automatically generated ones\\) in ConwayRefinement with [0-9]+ linters$" }
  {
    if (index($0, pfx) == 1) {
      rest = substr($0, length(pfx) + 1)
      if (rest ~ ("^[0-9]+:[0-9]+: error: " hdr)) { print NR " error " rest; next }
    }
    if ($0 ~ ("^" hdr)) print NR " bare " $0
  }' "$TMP/out.txt" > "$TMP/headers.txt"

nheaders=$(wc -l < "$TMP/headers.txt")
if [ "$nheaders" -ne 1 ]; then
  cat "$TMP/out.txt"
  if [ "$nheaders" -eq 0 ]; then
    fail "driver/linter failure: no lint report header found (lean exit $status) — see output above"
  fi
  fail "driver/linter failure: $(echo $nheaders | tr -d " ") report headers found (possible forged report) — see output above"
fi

hdr_lineno=$(awk '{print $1}' "$TMP/headers.txt")
hdr_kind=$(awk '{print $2}' "$TMP/headers.txt")
hdr_count=$(sed -n 's/^.*-- Found \([0-9]*\) errors\{0,1\} in .*/\1/p' "$TMP/headers.txt")
hdr_nlinters=$(sed -n 's/^.* in ConwayRefinement with \([0-9]*\) linters$/\1/p' "$TMP/headers.txt")
[ -n "$hdr_kind" ] && [ -n "$hdr_count" ] && [ -n "$hdr_nlinters" ] \
  || fail "internal error: could not re-parse the report header"

nlinters=$(echo "$LINTERS" | wc -w | tr -d ' ')
if [ "$hdr_nlinters" -ne "$nlinters" ]; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: report header claims $hdr_nlinters linter(s) but $nlinters were requested"
fi

tail -n +"$((hdr_lineno + 1))" "$TMP/out.txt" > "$TMP/report.txt"
if ! grep -qxF "$MARKER" "$TMP/report.txt"; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: driver did not run to completion (missing nonce marker after the report) — see output above"
fi

case "$hdr_kind:$status" in
  error:0) cat "$TMP/out.txt"; fail "driver/linter failure: lint reported errors but lean exited 0" ;;
  bare:0)  if [ "$hdr_count" -ne 0 ]; then
             cat "$TMP/out.txt"
             fail "driver/linter failure: unprefixed report claims $hdr_count violation(s)"
           fi ;;
  error:*) [ "$hdr_count" -gt 0 ] || { cat "$TMP/out.txt"; fail "driver/linter failure: error report with count 0"; } ;;
  bare:*)  cat "$TMP/out.txt"
           fail "driver/linter failure: lean exited $status but the lint itself reported no violations — some other error occurred; see output above" ;;
esac

# --- 5. parse the report region with the block-aware state machine ----------------
set +e
LC_ALL=C awk -v expected="$LINTERS" '
  BEGIN {
    n = split(expected, a, " ")
    for (i = 1; i <= n; i++) ok[a[i]] = 1
  }
  inblock {
    if ($0 ~ /^#check /) { code = 4; exit code }
    if ($0 ~ /-\/[[:space:]]*$/) inblock = 0
    next
  }
  /^\/- The `.*` linter reports:/ {
    l = $0; sub(/^\/- The `/, "", l); sub(/` linter reports:.*$/, "", l)
    if (!(l in ok)) { code = 5; exit code }
    if (l in seen)  { code = 6; exit code }
    seen[l] = 1; linter = l
    next
  }
  /^#check / {
    if (linter == "") { code = 3; exit code }
    name = $2; sub(/^@/, "", name)
    print linter " " name
    if ($0 !~ /-\/[[:space:]]*$/) inblock = 1
    next
  }
  END {
    if (code) exit code
    if (inblock) exit 7
  }
' "$TMP/report.txt" > "$TMP/violations.txt"
parse_rc=$?
set -e
if [ "$parse_rc" -ne 0 ]; then
  cat "$TMP/out.txt"
  case "$parse_rc" in
    3) fail "driver/linter failure: a #check block appeared before any linter section" ;;
    4) fail "driver/linter failure: a #check block opened before the previous one closed" ;;
    5) fail "driver/linter failure: a report section names a linter outside the requested set (possible forged section opener)" ;;
    6) fail "driver/linter failure: a linter section was opened twice (possible forged section opener)" ;;
    7) fail "driver/linter failure: unterminated #check block at the end of the report" ;;
    *) fail "driver/linter failure: report parsing failed (awk exit $parse_rc)" ;;
  esac
fi
nchecks=$(wc -l < "$TMP/violations.txt" | tr -d ' ')
if [ "${nchecks:-0}" -ne "$hdr_count" ]; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: header claims $hdr_count violation(s) but $nchecks #check block(s) parsed"
fi
LC_ALL=C sort -u -o "$TMP/violations.txt" "$TMP/violations.txt"
total=$(wc -l < "$TMP/violations.txt" | tr -d ' ')
echo "lint-env: linted $(echo $mods | tr -d " ") modules with $nlinters linters; $total (linter, declaration) violation(s)."

# --- 6. --update, or compare against the baseline --------------------------------
if [ "$UPDATE" = 1 ]; then
  cp "$TMP/violations.txt" "$BASELINE"
  echo "lint-env: wrote $total grandfathered entr(y/ies) to $BASELINE."
  exit 0
fi

LC_ALL=C comm -13 "$TMP/violations.txt" "$BASELINE" > "$TMP/fixed.txt"
if [ -s "$TMP/fixed.txt" ]; then
  echo
  echo "lint-env: RATCHET — $(wc -l < "$TMP/fixed.txt" | tr -d ' ') baseline entr(y/ies) no longer violate."
  echo "Please delete these lines from $BASELINE (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/fixed.txt"
fi

LC_ALL=C comm -23 "$TMP/violations.txt" "$BASELINE" > "$TMP/new.txt"
if [ -s "$TMP/new.txt" ]; then
  echo
  echo "lint-env: NEW violation(s) not in the grandfathered baseline (as '<linter> <declaration>'):"
  sed 's/^/  /' "$TMP/new.txt"
  echo
  awk 'NR==FNR { want[$0]=1; next }
       /^\/- The `[A-Za-z0-9_]+` linter reports:/ {
         l = $0; sub(/^\/- The `/, "", l); sub(/` linter reports:.*$/, "", l)
         pending = "  [" l "]"
       }
       /^#check / {
         name = $2; sub(/^@/, "", name)
         p = ((l " " name) in want)
         if (p && pending != "") { print pending; pending = "" }
       }
       p { print "  " $0 }
       p && /-\/[[:space:]]*$/ { p = 0; print "" }' "$TMP/new.txt" "$TMP/report.txt"
  echo
  echo "Fix the declaration per the explanation above, or — as a deliberate, commented"
  echo "exception — use @[nolint <linter>] plus a '<linter> <declName>' line in $ALLOWLIST."
  fail "$(wc -l < "$TMP/new.txt" | tr -d ' ') new violation(s); see the list above"
fi

echo "LINT-ENV: PASS — no new violations ($total grandfathered, $(wc -l < "$TMP/fixed.txt" | tr -d ' ') ratchetable)."
