#!/usr/bin/env bash
# Run kairos and Logos's logos on every .cpc file under the given paths
# (default: Logos's s-expression regressions) and report any file on which
# their verdicts or exit codes differ. kairos runs with --compare, so its own
# checker and Logos's checker are also compared within the one process.
#
#   scripts/compare-logos.sh [dir-or-file ...]
#
# Needs `lake build kairos Cpc/logos` first. Exits 1 on any disagreement.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
K="$ROOT/.lake/build/bin/kairos"
L="$ROOT/.lake/packages/Cpc/.lake/build/bin/logos"
for b in "$K" "$L"; do
  [ -x "$b" ] || { echo "missing $b: run 'lake build kairos Cpc/logos'" >&2; exit 2; }
done
[ $# -gt 0 ] || set -- "$ROOT/.lake/packages/Cpc/test/regress/sexp"
agree=0; differ=0
while IFS= read -r f; do
  k=$("$K" --compare "$f" 2>/dev/null); kc=$?
  l=$("$L" "$f" 2>/dev/null); lc=$?
  if [ "$k/$kc" = "$l/$lc" ]; then
    agree=$((agree + 1))
  else
    differ=$((differ + 1))
    echo "DIFFER $f: kairos=$k($kc) logos=$l($lc)"
  fi
done < <(find "$@" -name '*.cpc' -type f | sort)
echo "agree: $agree, differ: $differ"
[ "$differ" -eq 0 ]
