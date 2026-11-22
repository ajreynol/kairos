#!/usr/bin/env bash
# Regenerate Kairos/Gen/ from the CPC signature of the pinned Logos.
#
#   1. Run Logos's own Lean pipeline (Ethos's tools/eoc/driver.py, with
#      Logos's semantics) on Logos's install/defs/Cpc.cached.eo, for Cpc and
#      for CpcMini (the rules install-sig.sh --mini picks). This yields
#      lean-cpc-final.eo, the exact input of the lean-meta stage.
#   2. Check that the Lean it yields is Logos's committed Cpc/ and CpcMini/,
#      modulo the header and module name install-sig.sh adds. So the final
#      signature Kairos compiles is the one Logos's checker was compiled from.
#   3. Run kairos-eoc on CpcMini's final signature; install into Kairos/Gen/.
#
# Usage: scripts/generate.sh [--check]
#   --check   write nothing; exit 1 if Kairos/Gen/ is not what would be generated
#
# Requires scripts/get-deps.sh to have been run.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CHECK=0
while [ $# -gt 0 ]; do
  case "$1" in
    --check) CHECK=1; shift ;;
    -h|--help) sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unrecognized option $1" >&2; exit 2 ;;
  esac
done

ENV_FILE="${repo_root}/deps/env.sh"
[ -f "${ENV_FILE}" ] || { echo "error: run scripts/get-deps.sh first" >&2; exit 1; }
# shellcheck source=/dev/null
. "${ENV_FILE}"
pinned="$("${repo_root}/scripts/logos-rev.sh")"
if [ "${KAIROS_LOGOS_REV}" != "${pinned}" ]; then
  echo "error: deps/ was built for Logos ${KAIROS_LOGOS_REV}, but" >&2
  echo "lake-manifest.json pins ${pinned}. Rerun scripts/get-deps.sh." >&2
  exit 1
fi

L="${KAIROS_LOGOS_DIR}"
OUT="${repo_root}/build/kairos-out"
GEN_REL="kairos/Kairos/Gen"
DRIVER="${KAIROS_ETHOS_DIR}/tools/eoc/driver.py"
rm -rf "${OUT}"

# The files install-sig.sh installs as generated (its LEAN_OUTPUTS). Proofs/
# otherwise holds hand-written proofs, whose generated skeletons are not kept.
mapfile -t outputs < <(awk '/^LEAN_OUTPUTS=\(/{f=1;next} f&&/^\)/{exit} f' \
  "${L}/install/install-sig.sh" | sed -n 's/^ *"\(.*\.lean\)" *$/\1/p')
[ "${#outputs[@]}" -gt 0 ] || {
  echo "error: no LEAN_OUTPUTS in Logos's install/install-sig.sh" >&2; exit 1; }
# CpcMini's rules, as install-sig.sh --mini chooses them.
mapfile -t mini_rules < <(sed -n '/MINI}" = "1"/,/^fi/p' "${L}/install/install-sig.sh" \
  | sed -n 's/^ *RULES=(\(.*\))$/\1/p' | tr ' ' '\n' | grep .)
[ "${#mini_rules[@]}" -gt 0 ] || {
  echo "error: no CpcMini rules in Logos's install/install-sig.sh" >&2; exit 1; }

# Run Logos's own Lean pipeline into $1; the remaining arguments say what to
# compile.
run_pipeline() {
  local stage="$1"; shift
  rm -rf "${stage}"
  python3 "${DRIVER}" lean \
    --build-dir "${KAIROS_ETHOS_EOC_BUILD}" --final-out-dir "${stage}" \
    --semantics "${L}/install/defs/Cpc.eos" \
    --smt-semantics "${L}/install/defs/smt.eos" \
    --skip-cvc5 --no-build "$@" >/dev/null
  [ -f "${stage}/lean-cpc-final.eo" ] || {
    echo "error: the driver did not write ${stage}/lean-cpc-final.eo" >&2; exit 1; }
}

# Check that the Lean in $1 is Logos's committed package $2, modulo the
# header and the module name install-sig.sh rewrites.
check_package() {
  local stage="$1" pkg="$2" mismatch=0 n=0 rel f committed
  for rel in "${outputs[@]}"; do
    f="${stage}/lean/${rel}"
    committed="${L}/${pkg}/${rel}"
    [ -f "${committed}" ] || continue   # e.g. CpcMini has no parser
    n=$((n + 1))
    # install-sig.sh prepends a comment header of 7 lines (6 + a blank one).
    if [ ! -f "${f}" ] || ! cmp -s \
        <(sed "s/import \(all \)\{0,1\}Cpc\./import \1${pkg}./g" "${f}") \
        <(tail -n +8 "${committed}"); then
      echo "    differs: ${pkg}/${rel}" >&2
      mismatch=1
    fi
  done
  if [ "${mismatch}" = "1" ]; then
    echo "error: the pinned Logos's ${pkg}/ is not what its own pipeline generates;" >&2
    echo "Kairos would not be compiled from the signature Logos was." >&2
    exit 1
  fi
  echo "    ok: ${pkg}, ${n} files identical"
}

echo "==> [1/3] Logos's pipeline on install/defs/Cpc.cached.eo (Logos ${KAIROS_LOGOS_REV:0:8})"
STAGE="${repo_root}/build/eoc-out"
STAGE_MINI="${repo_root}/build/eoc-out-mini"
run_pipeline "${STAGE}" --all "${L}/install/defs/Cpc.cached.eo"
run_pipeline "${STAGE_MINI}" --no-parser "${L}/install/defs/Cpc.cached.eo" "${mini_rules[@]}"

echo "==> [2/3] Checking the regenerated Lean is Logos's committed packages"
check_package "${STAGE}" Cpc
check_package "${STAGE_MINI}" CpcMini

echo "==> [3/3] kairos-eoc on CpcMini (rules: ${mini_rules[*]})"
ETHOS_PLUGIN_OUTPUT_DIR="${OUT}" "${KAIROS_EOC}" "${STAGE_MINI}/lean-cpc-final.eo" >/dev/null
[ -d "${OUT}/${GEN_REL}" ] || { echo "error: kairos-eoc wrote nothing" >&2; exit 1; }
sed -n 's/^\/-! \(Generated .*\)\. Left out:$/    \1/p' "${OUT}/${GEN_REL}/Programs.lean"

DEST="${repo_root}/Kairos/Gen"
if [ "${CHECK}" = "1" ]; then
  if diff -r "${OUT}/${GEN_REL}" "${DEST}" >/dev/null 2>&1; then
    echo "==> Kairos/Gen/ is up to date"
    exit 0
  fi
  diff -r "${OUT}/${GEN_REL}" "${DEST}" | head -40 >&2 || true
  echo "error: Kairos/Gen/ is not what scripts/generate.sh generates" >&2
  exit 1
fi
rm -rf "${DEST}"
mkdir -p "$(dirname "${DEST}")"
cp -r "${OUT}/${GEN_REL}" "${DEST}"
echo "==> Installed Kairos/Gen/"
