#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/install-cpc.sh [OPTION]...

Regenerate Kairos/Gen/ from the CPC signature of the pinned Logos:

  install/install-cpc.sh            # regenerate Kairos/Gen/
  install/install-cpc.sh --check    # install nothing; is Kairos/Gen/ up to date?

What it compiles is Logos's own recorded copy of the signature,
install/defs/Cpc.cached.eo of the Logos that lake-manifest.json pins (--cached
is accepted and is the only mode: Kairos is compiled from exactly what Logos
was). The run:

  1. runs Logos's Lean pipeline (Ethos's tools/eoc/driver.py, with Logos's
     semantics) on that signature, for Cpc and for CpcMini, which yields
     lean-cpc-final.eo, the exact input of the lean-meta stage;
  2. checks that the Lean it yields is Logos's committed Cpc/ and CpcMini/,
     modulo the header and module name install-sig.sh adds, so the final
     signature Kairos compiles is the one Logos's checker was compiled from;
  3. runs kairos-eoc on Cpc's final signature and installs Kairos/Gen/.

Options:
  --check          write nothing; exit 1 if Kairos/Gen/ is not what is generated
  --cached         compile Logos's cached signature (the default)
  --deps-dir DIR   where install/get-eo-compiler.sh put things (default: <install>/deps)
  -h, --help       show this message

Run install/get-eo-compiler.sh first. Exits 0 when it did what it was asked
(under --check: when Kairos/Gen/ is up to date) and 1 otherwise.
USAGE
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
DEPS_DIR="${script_dir}/deps"
CHECK=0
while [ $# -gt 0 ]; do
  case "$1" in
    --check) CHECK=1; shift ;;
    --cached) shift ;;
    --deps-dir) DEPS_DIR="${2:?--deps-dir requires a value}"; shift 2 ;;
    --deps-dir=*) DEPS_DIR="${1#*=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unrecognized option $1" >&2; usage >&2; exit 2 ;;
  esac
done

ENV_FILE="${DEPS_DIR}/eoc-env.sh"
[ -f "${ENV_FILE}" ] || { echo "error: run install/get-eo-compiler.sh first" >&2; exit 1; }
# shellcheck source=/dev/null
. "${ENV_FILE}"
pinned="$("${repo_root}/scripts/logos-rev.sh")"
if [ "${KAIROS_LOGOS_REV}" != "${pinned}" ]; then
  echo "error: ${DEPS_DIR} holds Logos ${KAIROS_LOGOS_REV}, but lake-manifest.json" >&2
  echo "pins ${pinned}. Rerun install/get-eo-compiler.sh." >&2
  exit 1
fi

L="${KAIROS_LOGOS_DIR}"
OUT="${DEPS_DIR}/kairos-out"
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
STAGE="${DEPS_DIR}/eoc-out"
STAGE_MINI="${DEPS_DIR}/eoc-out-mini"
run_pipeline "${STAGE}" --all "${L}/install/defs/Cpc.cached.eo"
run_pipeline "${STAGE_MINI}" --no-parser "${L}/install/defs/Cpc.cached.eo" "${mini_rules[@]}"

echo "==> [2/3] Checking the regenerated Lean is Logos's committed packages"
check_package "${STAGE}" Cpc
check_package "${STAGE_MINI}" CpcMini

echo "==> [3/3] kairos-eoc on Cpc"
KAIROS_CALC=Cpc ETHOS_PLUGIN_OUTPUT_DIR="${OUT}" "${KAIROS_EOC}" "${STAGE}/lean-cpc-final.eo" >/dev/null
[ -d "${OUT}/${GEN_REL}" ] || { echo "error: kairos-eoc wrote nothing" >&2; exit 1; }
sed -n 's/^\/-! \(Generated .*\)\. Left out:$/    \1/p' "${OUT}/${GEN_REL}/Programs.lean"

DEST="${repo_root}/Kairos/Gen"
if [ "${CHECK}" = "1" ]; then
  if diff -r "${OUT}/${GEN_REL}" "${DEST}" >/dev/null 2>&1; then
    echo "==> Kairos/Gen/ is up to date"
    exit 0
  fi
  diff -r "${OUT}/${GEN_REL}" "${DEST}" | head -40 >&2 || true
  echo "error: Kairos/Gen/ is not what install/install-cpc.sh generates" >&2
  exit 1
fi
rm -rf "${DEST}"
mkdir -p "$(dirname "${DEST}")"
cp -r "${OUT}/${GEN_REL}" "${DEST}"
echo "==> Installed Kairos/Gen/"
