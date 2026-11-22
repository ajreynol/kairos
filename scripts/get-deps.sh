#!/usr/bin/env bash
# Fetch and build everything Kairos's code generation needs, all derived from
# one pin: the Logos revision in lake-manifest.json.
#
#   1. Logos at that revision (Lake's checkout, .lake/packages/Cpc).
#   2. Ethos at the commit that Logos pins (ETHOS_VERSION in Logos's
#      install/get-eo-compiler.sh), with ethos-eoc built, by running that very
#      script. So the compiler is exactly the one Logos's Lean comes from.
#   3. kairos-eoc, the Kairos stage in eoc/, built against that Ethos tree.
#
# The paths are recorded in deps/env.sh, which scripts/generate.sh reads.
#
# Usage: scripts/get-deps.sh [--jobs N] [--skip-ethos] [--werror]
#   --skip-ethos  reuse deps/eoc (only rebuild kairos-eoc)
#   --werror      warnings in Kairos's own C++ are errors (as in CI)

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JOBS="$(nproc 2>/dev/null || echo 4)"
SKIP_ETHOS=0
WERROR=OFF
while [ $# -gt 0 ]; do
  case "$1" in
    --jobs) JOBS="${2:?--jobs requires a value}"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    --skip-ethos) SKIP_ETHOS=1; shift ;;
    --werror) WERROR=ON; shift ;;
    -h|--help) sed -n '2,17p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unrecognized option $1" >&2; exit 2 ;;
  esac
done

LOGOS_REV="$("${repo_root}/scripts/logos-rev.sh")"
LOGOS_DIR="${repo_root}/.lake/packages/Cpc"
DEPS_DIR="${repo_root}/deps"
EOC_DEPS="${DEPS_DIR}/eoc"
KAIROS_BUILD="${repo_root}/build/eoc"

echo "==> Logos ${LOGOS_REV}"
if [ ! -d "${LOGOS_DIR}/.git" ]; then
  (cd "${repo_root}" && lake update Cpc)
fi
actual="$(git -C "${LOGOS_DIR}" rev-parse HEAD)"
if [ "${actual}" != "${LOGOS_REV}" ]; then
  echo "error: ${LOGOS_DIR} is at ${actual}, but lake-manifest.json pins" >&2
  echo "${LOGOS_REV}. Run 'lake update Cpc' (or fix the manifest)." >&2
  exit 1
fi
if [ -n "$(git -C "${LOGOS_DIR}" status --porcelain --untracked-files=no)" ]; then
  echo "error: ${LOGOS_DIR} has local modifications; Kairos must be generated" >&2
  echo "from the pinned Logos exactly." >&2
  exit 1
fi

ETHOS_VERSION="$(sed -n 's/^ETHOS_VERSION="\([0-9a-f]\{40\}\)"$/\1/p' \
  "${LOGOS_DIR}/install/get-eo-compiler.sh")"
[ -n "${ETHOS_VERSION}" ] || {
  echo "error: no ETHOS_VERSION in Logos's install/get-eo-compiler.sh" >&2; exit 1; }
echo "==> Ethos ${ETHOS_VERSION} (pinned by Logos)"

if [ "${SKIP_ETHOS}" = "0" ]; then
  # Logos's own script, so that how ethos-eoc is built cannot drift from it.
  bash "${LOGOS_DIR}/install/get-eo-compiler.sh" \
    --deps-dir "${EOC_DEPS}" --jobs "${JOBS}"
fi
# shellcheck source=/dev/null
. "${EOC_DEPS}/eoc-env.sh"
if [ "${EOC_ETHOS_VERSION}" != "${ETHOS_VERSION}" ]; then
  echo "error: deps/eoc holds Ethos ${EOC_ETHOS_VERSION}, Logos pins" >&2
  echo "${ETHOS_VERSION}. Rerun without --skip-ethos." >&2
  exit 1
fi

echo "==> Building kairos-eoc against ${EOC_ETHOS_DIR}"
cmake -S "${repo_root}/eoc" -B "${KAIROS_BUILD}" \
  -DCMAKE_BUILD_TYPE=Release -DETHOS_SOURCE_DIR="${EOC_ETHOS_DIR}" \
  -DKAIROS_WERROR="${WERROR}" >/dev/null
cmake --build "${KAIROS_BUILD}" --parallel "${JOBS}" --target kairos-eoc
KAIROS_EOC="${KAIROS_BUILD}/kairos-eoc"
[ -x "${KAIROS_EOC}" ] || { echo "error: ${KAIROS_EOC} was not built" >&2; exit 1; }

cat > "${DEPS_DIR}/env.sh" <<ENV
# Written by scripts/get-deps.sh; read by scripts/generate.sh. Do not edit.
KAIROS_LOGOS_REV="${LOGOS_REV}"
KAIROS_LOGOS_DIR="${LOGOS_DIR}"
KAIROS_ETHOS_VERSION="${ETHOS_VERSION}"
KAIROS_ETHOS_DIR="${EOC_ETHOS_DIR}"
KAIROS_ETHOS_EOC_BUILD="${EOC_BUILD_DIR}"
KAIROS_EOC="${KAIROS_EOC}"
ENV

echo "==> Done. Recorded in deps/env.sh"
