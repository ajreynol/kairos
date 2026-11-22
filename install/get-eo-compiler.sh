#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/get-eo-compiler.sh [OPTION]...

Download and build what install/install-cpc.sh runs, all of it derived from
one pin, the Logos revision in lake-manifest.json (package Cpc):

  1. Logos at that revision, into install/deps/logos. It holds the signature
     Kairos is compiled from (install/defs/Cpc.cached.eo) and the Ethos commit
     its Lean was compiled with (ETHOS_VERSION in its get-eo-compiler.sh).
  2. Ethos at that commit, with ethos-eoc built, by running Logos's own
     install/get-eo-compiler.sh, into install/deps/eoc. So the compiler is
     exactly the one Logos's Lean comes from.
  3. kairos-eoc, the Kairos stage in eoc/, built against that Ethos tree,
     into install/deps/kairos-eoc.

The paths are recorded in install/deps/eoc-env.sh, which install-cpc.sh reads.

Options:
  --deps-dir DIR   where to put everything (default: <install>/deps)
  --jobs N         parallel compile jobs (default: all processors)
  --skip-ethos     reuse the Logos and Ethos already in DIR; rebuild kairos-eoc only
  --werror         warnings in Kairos's own C++ are errors (as in CI)
  -h, --help       show this message

Requires cmake >= 3.12, a C++17 compiler, the GMP development headers,
python3, tar, and wget or curl.
USAGE
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
DEPS_DIR="${script_dir}/deps"
JOBS="$(nproc 2>/dev/null || echo 4)"
SKIP_ETHOS=0
WERROR=OFF
while [ $# -gt 0 ]; do
  case "$1" in
    --deps-dir) DEPS_DIR="${2:?--deps-dir requires a value}"; shift 2 ;;
    --deps-dir=*) DEPS_DIR="${1#*=}"; shift ;;
    --jobs) JOBS="${2:?--jobs requires a value}"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    --skip-ethos) SKIP_ETHOS=1; shift ;;
    --werror) WERROR=ON; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unrecognized option $1" >&2; usage >&2; exit 2 ;;
  esac
done
mkdir -p "${DEPS_DIR}"
DEPS_DIR="$(cd "${DEPS_DIR}" && pwd)"

download() {
  if command -v wget >/dev/null 2>&1; then
    wget -q -O "$2" "$1"
  elif command -v curl >/dev/null 2>&1; then
    curl -Lfs "$1" -o "$2"
  else
    echo "Neither wget nor curl is installed; cannot download $1." >&2
    exit 1
  fi
}

LOGOS_REV="$(python3 -I - "${repo_root}/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
revs = [p["rev"] for p in m["packages"] if p["name"] == "Cpc"]
if len(revs) != 1:
    sys.exit("lake-manifest.json must pin exactly one package named Cpc")
print(revs[0])
PY
)"
LOGOS_URL="$(python3 -I - "${repo_root}/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
print([p["url"] for p in m["packages"] if p["name"] == "Cpc"][0].removesuffix(".git"))
PY
)"
LOGOS_DIR="${DEPS_DIR}/logos"
EOC_DEPS="${DEPS_DIR}/eoc"

if [ "${SKIP_ETHOS}" = "0" ]; then
  echo "==> Downloading Logos ${LOGOS_REV}"
  rm -rf "${LOGOS_DIR}"
  mkdir -p "${LOGOS_DIR}"
  download "${LOGOS_URL}/archive/${LOGOS_REV}.tar.gz" "${DEPS_DIR}/logos.tgz"
  tar --strip-components 1 -xzf "${DEPS_DIR}/logos.tgz" -C "${LOGOS_DIR}"
  rm -f "${DEPS_DIR}/logos.tgz"
  echo "${LOGOS_REV}" > "${LOGOS_DIR}/.kairos-rev"
fi
[ -f "${LOGOS_DIR}/.kairos-rev" ] && [ "$(cat "${LOGOS_DIR}/.kairos-rev")" = "${LOGOS_REV}" ] || {
  echo "error: ${LOGOS_DIR} is not Logos ${LOGOS_REV}; rerun without --skip-ethos." >&2
  exit 1
}

ETHOS_VERSION="$(sed -n 's/^ETHOS_VERSION="\([0-9a-f]\{40\}\)"$/\1/p' \
  "${LOGOS_DIR}/install/get-eo-compiler.sh")"
[ -n "${ETHOS_VERSION}" ] || {
  echo "error: no ETHOS_VERSION in Logos's install/get-eo-compiler.sh" >&2; exit 1; }
echo "==> Ethos ${ETHOS_VERSION} (pinned by Logos)"

if [ "${SKIP_ETHOS}" = "0" ]; then
  # Logos's own script, so that how ethos-eoc is built cannot drift from it.
  bash "${LOGOS_DIR}/install/get-eo-compiler.sh" --deps-dir "${EOC_DEPS}" --jobs "${JOBS}"
fi
# shellcheck source=/dev/null
. "${EOC_DEPS}/eoc-env.sh"
if [ "${EOC_ETHOS_VERSION}" != "${ETHOS_VERSION}" ]; then
  echo "error: ${EOC_DEPS} holds Ethos ${EOC_ETHOS_VERSION}, Logos pins ${ETHOS_VERSION}." >&2
  echo "Rerun without --skip-ethos." >&2
  exit 1
fi

echo "==> Building kairos-eoc against ${EOC_ETHOS_DIR}"
KAIROS_BUILD="${DEPS_DIR}/kairos-eoc"
cmake -S "${repo_root}/eoc" -B "${KAIROS_BUILD}" -DCMAKE_BUILD_TYPE=Release \
  -DETHOS_SOURCE_DIR="${EOC_ETHOS_DIR}" -DKAIROS_WERROR="${WERROR}" >/dev/null
cmake --build "${KAIROS_BUILD}" --parallel "${JOBS}" --target kairos-eoc
KAIROS_EOC="${KAIROS_BUILD}/kairos-eoc"
[ -x "${KAIROS_EOC}" ] || { echo "error: ${KAIROS_EOC} was not built" >&2; exit 1; }

cat > "${DEPS_DIR}/eoc-env.sh" <<ENV
# Written by install/get-eo-compiler.sh; read by install/install-cpc.sh. Edit by
# re-running get-eo-compiler.sh rather than by hand.
KAIROS_LOGOS_REV="${LOGOS_REV}"
KAIROS_LOGOS_DIR="${LOGOS_DIR}"
KAIROS_ETHOS_VERSION="${ETHOS_VERSION}"
KAIROS_ETHOS_DIR="${EOC_ETHOS_DIR}"
KAIROS_ETHOS_EOC_BUILD="${EOC_BUILD_DIR}"
KAIROS_EOC="${KAIROS_EOC}"
ENV

cat <<DONE

==> Done.

  logos       ${LOGOS_DIR} (${LOGOS_REV})
  ethos       ${EOC_ETHOS_DIR} (${ETHOS_VERSION})
  kairos-eoc  ${KAIROS_EOC}

Regenerate Kairos/Gen with install/install-cpc.sh.
DONE
