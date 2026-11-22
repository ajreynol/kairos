#!/usr/bin/env bash
# Show what changed upstream, in the files listed in eoc/FORK_BASE, between
# the Ethos commit we forked them at and the Ethos commit the current Logos
# pin uses (install/deps/eoc/ethos). Run after bumping the Logos pin.
#
# Usage: scripts/fork-drift.sh
# Exit status: 0 if nothing changed upstream, 1 if something did.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=/dev/null
. "${repo_root}/install/deps/eoc-env.sh"

base="$(sed -n 's/^ETHOS_COMMIT=//p' "${repo_root}/eoc/FORK_BASE")"
files=()
while read -r path _; do files+=("${path}"); done \
  < <(grep -v '^#' "${repo_root}/eoc/FORK_BASE" | grep -v '^ETHOS_COMMIT=' | grep .)

if [ "${base}" = "${KAIROS_ETHOS_VERSION}" ]; then
  # Same commit: just confirm the files still hash as recorded.
  status=0
  while read -r path sum; do
    actual="$(sha256sum "${KAIROS_ETHOS_DIR}/${path}" | cut -d' ' -f1)"
    if [ "${actual}" != "${sum}" ]; then
      echo "hash mismatch: ${path}" >&2; status=1
    fi
  done < <(grep -v '^#' "${repo_root}/eoc/FORK_BASE" | grep -v '^ETHOS_COMMIT=' | grep .)
  [ "${status}" = "0" ] && echo "Fork base is the pinned Ethos commit; no drift."
  exit "${status}"
fi

old="$(mktemp -d)"
trap 'rm -rf "${old}"' EXIT
echo "==> Fetching Ethos ${base} (fork base)"
curl -Lfs "https://github.com/cvc5/ethos/archive/${base}.tar.gz" \
  | tar --strip-components 1 -xz -C "${old}"
status=0
for path in "${files[@]}"; do
  diff -u --label "a/${path} (${base:0:8})" --label "b/${path} (${KAIROS_ETHOS_VERSION:0:8})" \
    "${old}/${path}" "${KAIROS_ETHOS_DIR}/${path}" || status=1
done
exit "${status}"
