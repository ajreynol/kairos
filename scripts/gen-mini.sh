#!/usr/bin/env bash
# Development helper: rebuild kairos-eoc, regenerate Kairos/Gen/Programs.lean
# from CpcMini's final signature, and check it with Lean.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${repo_root}"
. deps/env.sh
cmake --build build/eoc -j8 2>&1 | grep -E "error" && exit 1
O=build/kairos-out-mini
rm -rf "$O"
ETHOS_PLUGIN_OUTPUT_DIR="$PWD/$O" "$KAIROS_EOC" build/eoc-out-mini/lean-cpc-final.eo >/dev/null
cp "$O/kairos/Kairos/Gen/Programs.lean" Kairos/Gen/Programs.lean
cp "$O/kairos/Kairos/Gen/Dispatch.lean" Kairos/Gen/Dispatch.lean
lake build Kairos
