#!/usr/bin/env bash
# Print the Logos revision pinned in lake-manifest.json (package "Cpc").
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
python3 -I - "${repo_root}/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
revs = [p["rev"] for p in m["packages"] if p["name"] == "Cpc"]
if len(revs) != 1:
    sys.exit("lake-manifest.json must pin exactly one package named Cpc")
print(revs[0])
PY
