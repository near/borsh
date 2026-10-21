#!/usr/bin/env bash
# Render BorshSpec/Spec.lean as one self-contained HTML page: ../out/spec.html
# Needs elan (Lean is fetched by the toolchain files) and python3 (standard library only).
set -euo pipefail
cd "$(dirname "$0")"
site="$(lake query :literateHtml)"
python3 -I single-file.py "$site" ../out/spec.html
