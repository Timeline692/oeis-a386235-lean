#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'lake was not found. Install elan and ensure its bin directory is on PATH.' >&2
  exit 127
fi
lake update
lake exe cache get Mathlib.Tactic Mathlib.Data.Int.Interval Mathlib.Analysis.SpecialFunctions.Integrals Mathlib.Analysis.Asymptotics.SpecificAsymptotics
lake env lean A386235.lean
