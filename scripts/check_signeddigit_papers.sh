#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"

paper_a_modules=(
  "src/Reals/SignedDigit/Safe/Limit/Core.agda"
  "src/Reals/SignedDigit/Safe/Limit.agda"
  "src/Reals/SignedDigit/Meta/AssumeEq.agda"
  "src/Reals/SignedDigit/Meta/ChoiceFromEq.agda"
  "src/Reals/SignedDigit/Meta/LEMBoundary.agda"
  "src/Reals/SignedDigit/PaperA/Entrypoint.agda"
)

paper_b_modules=(
  "src/Reals/SignedDigit/IncDec.agda"
  "src/Reals/SignedDigit/HCIT/Algebra.agda"
  "src/Reals/SignedDigit/HCIT/Structure.agda"
  "src/Reals/SignedDigit/HCIT/Terminality.agda"
  "src/Reals/SignedDigit/PaperB/Entrypoint.agda"
)

run_group() {
  local label="$1"
  shift
  local modules=("$@")

  echo "== ${label} =="
  for mod in "${modules[@]}"; do
    echo "[agda] ${mod}"
    "${AGDA_BIN}" "${mod}"
  done
}

run_group "Paper A module set" "${paper_a_modules[@]}"
run_group "Paper B module set" "${paper_b_modules[@]}"

echo "All paper module sets typechecked."
