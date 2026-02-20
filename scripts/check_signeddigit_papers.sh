#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"
RUN_MIDPOINT_AGDA_CHECKS="${RUN_MIDPOINT_AGDA_CHECKS:-0}"

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

midpoint_modules=(
  "src/Reals/SignedDigit/Interval.agda"
  "src/Reals/SignedDigit/Midpoint/Algebra.agda"
  "src/Reals/SignedDigit/Midpoint/Average.agda"
  "src/Reals/SignedDigit/Midpoint/Comparison.agda"
  "src/Reals/SignedDigit/Midpoint/Structure.agda"
  "src/Reals/SignedDigit/Midpoint/RealStructure.agda"
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

if [[ "${RUN_MIDPOINT_AGDA_CHECKS}" == "1" ]]; then
  run_group "Midpoint module set" "${midpoint_modules[@]}"
else
  echo "== Midpoint module set =="
  echo "Skipping (set RUN_MIDPOINT_AGDA_CHECKS=1 to enable)."
fi

echo "All paper module sets typechecked."
