#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

lake build HindmanSumsProducts.Main Challenge
lake env lean --trust=0 Verification/ChallengeStatement.lean
lake env lean --trust=0 Verification/MainStatement.lean

result_dir=.lake/verification-results
mkdir -p "$result_dir"
axiom_log="$result_dir/axioms.log"
if ! lake env lean --trust=0 Verification/Axioms.lean >"$axiom_log" 2>&1; then
  cat "$axiom_log"
  exit 1
fi
cat "$axiom_log"
python3 scripts/check_axioms.py "$axiom_log"
