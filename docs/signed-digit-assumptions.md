# Signed-Digit Assumption Ledger

Canonical machine-readable source:
- `docs/signed-digit-assumptions.json`

Validation script (CI-ready):
- `scripts/check_signeddigit_assumptions.py`

This ledger tracks:
- every `postulate` declaration under `src/Reals/SignedDigit/`
- dependency class (`semantic-arithmetic` or `ac-omega`)
- module-level `--allow-unsolved-metas` usage

The checker prints the discovered postulate inventory and fails on:
- undocumented postulates
- stale ledger entries
- unsolved-metas module mismatch
