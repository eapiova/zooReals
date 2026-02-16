#!/usr/bin/env bash
set -euo pipefail

scripts/check_signeddigit_assumptions.py
scripts/check_signeddigit_references.py
scripts/check_signeddigit_papers.sh
