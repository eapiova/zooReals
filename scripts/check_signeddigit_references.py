#!/usr/bin/env python3
"""Validate SignedDigit bibliography audit mapping.

Checks:
- every audited key exists in references.bib
- each entry has local_pdf or external_url
- local_pdf paths exist
- optional title_hint appears on first PDF page (when pdftotext is available)
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

MANIFEST = Path("docs/signed-digit-reference-audit.json")
BIB = Path("references.bib")

KEY_RE = re.compile(r"@\w+\{\s*([^,]+),")


def read_bib_keys(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    return set(KEY_RE.findall(text))


def first_page_text(pdf: Path) -> str:
    proc = subprocess.run(
        ["pdftotext", "-f", "1", "-l", "1", str(pdf), "-"],
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "pdftotext failed")
    return proc.stdout


def normalize_for_match(text: str) -> str:
    # Robust against line breaks, punctuation, ligatures, and case.
    return re.sub(r"[^a-z0-9]+", "", text.lower())


def main() -> int:
    if not MANIFEST.exists():
        print(f"ERROR: missing manifest: {MANIFEST}", file=sys.stderr)
        return 2
    if not BIB.exists():
        print(f"ERROR: missing bibliography: {BIB}", file=sys.stderr)
        return 2

    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    entries = data.get("entries", [])
    bib_keys = read_bib_keys(BIB)

    pdftotext_available = shutil.which("pdftotext") is not None
    if not pdftotext_available:
        print("WARN: pdftotext not found; title_hint checks will be skipped.")

    failed = False

    for entry in entries:
        key = entry["key"]
        local_pdf = entry.get("local_pdf")
        external_url = entry.get("external_url")
        title_hint = entry.get("title_hint")

        print(f"[{key}]", end=" ")

        if key not in bib_keys:
            print("FAIL (missing bib key)")
            failed = True
            continue

        if not local_pdf and not external_url:
            print("FAIL (missing local_pdf/external_url)")
            failed = True
            continue

        if local_pdf:
            pdf_path = Path(local_pdf)
            if not pdf_path.exists():
                print(f"FAIL (missing file: {local_pdf})")
                failed = True
                continue

            if title_hint and pdftotext_available:
                try:
                    text = first_page_text(pdf_path).lower()
                except Exception as exc:  # noqa: BLE001
                    print(f"FAIL (cannot inspect PDF title: {exc})")
                    failed = True
                    continue

                if normalize_for_match(title_hint) not in normalize_for_match(text):
                    print("FAIL (title_hint not found on first page)")
                    failed = True
                    continue

            print(f"OK (local: {local_pdf})")
        else:
            print(f"OK (external: {external_url})")

    if failed:
        return 1

    print("All signed-digit bibliography mappings are valid.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
