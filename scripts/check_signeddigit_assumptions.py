#!/usr/bin/env python3
"""Validate SignedDigit postulate inventory against the canonical ledger.

This script is intended for CI:
- prints discovered postulates grouped by module
- fails on undocumented postulates
- fails on stale ledger entries
- checks allow-unsolved-metas modules against ledger
"""

from __future__ import annotations

import json
import re
import sys
from collections import defaultdict
from pathlib import Path

LEDGER_PATH = Path("docs/signed-digit-assumptions.json")

POSTULATE_RE = re.compile(r"^(\s*)postulate\b")
# Captures lines like "  name : ..." while ignoring continuation lines "  (x : ..."
DECL_RE = re.compile(r"^\s*([^\s(:][^:\s]*)\s*:")
UNSOLVED_RE = re.compile(r"allow-unsolved-metas")


def module_from_file(path: Path) -> str:
    rel = path.relative_to("src").with_suffix("")
    return ".".join(rel.parts)


def parse_postulates(path: Path) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    found: list[str] = []
    i = 0
    while i < len(lines):
        m = POSTULATE_RE.match(lines[i])
        if not m:
            i += 1
            continue

        pindent = len(lines[i]) - len(lines[i].lstrip(" "))
        i += 1

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()
            if stripped == "" or stripped.startswith("--"):
                i += 1
                continue

            indent = len(line) - len(line.lstrip(" "))
            if indent <= pindent:
                break

            m_decl = DECL_RE.match(line)
            if m_decl:
                found.append(m_decl.group(1).strip())

            i += 1

    return found


def main() -> int:
    if not LEDGER_PATH.exists():
        print(f"ERROR: missing ledger file: {LEDGER_PATH}", file=sys.stderr)
        return 2

    ledger = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
    source_root = Path(ledger["source_root"])

    allowed_classes = set(ledger["dependency_classes"].keys())

    ledger_entries = ledger["postulates"]
    ledger_set: set[tuple[str, str]] = set()
    class_by_entry: dict[tuple[str, str], str] = {}

    for entry in ledger_entries:
        key = (entry["module"], entry["name"])
        if key in ledger_set:
            print(f"ERROR: duplicate ledger entry: {key[0]}.{key[1]}", file=sys.stderr)
            return 2
        cls = entry["class"]
        if cls not in allowed_classes:
            print(f"ERROR: invalid class '{cls}' for {key[0]}.{key[1]}", file=sys.stderr)
            return 2
        ledger_set.add(key)
        class_by_entry[key] = cls

    discovered_set: set[tuple[str, str]] = set()
    discovered_by_module: dict[str, list[str]] = defaultdict(list)

    for agda_file in sorted(source_root.rglob("*.agda")):
        module = module_from_file(agda_file)
        names = parse_postulates(agda_file)
        for name in names:
            key = (module, name)
            discovered_set.add(key)
            discovered_by_module[module].append(name)

    print("SignedDigit postulate inventory")
    print("============================")
    for module in sorted(discovered_by_module):
        print(f"{module}")
        for name in sorted(discovered_by_module[module]):
            cls = class_by_entry.get((module, name), "UNDOCUMENTED")
            print(f"  - {name} [{cls}]")

    undocumented = sorted(discovered_set - ledger_set)
    stale = sorted(ledger_set - discovered_set)

    # Check allow-unsolved-metas modules
    discovered_unsolved: set[str] = set()
    for agda_file in sorted(source_root.rglob("*.agda")):
        head = "\n".join(agda_file.read_text(encoding="utf-8").splitlines()[:5])
        if UNSOLVED_RE.search(head):
            discovered_unsolved.add(module_from_file(agda_file))

    ledger_unsolved = {entry["module"] for entry in ledger.get("allow_unsolved_metas", [])}

    if undocumented:
        print("\nERROR: undocumented postulates detected:")
        for module, name in undocumented:
            print(f"  - {module}.{name}")

    if stale:
        print("\nERROR: stale ledger entries (no longer present in source):")
        for module, name in stale:
            print(f"  - {module}.{name}")

    if discovered_unsolved != ledger_unsolved:
        print("\nERROR: allow-unsolved-metas module set mismatch")
        print("  discovered:")
        for module in sorted(discovered_unsolved):
            print(f"    - {module}")
        print("  ledger:")
        for module in sorted(ledger_unsolved):
            print(f"    - {module}")
        return 1

    if undocumented or stale:
        return 1

    print("\nOK: ledger is complete and consistent.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
