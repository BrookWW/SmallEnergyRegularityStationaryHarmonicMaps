#!/usr/bin/env python3
"""Scan all project mathematics and inspect every recorded theorem's axioms.

Only propext, Classical.choice and Quot.sound are permitted. The lexical scan
masks comments and strings and covers all three source libraries. The Lean
probe reads existing compiled artifacts and never rebuilds dependencies.
"""

import json
import re
import sys

from verification_common import (
    PROJECT, check_frozen_coverage, lean_output, lean_sources, load_theorems,
    parse_records, strip_comments_and_strings,
)


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = {
    "sorry", "admit", "axiom", "sorryAx", "unsafe", "native_decide",
    "implemented_by", "extern", "ofReduceBool", "ofReduceNat", "trustCompiler",
    "skipKernelTC", "maxHeartbeats", "maxRecDepth", "maxSynthPendingDepth",
}


def scan_sources():
    paths = lean_sources()
    if len(paths) < 3:
        raise ValueError("Mathematical Lean sources are missing.")
    violations = []
    for path in paths:
        source = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", source):
            if match.group() in FORBIDDEN_TOKENS:
                line = source.count("\n", 0, match.start()) + 1
                violations.append(f"{path.relative_to(PROJECT)}:{line}: {match.group()}")
        if re.search(r"\bset_option\s+(?:debug\.|compiler\.|Elab\.async|tactic\.compiler)", source):
            violations.append(f"{path.relative_to(PROJECT)}: unapproved verification option")
    if violations:
        raise ValueError("Forbidden proof-gap, resource-override or trust-bypass token(s):\n" + "\n".join(violations))
    print(f"PROOF-GAP AND TRUST CHECK PASS: {len(paths)} Lean files")


def main():
    records = load_theorems()
    check_frozen_coverage(records)
    scan_sources()
    modules = sorted({record["module"] for record in records})
    names = sorted(record["theorem"] for record in records)
    code = "module\n" + "\n".join("public import " + module for module in modules)
    code += "\nmeta import Lean\nopen Lean\n"
    for name in names:
        code += "\nrun_cmd do\n  let env ← getEnv\n  let n := ``" + name + "\n"
        code += '''
  let some _ := env.find? n | throwError "missing theorem: {n}"
  let axioms ← Lean.collectAxioms n
  logInfo ("AXIOMJSON " ++ n.toString ++ " " ++ (toJson (axioms.toList.map Name.toString)).compress)
'''
    actual = parse_records(lean_output(code), "AXIOMJSON", names)
    for name in names:
        axioms = json.loads(actual[name])
        if not isinstance(axioms, list) or not all(isinstance(axiom, str) for axiom in axioms):
            raise ValueError(f"Malformed axiom list for {name}")
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Disallowed axioms for {name}: {', '.join(sorted(unexpected))}")
        print("AXIOMS OK", name, ", ".join(sorted(axioms)) or "none")
    print(f"AXIOM CHECK PASS: {len(names)} complete theorem dependency closures")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
