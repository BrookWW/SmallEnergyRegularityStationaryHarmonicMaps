#!/usr/bin/env python3
"""Recompute the exact rational example from the public constant functions."""

import json
import sys

from verification_common import PROJECT, lean_output


def main():
    path = PROJECT / "verification/effective-constants.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1 or data.get("module") != \
            "StationaryHarmonicMaps.Analysis.EffectiveStationaryConstants":
        raise ValueError("Unsupported effective-constant example schema")
    cases = data.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("Missing effective-constant examples")
    for case in cases:
        n, q, bound = case["n"], case["q"], case["geometric_bound"]
        if type(n) is not int or n < 2 or type(q) is not int or q < 0 or bound != "1":
            raise ValueError("Unexpected dimensional or geometric example input")
        code = r'''
module
public meta import StationaryHarmonicMaps.Analysis.EffectiveStationaryConstants
meta import Lean
open StationaryHarmonicMaps.Analysis
#eval do
  let e := effectiveStationaryEnergyThreshold NINPUT QINPUT 1
  let c := effectiveStationaryHolderConstant NINPUT QINPUT 1
  let data := Lean.Json.mkObj [
    ("n", Lean.toJson (NINPUT : Nat)), ("q", Lean.toJson (QINPUT : Nat)),
    ("geometric_bound", Lean.toJson ("1" : String)),
    ("epsilon_num", Lean.toJson (toString e.num)),
    ("epsilon_den", Lean.toJson (toString e.den)),
    ("holder_num", Lean.toJson (toString c.num)),
    ("holder_den", Lean.toJson (toString c.den)),
    ("epsilon_positive", Lean.toJson (decide (0 < e))),
    ("holder_positive", Lean.toJson (decide (0 < c)))]
  IO.println ("NUMERICJSON " ++ data.compress)
'''.replace("NINPUT", str(n)).replace("QINPUT", str(q))
        output = lean_output(code)
        records = [line.removeprefix("NUMERICJSON ")
                   for line in output.splitlines() if line.startswith("NUMERICJSON ")]
        if len(records) != 1 or json.loads(records[0]) != case:
            raise ValueError("Exact rational constant computation differs from the example")
        if not case["epsilon_positive"] or not case["holder_positive"]:
            raise ValueError("The computed constants must be positive")
        print(f"EFFECTIVE CONSTANT MATCH: n={n}, q={q}, geometric bound={bound}")
        print(f"  epsilon numerator/denominator decimal digits: "
              f"{len(case['epsilon_num'])}/{len(case['epsilon_den'])}")
        print(f"  Holder numerator/denominator decimal digits: "
              f"{len(case['holder_num'])}/{len(case['holder_den'])}")
    print(f"EFFECTIVE CONSTANT COMPUTATION PASS: {len(cases)} exact rational examples")


if __name__ == "__main__":
    try:
        main()
    except (KeyError, OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
