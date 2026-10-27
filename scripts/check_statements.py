#!/usr/bin/env python3
"""Compare compiled theorem types with verification/theorem-types.json.

Run after `lake build`. The expression encoding includes binder names and
visibility, constants, universe levels, implicit arguments, and the complete
type expression. Source-position metadata is omitted. Referenced definitions
are not unfolded; this checks the stored elaborated interfaces.
"""

import hashlib
import sys

from verification_common import check_frozen_coverage, lean_output, load_theorems, parse_records


ENCODER = r'''
meta import Lean
open Lean
private meta partial def encodeLevel : Level → Json
  | .zero => toJson ("zero" : String)
  | .succ l => Json.arr #[toJson ("succ" : String), encodeLevel l]
  | .max a b => Json.arr #[toJson ("max" : String), encodeLevel a, encodeLevel b]
  | .imax a b => Json.arr #[toJson ("imax" : String), encodeLevel a, encodeLevel b]
  | .param n => Json.arr #[toJson ("param" : String), toJson n.toString]
  | .mvar n => Json.arr #[toJson ("mvar" : String), toJson n.name.toString]
private meta partial def encodeExpr : Expr → Json
  | .bvar i => Json.arr #[toJson ("bvar" : String), toJson i]
  | .fvar i => Json.arr #[toJson ("fvar" : String), toJson i.name.toString]
  | .mvar i => Json.arr #[toJson ("mvar" : String), toJson i.name.toString]
  | .sort u => Json.arr #[toJson ("sort" : String), encodeLevel u]
  | .const n us => Json.arr #[toJson ("const" : String), toJson n.toString, Json.arr (us.toArray.map encodeLevel)]
  | .app f a => Json.arr #[toJson ("app" : String), encodeExpr f, encodeExpr a]
  | .lam n t b bi => Json.arr #[toJson ("lam" : String), toJson n.toString, toJson (reprStr bi), encodeExpr t, encodeExpr b]
  | .forallE n t b bi => Json.arr #[toJson ("forall" : String), toJson n.toString, toJson (reprStr bi), encodeExpr t, encodeExpr b]
  | .letE n t v b nondep => Json.arr #[toJson ("let" : String), toJson n.toString, encodeExpr t, encodeExpr v, encodeExpr b, toJson nondep]
  | .lit l => Json.arr #[toJson ("lit" : String), toJson (reprStr l)]
  | .mdata _ e => encodeExpr e
  | .proj n i e => Json.arr #[toJson ("proj" : String), toJson n.toString, toJson i, encodeExpr e]
'''


def main():
    records = load_theorems()
    check_frozen_coverage(records)
    modules = sorted({record["module"] for record in records})
    names = [record["theorem"] for record in records]
    code = "module\n" + "\n".join("public import " + module for module in modules)
    code += "\n" + ENCODER
    for name in names:
        code += "\nrun_cmd do\n  let env ← getEnv\n  let n := ``" + name + "\n"
        code += '''
  let some ci := env.find? n | throwError "missing theorem: {n}"
  logInfo ("TYPEJSON " ++ n.toString ++ " " ++ (Json.arr #[toJson (ci.levelParams.map Name.toString), encodeExpr ci.type]).compress)
'''
    actual = parse_records(lean_output(code), "TYPEJSON", names)
    for record in records:
        name = record["theorem"]
        fingerprint = hashlib.sha256(actual[name].encode("utf-8")).hexdigest()
        if fingerprint != record["type_sha256"]:
            raise ValueError(f"Elaborated theorem type changed: {name}")
        print("TYPE MATCH", name, fingerprint)
    print(f"STATEMENT CHECK PASS: {len(records)} theorem types")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
