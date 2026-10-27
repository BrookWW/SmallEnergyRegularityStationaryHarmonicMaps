#!/usr/bin/env python3
"""Check the exact public mathematical footprint and pinned dependencies."""

from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

from verification_common import NAMESPACES, PROJECT, lean_sources, strip_comments_and_strings


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_header(source):
    """A module must precede doc commands, after ordinary comments only."""
    index = 0
    while index < len(source):
        if source[index].isspace() or source[index] == "\ufeff":
            index += 1
        elif source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end < 0 else end + 1
        elif source.startswith("/-", index) and not source.startswith(("/--", "/-!"), index):
            index += 2
            depth = 1
            while index < len(source) and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                return False
        else:
            return re.match(r"module(?![\w'.!?])", source[index:]) is not None
    return False


def check_records(records, label):
    if not isinstance(records, dict) or not records:
        raise ValueError(f"Missing {label} fingerprints")
    for name, expected in records.items():
        path = PROJECT / name
        if Path(name).is_absolute() or ".." in Path(name).parts:
            raise ValueError(f"Invalid source path: {name}")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"Invalid fingerprint: {name}")
        if path.is_symlink() or not path.resolve().is_relative_to(PROJECT) or not path.is_file() or digest(path) != expected:
            raise ValueError(f"{label} fingerprint changed: {name}")


def check_dependencies():
    if (PROJECT / ".lake/package-overrides.json").exists():
        raise ValueError("Undeclared package override")
    lake = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
    configuration = (PROJECT / "lakefile.toml").read_text(encoding="utf-8")
    direct = re.findall(r"\[\[require\]\]([^\[]*)", configuration)
    expected_direct = {
        "name": "mathlib", "git": "https://github.com/leanprover-community/mathlib4",
        "rev": "905b95818eb32af7874a58b427f50c1711a5e96c",
    }
    if len(direct) != 1 or dict(re.findall(r'^\s*(\w+)\s*=\s*"([^"]+)"\s*$', direct[0], re.M)) != expected_direct:
        raise ValueError("Mathlib must be the sole pinned direct dependency")
    packages = lake.get("packages", [])
    if not packages or lake.get("packagesDir") != ".lake/packages":
        raise ValueError("Invalid Lake package manifest")
    for dependency in packages:
        if dependency["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", dependency["rev"]):
            raise ValueError("Unpinned dependency: " + dependency["name"])
        package = PROJECT / ".lake/packages" / dependency["name"]
        if package.is_symlink() or not package.is_dir():
            raise ValueError("Missing or symlinked dependency: " + dependency["name"])
        actual = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output([
            "git", "-C", str(package), "status", "--porcelain", "--untracked-files=no"
        ], text=True).strip()
        if actual != dependency["rev"] or dirty:
            raise ValueError("Dependency source drift: " + dependency["name"])
    environment = os.environ.copy()
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN"):
        environment.pop(name, None)
    search_path = subprocess.check_output(
        ["lake", "--no-build", "env", "printenv", "LEAN_PATH"], cwd=PROJECT,
        env=environment, text=True,
    ).strip()
    if not search_path:
        raise ValueError("Empty Lean import search path")
    lean_prefix = Path(subprocess.check_output(
        ["lake", "--no-build", "env", "lean", "--print-prefix"], cwd=PROJECT,
        env=environment, text=True,
    ).strip()).resolve()
    version = subprocess.check_output(
        ["lake", "--no-build", "env", "lean", "--version"], cwd=PROJECT,
        env=environment, text=True,
    ).strip()
    if not re.search(r"\bversion 4\.32\.2(?:\s|,)", version):
        raise ValueError("Actual Lean executable does not match the pinned toolchain")
    for item in search_path.split(os.pathsep):
        path = Path(item)
        path = (PROJECT / path).resolve() if not path.is_absolute() else path.resolve()
        if not path.is_relative_to(PROJECT) and path != lean_prefix / "lib/lean":
            raise ValueError("Non-project Lean search path: " + str(path))


def main():
    manifest = json.loads((PROJECT / "verification/sources.json").read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise ValueError("Unsupported source manifest schema")
    paths = lean_sources()
    actual = {path.relative_to(PROJECT).as_posix() for path in paths}
    if actual != set(manifest.get("lean_source_files", {})):
        raise ValueError("Mathematical source inventory differs from verification/sources.json")
    all_lean = {path.relative_to(PROJECT).as_posix() for path in PROJECT.rglob("*.lean")
                if not set(path.relative_to(PROJECT).parts) & {".lake", ".git"}}
    if all_lean != actual:
        raise ValueError("Unregistered Lean source outside the three declared libraries")
    check_records(manifest["lean_source_files"], "Mathematical source")
    check_records(manifest["build_configuration"], "Build configuration")
    check_records(manifest["verification_tools"], "Verification tool")
    check_records(manifest["theorem_metadata"], "Theorem metadata")
    for path in paths:
        source = path.read_text(encoding="utf-8")
        relative = path.relative_to(PROJECT).as_posix()
        if path.is_symlink() or not module_header(source):
            raise ValueError("Invalid module header or source symlink: " + relative)
        if len(source.splitlines()) > 10_000:
            raise ValueError("Oversized Lean module: " + relative)
        if re.search(r"(?:/Users/|/home/|/private/|/tmp/|(?:blueprint|review|registry)/)", source):
            raise ValueError("Private reference in mathematical source: " + relative)
        code = strip_comments_and_strings(source)
        for imported in re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", code, re.M):
            if not imported.startswith(tuple(name + "." for name in NAMESPACES) + ("Mathlib.",)) and imported not in NAMESPACES + ("Mathlib",):
                raise ValueError(f"Unexpected mathematical import {imported} in {relative}")
    check_dependencies()
    print(f"SOURCE FOOTPRINT PASS: {len(paths)} regular Lean modules")
    print("SOURCE, BUILD-CONFIGURATION AND VERIFICATION-TOOL FINGERPRINTS PASS")
    print("PINNED DEPENDENCIES AND ISOLATED IMPORT SEARCH PATH PASS")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
