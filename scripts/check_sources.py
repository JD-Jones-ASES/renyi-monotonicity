#!/usr/bin/env python3
"""Check source policy and pinned package invariants; no mathematical oracle."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
challenge = ROOT / "RenyiMonotonicityChallenge.lean"
files = sorted(ROOT.glob("*.lean")) + sorted((ROOT / "RenyiMonotonicity").rglob("*.lean"))


def require(condition, message):
    if not condition:
        raise SystemExit(message)


for path in files:
    body = path.read_text()
    require(not path.is_symlink(), f"Lean source symlink: {path}")
    require(body.startswith("module\n"), f"Missing module header: {path}")
    require(len(body.splitlines()) <= 10000, f"Oversized source: {path}")
    if path != challenge:
        require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body),
                f"Forbidden implementation token: {path}")
        require("import RenyiMonotonicityChallenge" not in body, f"Challenge leakage: {path}")

require(challenge.stat().st_size <= 100 * 1024, "Oversized Challenge bytes")
require(len(challenge.read_text().splitlines()) <= 1000, "Oversized Challenge lines")
imports = re.findall(r"^public import (\S+)", challenge.read_text(), re.M)
require(bool(imports) and all(x == "Mathlib" or x.startswith("Mathlib.") for x in imports),
        "Challenge imports must stay within Mathlib")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
require(manifest["name"] == "renyiMonotonicity", "Incorrect package name")
for package in manifest["packages"]:
    require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]), f"Unpinned package: {package['name']}")
    require(re.fullmatch(r"https://github.com/[\w.-]+/[\w.-]+", package["url"]),
            f"Unexpected dependency URL: {package['name']}")
for path in ROOT.glob("comparator*.json"):
    config = json.loads(path.read_text())
    require(config["challenge_module"] == "RenyiMonotonicityChallenge", "Wrong Challenge")
    require(config["solution_module"] == "RenyiMonotonicitySolution", "Wrong Solution")
    require(config["theorem_names"] and len(set(config["theorem_names"])) == len(config["theorem_names"]),
            f"Missing or duplicate contracts: {path}")
    require(set(config["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"},
            f"Unexpected permitted axioms: {path}")
for path in ROOT.glob("*.md"):
    require(not any(ord(c) < 32 and c not in "\n\t" for c in path.read_text()),
            f"Control character in document: {path}")
print(f"Source checks passed: {len(files)} Lean modules; full proof status is recorded separately.")
