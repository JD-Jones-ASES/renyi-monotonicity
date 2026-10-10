#!/usr/bin/env python3
"""Audit exactly the selected declaration closure with Lean's axiom printer."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument("--config", default="comparator.json")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
config = json.loads((root / args.config).read_text())
names = config["theorem_names"]
permitted = set(config["permitted_axioms"])
with tempfile.TemporaryDirectory(prefix="renyi-axioms-") as directory:
    source = Path(directory) / "AxiomAudit.lean"
    source.write_text("import RenyiMonotonicitySolution\n" +
                      "".join(f"#print axioms {name}\n" for name in names))
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=root,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
for name in names:
    pattern = rf"'{re.escape(name)}' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
    matches = list(re.finditer(pattern, result.stdout))
    if len(matches) != 1:
        raise SystemExit(f"Expected exactly one axiom report for {name}")
    axioms = {x.strip() for x in (matches[0].group(1) or "").split(",") if x.strip()}
    if not axioms <= permitted:
        raise SystemExit(f"Forbidden axioms for {name}: {sorted(axioms - permitted)}")
print(f"PASS: permitted-axiom audit for {len(names)} selected declarations ({args.config}).")
