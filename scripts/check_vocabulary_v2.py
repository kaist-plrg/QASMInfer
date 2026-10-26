#!/usr/bin/env python3
"""CLI acceptance probe; optionally compare a v1 executable and load catalogs.

Run after dune build. Catalogs must obey the existing lhs-binding contract.
This script writes only to a temporary directory and prints a JSON report.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import tempfile
import time

GATES = {"cz": 2, "cy": 2, "ch": 2, "csx": 2,
         "ccx": 3, "cswap": 3, "rccx": 3}


def run(executable, *args):
    start = time.perf_counter()
    result = subprocess.run([str(executable), *map(str, args)],
                            capture_output=True, text=True, check=True)
    return result.stdout, time.perf_counter() - start


def probabilities(executable, source):
    output, _ = run(executable, "--json", source)
    return {row["state"]: row["probability"]
            for row in json.loads(output)["probabilities"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, default=Path("_build/default/src/bin/main.exe"))
    parser.add_argument("--v1", type=Path)
    parser.add_argument("--catalog", action="append", type=Path, default=[])
    parser.add_argument("--corpus", action="append", type=Path, default=[])
    args = parser.parse_args()
    if args.corpus and not args.v1:
        parser.error("--corpus requires --v1")
    executable = args.exe.resolve()
    report = {"round_trips": 0, "semantic_cases": 0, "max_tv": 0.0, "catalogs": []}
    with tempfile.TemporaryDirectory(prefix="qasminfer-v2-") as tmp:
        tmp = Path(tmp)
        source, output = tmp / "input.qasm", tmp / "output.qasm"
        # Permuting roles exercises controls, targets and register boundaries.
        for name, arity in GATES.items():
            for wires in itertools.permutations(range(3), arity):
                call = name + " " + ",".join(f"q[{q}]" for q in wires) + ";"
                program = ('OPENQASM 2.0; include "qelib1.inc"; qreg q[4]; creg c[4];\n'
                           'x q[1]; h q[0]; h q[2]; cx q[2],q[3]; t q[0];\n' + call + '\n'
                           'h q[0]; h q[1]; h q[2]; measure q -> c;\n')
                source.write_text(program)
                for dialect in ("oq2", "oq3"):
                    run(executable, "--unoptimize", "--step", 0, "--emit", dialect, source, output)
                    text = output.read_text()
                    assert call in text, (name, wires, dialect, "name lost")
                    again = tmp / "again.qasm"
                    run(executable, "--unoptimize", "--step", 0, "--emit", dialect, output, again)
                    assert text == again.read_text(), (name, wires, dialect, "unstable output")
                    report["round_trips"] += 1
                if args.v1:
                    # Compare each engine's own step-0 output, as required by
                    # the vocabulary proposal, under each engine's semantics.
                    old = tmp / "v1.qasm"
                    run(args.v1.resolve(), "--unoptimize", "--step", 0, source, old)
                    left, right = probabilities(args.v1.resolve(), old), probabilities(executable, output)
                    tv = sum(abs(left.get(k, 0.) - right.get(k, 0.))
                             for k in left.keys() | right.keys()) / 2
                    assert tv < 1e-12, (name, wires, tv)
                    report["max_tv"] = max(report["max_tv"], tv)
                    report["semantic_cases"] += 1
        report["corpus"] = []
        for path in args.corpus:
            old = tmp / "v1.qasm"
            run(args.v1.resolve(), "--unoptimize", "--step", 0, path.resolve(), old)
            run(executable, "--unoptimize", "--step", 0, path.resolve(), output)
            left, right = probabilities(args.v1.resolve(), old), probabilities(executable, output)
            tv = sum(abs(left.get(k, 0.) - right.get(k, 0.))
                     for k in left.keys() | right.keys()) / 2
            assert tv < 1e-12, (path, tv)
            report["corpus"].append({"path": str(path), "tv": tv,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        source.write_text('OPENQASM 2.0; include "qelib1.inc"; qreg q[3]; ccx q[0],q[1],q[2];\n')
        for path in args.catalog:
            data = path.read_bytes()
            rules = json.loads(data)
            if isinstance(rules, dict):
                rules = rules["rules"]
            # Avoid silently counting rules skipped because their width exceeds
            # the probe program. The accepted catalogs are at most three wires.
            assert all(v < 3 for r in rules for side in ("lhs", "rhs")
                       for g in r[side] for k, v in g.items() if k != "gate")
            _, elapsed = run(executable, "--unoptimize", "--step", 0,
                             "--rule-file", path.resolve(), source, output)
            report["catalogs"].append({"path": str(path), "rules": len(rules),
                "sha256": hashlib.sha256(data).hexdigest(), "seconds": elapsed})
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
