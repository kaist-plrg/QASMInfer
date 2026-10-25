#!/usr/bin/env python3
"""Python stdlib only. Compare task-70 CLI fixtures against an ee83932 binary.

Uses temporary outputs only. Optionally checks the benchmark's frozen surface
read-only; it never builds or executes its oracle, adapters, or lane builders.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NEW_RULE = "Insert_Dead_If_Bit"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT).decode()


def run(binary, args):
    return subprocess.run([str(binary), *map(str, args)], capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--benchmark-root", type=Path)
    args = parser.parse_args()
    fixtures = {}
    for name in git("ls-tree", "-r", "--name-only", "ee83932", "test").splitlines():
        if name.endswith(".qasm"):
            fixtures[name] = git("show", f"ee83932:{name}")
        elif name.endswith("/run.t"):
            lines = git("show", f"ee83932:{name}").splitlines()
            for i, line in enumerate(lines):
                match = re.match(r"  \$ cat > ([\w.-]+\.qasm) <<'?(\w+)'?$", line)
                if not match:
                    continue
                content = []
                for following in lines[i + 1:]:
                    if following == f"  > {match[2]}":
                        break
                    assert following.startswith("  > "), following
                    content.append(following[4:])
                fixtures[str(Path(name).parent / match[1])] = "\n".join(content) + "\n"
    counts = collections.Counter()
    per_rule = collections.Counter()
    skipped = []
    with tempfile.TemporaryDirectory(prefix="task79-identity-") as directory:
        directory = Path(directory)
        source = directory / "source.qasm"

        def compare(options):
            results = []
            for binary, suffix in [(args.baseline, "old"), (args.candidate, "new")]:
                dest = directory / f"{suffix}.qasm"
                dest.unlink(missing_ok=True)
                result = run(binary, ["--unoptimize", *options, source, dest])
                results.append((result.returncode, result.stdout, result.stderr,
                                dest.read_bytes() if dest.exists() else None))
            assert results[0] == results[1], (fixture, options, results)
            counts["cli_comparisons"] += 1
            counts["identical_outputs" if results[0][3] is not None else "identical_refusals"] += 1

        for fixture, content in sorted(fixtures.items()):
            source.write_text(content)
            listing = run(args.baseline, ["--unoptimize-rules", "--json", source])
            if listing.returncode:
                skipped.append(fixture)
                continue
            rows = json.loads(listing.stdout)["rules"]
            new_listing = run(args.candidate, ["--unoptimize-rules", "--json", source])
            assert new_listing.returncode == 0
            assert rows == [r for r in json.loads(new_listing.stdout)["rules"] if r["name"] != NEW_RULE]
            counts["valid_fixtures"] += 1
            for emit in ["oq2", "oq3", "auto"]:
                compare(["--step", "0", "--emit", emit])
                for seed in [0, 79, 20261025]:
                    compare(["--step", "3", "--seed", str(seed), "--emit", emit])
                for row in rows:
                    params = {"none": [], "qbit1": ["--qbits", "0"],
                              "qbit2": ["--qbits", "0,1"],
                              "cbit_instr": ["--cbits", "0", "--instr", "id q[0];"]}[row["param"]]
                    for index in range(row["occurrences"]):
                        compare(["--rule", row["name"], *params, "--occurrence", str(index),
                                 "--seed", "79", "--emit", emit])
                        per_rule[row["name"]] += 1
                    # Check the old generated-payload and parameter policy too.
                    compare(["--rule", row["name"], "--seed", "79", "--emit", emit])
                    per_rule[row["name"]] += 1

    surface_files = []
    if args.benchmark_root:
        bench = args.benchmark_root
        surface_files = sorted(set(
            list((bench / "scripts").rglob("build_*.py")) +
            list((bench / "data/suite-v1").rglob("*.toml")) +
            list((bench / "data/suite-v2").rglob("*.toml")) +
            [bench / "qasm_opt_bench.toml", bench / "qasm_opt_bench/ocaml_rule_engine.py"]
        ))
        # Source layout can be src/ in another checkout.
        surface_files = [p if p.exists() else bench / "src" / p.relative_to(bench)
                         for p in surface_files]
        assert surface_files and all(p.is_file() for p in surface_files)
        for path in surface_files:
            assert NEW_RULE not in path.read_text(), f"D56 surface leak: {path}"

    print(json.dumps({
        "baseline_commit": "ee83932",
        "baseline_sha256": hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        "candidate_sha256": hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        "fixture_count": len(fixtures), "counts": dict(counts),
        "existing_rules": dict(sorted(per_rule.items())),
        "invalid_fixtures_skipped": skipped,
        "d56_files_checked": [str(p.relative_to(args.benchmark_root)) for p in surface_files],
    }, indent=2))


if __name__ == "__main__":
    main()
