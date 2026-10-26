#!/usr/bin/env python3
"""Python stdlib only. Compare immutable test fixtures with frozen CLI binaries.

The original --baseline/--candidate invocation checks task-79 against ee83932.
Adding --pinned-baseline enables task-80: the composite-free union of 4a9ea80
and 22caa1d fixtures is checked against both binaries. All differences, including
historical default-sampler differences, are reported and cause exit status 1.
Only temporary destinations are written. --json is used for rule listing only;
this script never simulates a program, builds a binary, or changes a baseline.
"""
import argparse
import codecs
import collections
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NEW_RULE = "Insert_Dead_If_Bit"
COMPOSITES = frozenset({"cz", "cy", "ch", "csx", "ccx", "cswap", "rccx"})
SEEDS = (0, 79, 20261025)
EMISSIONS = ("oq2", "oq3", "auto")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def run(binary, args):
    return subprocess.run([str(binary), *map(str, args)], capture_output=True)


def sha256(content):
    return hashlib.sha256(content).hexdigest()


def fixture_union(refs, extended):
    """Retain distinct versions of a path, merging only identical path/content.

    Text fixtures include tracked .qasm files and cram heredocs. Task-80 also
    includes printf-authored fixtures (including malformed byte inputs), and
    complete QASM raw literals in OCaml unit tests. Generated rewrite outputs
    and programmatically constructed OCaml ASTs are not independent text inputs.
    """
    fixtures = {}

    def add(ref, name, content, origin):
        key = (name, content)
        if key not in fixtures:
            fixtures[key] = {"name": name, "content": content, "origins": []}
        fixtures[key]["origins"].append(f"{ref}:{origin}")

    for ref in refs:
        names = git("ls-tree", "-r", "--name-only", ref, "test").decode().splitlines()
        for name in names:
            if not (name.endswith(".qasm") or name.endswith("/run.t")
                    or (extended and name.endswith(".ml"))):
                continue
            content = git("show", f"{ref}:{name}")
            if name.endswith(".qasm"):
                add(ref, name, content, name)
            elif name.endswith("/run.t"):
                lines = content.decode().splitlines()
                for i, line in enumerate(lines):
                    match = re.fullmatch(r"  \$ cat > ([\w.-]+\.qasm) <<'?(\w+)'?", line)
                    if match:
                        body = []
                        for following in lines[i + 1:]:
                            if following == f"  > {match[2]}":
                                break
                            if not following.startswith("  > "):
                                raise ValueError(f"Malformed heredoc at {ref}:{name}:{i + 1}")
                            body.append(following[4:])
                        else:
                            raise ValueError(f"Unclosed heredoc at {ref}:{name}:{i + 1}")
                        add(ref, str(Path(name).parent / match[1]),
                            ("\n".join(body) + "\n").encode(), f"{name}:{i + 1}")
                    elif extended and line.startswith("  $ printf "):
                        words = shlex.split(line[4:])
                        if len(words) >= 3 and words[-2] == ">" and words[-1].endswith(".qasm"):
                            # The frozen suites use a literal format with no
                            # format arguments; reject unfamiliar factories.
                            if len(words) != 4 or "%" in words[1]:
                                raise ValueError(f"Unsupported printf fixture: {ref}:{name}:{i + 1}")
                            body, _ = codecs.escape_decode(words[1].encode())
                            add(ref, str(Path(name).parent / words[-1]), body,
                                f"{name}:{i + 1}")
            else:
                number = 0
                for match in re.finditer(rb"\{([a-z_]*)\|(.*?)\|\1\}", content, re.DOTALL):
                    body = match[2]
                    if not body.lstrip().startswith(b"OPENQASM"):
                        continue
                    number += 1
                    line = content[:match.start()].count(b"\n") + 1
                    add(ref, f"{name}::qasm-literal-{number}", body, f"{name}:{line}")
    return sorted(fixtures.values(), key=lambda f: (f["name"], f["content"]))


def code_tokens(content):
    # Do not classify comments or include filenames as gate occurrences.
    text = content.decode("utf-8", errors="replace")
    text = re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"', " ", text, flags=re.DOTALL)
    return set(re.findall(r"\b[A-Za-z_][A-Za-z_0-9]*\b", text))


def explicit_payload(content):
    # The numeric --qbits/--cbits addressing is independent of register names,
    # while --instr must use an actual source register name.
    text = content.decode("utf-8", errors="replace")
    match = re.search(r"\bqreg\s+(\w+)\s*\[|\bqubit\s*\[\s*\d+\s*\]\s*(\w+)", text)
    if match:
        return f"id {match[1] or match[2]}[0];"
    match = re.search(r"\bqubit\s+(\w+)\s*;", text)
    if match:
        return f"id {match[1]};"
    return "id $0;" if re.search(r"\$\d+", text) else "id q[0];"


def bytes_record(content):
    if content is None:
        return None
    return {"sha256": sha256(content), "size": len(content),
            "text": content.decode("utf-8", errors="backslashreplace")}


def result_record(result):
    code, stdout, stderr, destination = result
    return {"exit": code, "stdout": bytes_record(stdout),
            "stderr": bytes_record(stderr), "destination": bytes_record(destination)}


def check_baseline(binary, candidate, commit, additions, fixtures, extended, directory):
    counts = collections.Counter()
    per_rule = collections.Counter()
    by_category = collections.defaultdict(collections.Counter)
    invalid = []
    mismatches = []
    source = directory / "source.qasm"
    destination = directory / "destination.qasm"

    def record(fixture, category, options, old, new):
        counts["cli_comparisons"] += 1
        by_category[category]["comparisons"] += 1
        if old == new:
            counts["identical_outputs" if old[3] is not None else "identical_refusals"] += 1
            by_category[category]["identical"] += 1
        else:
            counts["mismatches"] += 1
            by_category[category]["mismatches"] += 1
            mismatches.append({"fixture": fixture["name"], "origins": fixture["origins"],
                               "category": category, "options": options,
                               "baseline": result_record(old), "candidate": result_record(new)})

    def compare(fixture, category, options):
        results = []
        # Both runs see exactly the same path arguments, including DESTINATION,
        # so byte comparisons do not need path/diagnostic normalization.
        for executable in (binary, candidate):
            destination.unlink(missing_ok=True)
            result = run(executable, ["--unoptimize", *options, source, destination])
            results.append((result.returncode, result.stdout, result.stderr,
                            destination.read_bytes() if destination.exists() else None))
        record(fixture, category, options, *results)

    for fixture in fixtures:
        source.write_bytes(fixture["content"])
        old = run(binary, ["--unoptimize-rules", "--json", source])
        new = run(candidate, ["--unoptimize-rules", "--json", source])
        counts["listing_comparisons"] += 1
        rows = []
        if old.returncode == 0:
            counts["valid_fixtures"] += 1
            old_json = json.loads(old.stdout)
            rows = old_json["rules"]
            if new.returncode == 0:
                new_json = json.loads(new.stdout)
                new_json["rules"] = [row for row in new_json["rules"] if row["name"] not in additions]
                listing_equal = old_json == new_json and old.stderr == new.stderr
            else:
                listing_equal = False
        else:
            counts["invalid_fixtures"] += 1
            invalid.append(fixture["name"])
            listing_equal = (old.returncode, old.stdout, old.stderr) == (new.returncode, new.stdout, new.stderr)
        if not listing_equal:
            counts["listing_mismatches"] += 1
            mismatches.append({"fixture": fixture["name"], "origins": fixture["origins"],
                               "category": "listing", "allowed_candidate_additions": sorted(additions),
                               "baseline": result_record((old.returncode, old.stdout, old.stderr, None)),
                               "candidate": result_record((new.returncode, new.stdout, new.stderr, None))})
        if old.returncode and not extended:
            continue
        for emit in EMISSIONS:
            compare(fixture, "step0", ["--step", "0", "--emit", emit])
            for seed in SEEDS:
                compare(fixture, "default_step3", ["--step", "3", "--seed", str(seed), "--emit", emit])
            for row in rows:
                params = {"none": [], "qbit1": ["--qbits", "0"],
                          "qbit2": ["--qbits", "0,1"],
                          "qbit3": ["--qbits", "0,1,2"],
                          "cbit_instr": ["--cbits", "0", "--instr",
                                         explicit_payload(fixture["content"]) if extended else "id q[0];"]}[row["param"]]
                for index in range(row["occurrences"]):
                    compare(fixture, "explicit_occurrence", ["--rule", row["name"], *params,
                            "--occurrence", str(index), "--seed", "79", "--emit", emit])
                    per_rule[row["name"]] += 1
                # Also preserve each rule's generated-payload/parameter policy.
                compare(fixture, "generated_parameters", ["--rule", row["name"],
                        "--seed", "79", "--emit", emit])
                per_rule[row["name"]] += 1
    return {"baseline_commit": commit, "baseline_path": str(binary),
            "baseline_sha256": sha256(binary.read_bytes()),
            "passed": not mismatches, "counts": dict(counts),
            "by_category": {name: dict(values) for name, values in sorted(by_category.items())},
            "existing_rules": dict(sorted(per_rule.items())),
            "invalid_fixtures": invalid,
            "invalid_fixtures_skipped": [] if extended else invalid,
            "mismatches": mismatches}


def check_frozen_surface(bench):
    if bench is None:
        return []
    surface_files = sorted(set(
        list((bench / "scripts").rglob("build_*.py")) +
        list((bench / "data/suite-v1").rglob("*.toml")) +
        list((bench / "data/suite-v2").rglob("*.toml")) +
        [bench / "qasm_opt_bench.toml", bench / "qasm_opt_bench/ocaml_rule_engine.py"]
    ))
    surface_files = [p if p.exists() else bench / "src" / p.relative_to(bench)
                     for p in surface_files]
    if not surface_files or not all(p.is_file() for p in surface_files):
        raise ValueError("Incomplete frozen benchmark surface")
    for path in surface_files:
        if NEW_RULE in path.read_text():
            raise ValueError(f"D56 surface leak: {path}")
    return [str(p.relative_to(bench)) for p in surface_files]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--pinned-baseline", type=Path,
                        help="22caa1d binary; enables task-80 union and composite-free filter")
    parser.add_argument("--baseline-commit", help="primary baseline fixture ref (default: ee83932, or 4a9ea80 in task-80 mode)")
    parser.add_argument("--fixture-ref", action="append", help="explicit fixture ref(s), replacing the default union")
    parser.add_argument("--composite-free", action="store_true", help="exclude fixtures naming any of the seven composites")
    parser.add_argument("--benchmark-root", type=Path)
    parser.add_argument("--output", type=Path, help="also save the complete JSON report here")
    args = parser.parse_args()
    extended = args.pinned_baseline is not None
    commit = args.baseline_commit or ("4a9ea80" if extended else "ee83932")
    refs = args.fixture_ref or ([commit, "22caa1d"] if extended else [commit])
    fixtures = fixture_union(refs, extended)
    selected, excluded = [], []
    for fixture in fixtures:
        names = sorted(COMPOSITES & code_tokens(fixture["content"]))
        if (extended or args.composite_free) and names:
            excluded.append({"fixture": fixture["name"], "origins": fixture["origins"],
                             "composites": names, "sha256": sha256(fixture["content"])})
        else:
            selected.append(fixture)
    if not selected:
        raise ValueError("No fixtures selected")
    baselines = [(args.baseline.resolve(), commit, set() if extended else {NEW_RULE})]
    if extended:
        baselines.append((args.pinned_baseline.resolve(), "22caa1d", {NEW_RULE, "Double_Measure"}))
    candidate = args.candidate.resolve()
    with tempfile.TemporaryDirectory(prefix="task80-identity-" if extended else "task79-identity-") as directory:
        reports = [check_baseline(binary, candidate, ref, additions, selected, extended, Path(directory))
                   for binary, ref, additions in baselines]
    report = {"passed": all(item["passed"] for item in reports),
              "candidate_path": str(candidate), "candidate_sha256": sha256(candidate.read_bytes()),
              "fixture_refs": refs, "fixture_count": len(fixtures),
              "selected_fixture_count": len(selected), "composite_fixtures_excluded": excluded,
              "fixture_scope": "tracked QASM and cram heredocs; task-80 additionally includes cram printf and OCaml QASM raw literals",
              "fixtures": [{"name": f["name"], "origins": f["origins"],
                            "sha256": sha256(f["content"])} for f in selected],
              "emission_modes": list(EMISSIONS), "default_step3_seeds": list(SEEDS),
              "baselines": reports, "d56_files_checked": check_frozen_surface(args.benchmark_root)}
    if not extended:
        # Retain the original top-level summary fields for task-79 consumers.
        report.update({key: reports[0][key] for key in ("baseline_commit", "baseline_sha256",
                       "counts", "existing_rules", "invalid_fixtures_skipped")})
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
