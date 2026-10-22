#!/usr/bin/env python3
"""Build native-name acceptance fixtures from a pinned expanded explorer catalog.

The expanded exporter encodes its original words in Q<n>C_<lhs>_to_<rhs> names.
Keep its direction, rule selection and explicit lhs identity padding. This is a
fixture adapter, not a relaxation of QASMInfer's rule admission checks. Always
validate the result with check_vocabulary_v2.py --catalog before using it.
"""
import argparse
import json
from pathlib import Path
import re

ROLES = {
    **{g: ("q",) for g in ("id", "x", "y", "z", "h", "s", "sdg", "t", "tdg", "sx", "sxdg")},
    **{g: ("control", "target") for g in ("cx", "cz", "cy", "ch", "csx")},
    "swap": ("q1", "q2"), "ccx": ("control1", "control2", "target"),
    "rccx": ("control1", "control2", "target"), "cswap": ("control", "q1", "q2"),
}


def wires(gates):
    return {v for gate in gates for k, v in gate.items() if k != "gate"}


def word_gates(word, width):
    if word == "I":
        return [{"gate": "id", "q": q} for q in range(width)]
    result = []
    for letter in word.split("_"):
        match = re.fullmatch(r"([A-Z]+)([0-9]+)", letter)
        if not match or match[1].lower() not in ROLES:
            raise ValueError(f"unrecognized explorer letter: {letter}")
        name, operands = match[1].lower(), list(map(int, match[2]))
        if any(q >= width for q in operands):
            raise ValueError(f"out-of-range explorer letter: {letter}")
        result.append(dict(gate=name, **dict(zip(ROLES[name], operands, strict=True))))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    if args.source.resolve() == args.destination.resolve():
        parser.error("source and destination must differ")
    rules = json.loads(args.source.read_text())
    for rule in rules:
        match = re.fullmatch(r"Q([23])C_(.+)_to_(.+)", rule["name"])
        if not match:
            raise ValueError(f"not a 2/3-wire expanded explorer rule: {rule['name']}")
        width = int(match[1])
        lhs, rhs = word_gates(match[2], width), word_gates(match[3], width)
        lhs += [{"gate": "id", "q": q} for q in sorted(wires(rule["lhs"]) - wires(lhs))]
        if wires(rhs) - wires(lhs):
            raise ValueError(f"unbound rhs qubits in {rule['name']}")
        rule.update(lhs=lhs, rhs=rhs)
    args.destination.write_text(json.dumps(rules, separators=(",", ":")))
    print(f"wrote {len(rules)} named rules to {args.destination}")


if __name__ == "__main__":
    main()
