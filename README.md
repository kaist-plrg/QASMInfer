# QASMInfer Unoptimization Framework

This branch extends QASMInfer with an experimental unoptimization framework.
QASMInfer itself is a verified exact inference engine for quantum circuits
written in OpenQASM; this version keeps that execution path and adds a Rocq-side
rewrite framework plus an OCaml CLI path for applying validated rewrite rules.

## Prereqs

- `dune` 3.24 or newer
- `rocq` (tested with Rocq 9.1.0)
- `ocaml`
- OCaml libraries: `yojson`, `zarith`

Suggested install via opam:

```bash
opam install dune rocq yojson zarith
```

## Layout

```
theories/
  extract/Extract.v              # extraction driver
  extract/extraction_header.txt  # header prepended to extracted OCaml
  rewrite/                       # rewrite specs and rewrite engine
  domega/StandardValid.v         # exact multi-qubit standard-gate validation
  ...                            # QASMInfer theories and implementation
scripts/patch_extraction.sh      # prepends header to generated file
src/lib/
  extracted/                     # extracted QASMInfer
  unoptimize/                    # OCaml rule loading and rewrite driver
  qasm2/                         # OpenQASM 2 parser/desugar/stringifier
  qasm3/                         # OpenQASM 3 parser/desugar (partial)
src/bin/                         # CLI execution and OpenQASM rewrite modes
```

## Build and run

Build the Rocq development, extracted OCaml library, and CLI executable:

```bash
dune build
```

Run exact inference:

```bash
dune exec qasminfer -- test.qasm
```

Install and run from the current opam switch:

```bash
dune install
qasminfer test.qasm
```

Unoptimize a program without executing it:

```bash
dune exec qasminfer -- --unoptimize input.qasm output.qasm
```

The rewrite path parses OpenQASM 2 or the supported OpenQASM 3 subset, lowers
the program to OpenQASMCore, applies extracted transformation specifications,
and emits canonical OpenQASM 2. This is a normalized rewrite, not a
text-preserving one: comments, barriers, includes, gate declarations, call
names, expression spelling, and parallel syntax may be lost or expanded.

### CLI options

- `--unoptimize SOURCE DESTINATION`, `--unopt SOURCE DESTINATION`: apply
  unoptimization and write canonical OpenQASM 2.
- `--unoptimize-rules SOURCE`: print the currently applicable unoptimization
  rules without rewriting.
- `--rule NAME`: restrict unoptimization to one built-in or loaded rule. This
  applies exactly one rewrite and cannot be combined with `--step`.
- `--step N`: apply up to `N` random unoptimization rewrites.
- `--rule-file FILE`: append JSON-defined standard-gate rewrite rules after the
  built-in rules.
- `--qbits 0`, `--qbits 0,1`: manually choose qbit parameters for
  `--unoptimize --rule NAME`.
- `--cbits 0`: manually choose cbit parameters for
  `--unoptimize --rule NAME`.
- `--occurrence N`: manually choose the matched occurrence for
  `--unoptimize --rule NAME`.
- `--verbose`, `-v`: print the OpenQASMCore program to stderr.
- `--json`: emit JSON in execution mode or `--unoptimize-rules` mode.
- `--output FILE`, `-o FILE`: write execution or `--unoptimize-rules` output to
  a file.

Execution-only `--json` and `--output`/`-o` cannot be combined with
`--unoptimize`. Manual parameter options require `--unoptimize --rule NAME`.

### Rule files

`--rule-file FILE` accepts either an array of rules or an object with a `rules`
array. Each JSON rule is validated exactly before rewriting starts, using
arithmetic over `Q[omega] / (omega^4 + 1)` and accepting global phase by powers
of `omega = exp(i pi / 4)`:

```json
[
  {
    "name": "I_to_XX",
    "lhs": [{ "gate": "id", "q": 0 }],
    "rhs": [{ "gate": "x", "q": 0 }, { "gate": "x", "q": 0 }]
  },
  {
    "name": "Swap_to_3Cnot",
    "lhs": [{ "gate": "swap", "q1": 0, "q2": 1 }],
    "rhs": [
      { "gate": "cx", "control": 0, "target": 1 },
      { "gate": "cx", "control": 1, "target": 0 },
      { "gate": "cx", "control": 0, "target": 1 }
    ]
  }
]
```

Gate names are `id`, `x`, `y`, `z`, `h`, `s`, `sdg`, `t`, `tdg`, `sx`, and
`sxdg`, plus two-qubit `cx` and `swap`. Rules that reference qubit indices
outside the source program are ignored; invalid in-bounds rules and duplicate
rule names in the combined built-in and rule-file rule set are rejected without
writing the destination.

### Output formats

Execution output:

```
00 : 5.0000000000000011e-01   # probability for creg being [00]
01 : 4.9999999999999989e-01   # probability for creg being [01]
10 : 0.0000000000000000e+00   # probability for creg being [10]
11 : 0.0000000000000000e+00   # probability for creg being [11]
```

Unoptimization writes canonical OpenQASM 2 to the destination file. For example,
running:

```bash
dune exec qasminfer -- --unoptimize --rule Insert_Swap --qbits 0,1 input.qasm output.qasm
```

can produce:

```qasm
OPENQASM 2.0;
include "qelib1.inc";
qreg q[2];
swap q[0],q[1];
h q[0];
```

JSON output:

```bash
dune exec qasminfer -- --json .test.qasm
dune exec qasminfer -- --json --output result.json .test.qasm
```

Example JSON:

```json
{
  "qubits": 1,
  "clbits": 2,
  "probabilities": [
    {"state": "00", "probability": 5.0000000000000011e-01},
    {"state": "01", "probability": 4.9999999999999989e-01},
    {"state": "10", "probability": 0.0000000000000000e+00},
    {"state": "11", "probability": 0.0000000000000000e+00}
  ]
}
```

## Publication

_Exact Inference for Quantum Circuits: A Testing Oracle for Quantum Software Stacks_, ASE 2025
