# QASMInfer Unoptimization Framework

This branch extends QASMInfer with an experimental unoptimization framework.
QASMInfer itself is a verified exact inference engine for quantum circuits
written in OpenQASM; this version keeps that execution path and adds a Rocq-side
rewrite framework plus an OCaml CLI path for applying validated rewrite rules.

## Prereqs

- `dune` 3.24 or newer
- `ocaml`
- OCaml tools and libraries: `menhir`, `yojson`, `zarith`

The normal consumer build does not require Rocq. Suggested install via opam:

```bash
opam install dune.3.24.2 menhir yojson zarith
```

Building the proofs or regenerating the extraction additionally requires Rocq
(tested with `rocq-core` 9.1.0 and `rocq-stdlib` 9.0.0).

## Layout

```
theories/
  dune-project                  # private Rocq-only Dune project
  extracted.ml                  # committed, provenance-stamped extraction
  extract/Extract.v              # extraction driver
  extract/extraction_header.txt  # header prepended to extracted OCaml
  extraction/                    # regeneration and provenance rules/scripts
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

Build the extracted OCaml library and CLI executable from the committed
extraction:

```bash
dune build
dune build @install
```

Neither command loads the private Rocq project under `theories/`.

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

## Committed extraction and proof checking

`theories/extracted.ml` is committed so downstream users can build the OCaml
library and `qasminfer` executable without installing Rocq. This also prevents
different consumer machines from silently regenerating the executable with
different prover versions. The generated header records the source revision,
Rocq version, Dune Rocq language version, and exact extraction command.

Proof and generator input changes must be committed before regeneration. Then
regenerate and promote the new artifact with the explicit extraction alias:

```bash
dune build --root theories @extract --auto-promote
git add theories/extracted.ml
git commit -m "build: refresh committed Rocq extraction"
```

The source commit is the latest first-parent commit whose tree establishes the
current proof and extraction inputs, including merge commits and excluding
`theories/extracted.ml`. Regeneration verifies that the selected commit's input
tree matches the checkout. The input commit is made first and the generated
artifact is committed second because a Git commit cannot contain its own hash;
the artifact-only commit therefore does not create self-referential churn.

Build the complete proof development and check the committed artifact with:

```bash
dune build --root theories @proofs
dune build --root theories @check-extraction
```

The check reruns `rocq repl`, applies the same sandbox-safe patching
implementation exposed by `scripts/patch_extraction.sh`, and byte-compares the
result with `theories/extracted.ml`. The public patching script remains a
self-contained two-argument entry point. On a mismatch the check prints the
regeneration command and fails. Do not edit the generated OCaml directly.

**Trust argument:** the committed extraction is CI-verified to be
byte-identical to the extraction of the checked proofs; Rocq's extraction
mechanism remains part of the TCB.

## Publication

_Exact Inference for Quantum Circuits: A Testing Oracle for Quantum Software Stacks_, ASE 2025
