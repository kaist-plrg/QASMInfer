# QASMInfer Unoptimization Framework

This branch extends QASMInfer with an experimental unoptimization framework.
QASMInfer itself is a verified exact inference engine for quantum circuits
written in OpenQASM; this version keeps that execution path and adds a Rocq-side
rewrite framework plus an OCaml CLI path for applying validated rewrite rules.

The new framework is research code under active development. In particular, it
is intended for studying semantics-preserving circuit expansion rules, not for
text-preserving OpenQASM formatting or source-to-source refactoring.

Currently, QASMInfer supports OpenQASM 2 and provides partial support for
OpenQASM 3.

## Prereqs

- `dune` (tested with 3.20.x)
- `rocq`/`coq` (tested with Rocq 9.1.0)
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
  transform/Rewrite.v            # verified transformation specifications
  transform/StandardValid.v      # exact standard-gate rewrite validation
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

The build pipeline ensures that the executable is generated from the Rocq
development, including the extracted transformation framework.

```bash
dune build             # builds Rocq theory, extracts to OCaml, builds library + exe
```

The original exact inference mode is still available:

```bash
dune exec qasminfer -- test.qasm
```

After installing into your opam switch:

```bash
dune install           # installs library + executable
qasminfer test.qasm    # run the installed executable
```

To apply the unoptimization framework without executing the circuit, use
`--unoptimize` (or its `--unopt` alias) with an input and output path:

```bash
dune exec qasminfer -- --unoptimize input.qasm output.qasm
# or, after installation:
qasminfer --unoptimize input.qasm output.qasm
# equivalently:
qasminfer --unopt input.qasm output.qasm
```

The rewrite path parses and inlines the supported input, lowers it to
OpenQASMCore, applies extracted transformation specifications, and converts the
result back to OpenQASM. Both supported OpenQASM 2 and partial OpenQASM 3
inputs produce canonical OpenQASM 2 output.

This is a normalized rewrite, not a text-preserving one. Comments, barriers,
includes, gate declarations and call names, symbolic expression spelling, and
parallel syntax may be lost or expanded. Use `--verbose` (or `-v`) to print the
transformed OpenQASMCore program to stderr. Execution-only `--json` and
`--output`/`-o` options cannot be combined with `--unoptimize`.

`--rule-file FILE` adds JSON-defined single-qubit standard-gate rewrite rules to
the unoptimization rule set. The file may be an array of rules, or an object
with a `rules` array. Each rule is validated exactly before rewriting starts,
using arithmetic over `Q[omega] / (omega^4 + 1)` and accepting global phase by
powers of `omega = exp(i pi / 4)`:

```json
[
  { "name": "I_to_XX", "lhs": ["id"], "rhs": ["x", "x"] }
]
```

Gate names are `id`, `x`, `y`, `z`, `h`, `s`, `sdg`, `t`, `tdg`, `sx`, and
`sxdg`. Invalid rules, and duplicate rule names in the combined built-in and
rule-file rule set, are rejected without writing the destination.

`--rule NAME` restricts unoptimization to transform specs with the given name,
including rules loaded from `--rule-file`. It can only be used with
`--unoptimize`, cannot be combined with `--step`, and applies exactly one
rewrite. If the named rule exists but has zero matches in the current program,
the command returns an error instead of retrying.

Example output:

```
00 : 5.0000000000000011e-01   # probability for creg being [00]
01 : 4.9999999999999989e-01   # probability for creg being [01]
10 : 0.0000000000000000e+00   # probability for creg being [10]
11 : 0.0000000000000000e+00   # probability for creg being [11]
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
