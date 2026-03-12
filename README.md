# QASMInfer

QASMInfer is a verified exact inference engine for quantum circuits written in
OpenQASM. The core inference algorithm is formalized and proven correct in Rocq,
and extracted to OCaml for execution.

Currently, QASMInfer supports OpenQASM 2 and provides partial support for
OpenQASM 3.

## Prereqs

- `dune` (tested with 3.20.x)
- `ocaml`

Suggested install via opam:

```bash
opam install dune ocaml
```

`rocq`/`coq` is not required for the default build on this branch. The verified
Rocq development remains in `theories/`, but `dune build` consumes the bundled
OCaml extraction committed under `src/lib/extracted/extracted.ml`.

## Layout

```
theories/
  extract/Extract.v              # extraction driver
  extract/extraction_header.txt  # header prepended to extracted OCaml
  dune.disabled                  # archived Rocq-specific dune integration
  ...                            # QASMInfer theories and implementation
scripts/patch_extraction.sh      # prepends header to generated file
src/lib/
  extracted/extracted.ml         # bundled OCaml extracted from Rocq
  qasm2/                         # OpenQASM 2 parser/desugar/stringifier
  qasm3/                         # OpenQASM 3 parser/desugar (partial)
src/bin/                         # CLI that parses QASM, runs QASMInfer, prints result
```

## Build and run

This branch intentionally excludes Rocq verification and extraction from the
default `dune` build graph so users without Rocq installed can still build the
project. `dune build` uses the committed OCaml extraction directly.

```bash
dune build             # builds the bundled OCaml libraries + executable
dune exec qasminfer test.qasm
```

The `theories/` sources are still shipped for reference, but verification and
re-extraction are out of band on this branch.

After installing into your opam switch:

```bash
dune install           # installs library + executable
qasminfer test.qasm    # run the installed executable
```

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
