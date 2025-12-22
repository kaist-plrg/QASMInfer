# QASMInfer

QASMInfer is a verified exact inference engine for quantum circuits written in
OpenQASM. The core inference algorithm is formalized and proven correct in Rocq,
and extracted to OCaml for execution.

Currently, QASMInfer supports OpenQASM 2 and provides partial support for
OpenQASM 3.

## Prereqs

- `dune` (tested with 3.20.x)
- `rocq`/`coq` (tested with Rocq 9.1.0)
- `ocaml`

Suggested install via opam:

```bash
opam install dune rocq
```

## Layout

```
theories/
  extract/Extract.v              # extraction driver
  extract/extraction_header.txt  # header prepended to extracted OCaml
  ...                            # QASMInfer theories and implementation
scripts/patch_extraction.sh      # prepends header to generated file
src/lib/
  extracted/                     # extracted QASMInfer
  qasm2/                         # OpenQASM 2 parser/desugar/stringifier
  qasm3/                         # OpenQASM 3 parser/desugar (partial)
src/bin/                         # CLI that parses QASM, runs QASMInfer, prints result
```

## Build and run

The build pipeline ensures that the executable is always generated from the verified Rocq development.

```bash
dune build             # builds Rocq theory, extracts to OCaml, builds library + exe
dune exec qasminfer test.qasm
```

After installing into your opam switch:

```bash
dune install           # installs library + executable
qasminfer test.qasm    # run the installed executable
```

Example output:

```
00: 0.5                # probability for creg being [00]
01: 0.0                # probability for creg being [01]
10: 0.0                # probability for creg being [10]
11: 0.5                # probability for creg being [11]
```

## Publication

_Exact Inference for Quantum Circuits: A Testing Oracle for Quantum Software Stacks_, ASE 2025
