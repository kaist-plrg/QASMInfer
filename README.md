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

Building the proofs or regenerating the extraction uses a separate proof
toolchain with Dune 3.23.1, `rocq-core` 9.1.0, and `rocq-stdlib` 9.0.0. Rocq
9.1.0 requires Dune earlier than 3.24, so do not install it in the consumer
switch above; use a dedicated proof switch instead. The private proof project
therefore uses Dune's Rocq language version 0.13.

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
  qasm3/                         # OpenQASM 3 parser/desugar/sugar (partial)
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
and emits canonical OpenQASM 2 or OpenQASM 3. This is a normalized rewrite, not
a text-preserving one: comments, barriers, includes, gate declarations, call
names, expression spelling, and parallel syntax may be lost or expanded.

### CLI options

- `--unoptimize SOURCE DESTINATION`, `--unopt SOURCE DESTINATION`: apply
  unoptimization and write the result.
- `--unoptimize-rules SOURCE`: print the currently applicable unoptimization
  rules without rewriting.
- `--rule NAME`: restrict unoptimization to one built-in or loaded rule. This
  applies exactly one rewrite and cannot be combined with `--step`.
- `--step N`: apply up to `N` random unoptimization rewrites.
- `--seed N`: seed the generator that picks random rewrites, making `--step`
  reproducible.
- `--rule-file FILE`: append JSON-defined standard-gate rewrite rules after the
  built-in rules.
- `--emit auto|oq2|oq3`: choose the destination dialect. See
  [Destination dialect](#destination-dialect).
- `--qbits 0`, `--qbits 0,1`: manually choose qbit parameters for
  `--unoptimize --rule NAME`.
- `--cbits 0`: manually choose cbit parameters for
  `--unoptimize --rule NAME`.
- `--instr TEXT`, `--instr-file FILE`: fix the instruction a `cbit_instr` rule
  inserts. See [Addressing a rewrite](#addressing-a-rewrite).
- `--occurrence N`: manually choose the matched occurrence for
  `--unoptimize --rule NAME`. See
  [Occurrence semantics](#occurrence-semantics).
- `--verbose`, `-v`: print the OpenQASMCore program to stderr.
- `--json`: emit JSON in execution mode or `--unoptimize-rules` mode.
- `--output FILE`, `-o FILE`: write execution or `--unoptimize-rules` output to
  a file.

Execution-only `--json` and `--output`/`-o` cannot be combined with
`--unoptimize`. `--emit`, `--seed`, `--instr`, and `--instr-file` require
`--unoptimize`; the manual parameter options additionally require `--rule NAME`.

### Destination dialect

Two built-in rule families produce a *nested* single-bit guard:
`Insert_If_FT` and `Insert_If_TF` insert `if(c==false) if(c==true) INSTR` (resp.
reversed) at an empty site, and `Double_If_True` and `Double_If_False` duplicate
an existing guard. OpenQASM 2 has neither nested conditionals nor single-bit
guards, so these programs cannot be written in it at all.

`--emit` selects how that is handled:

- `auto` (default): write OpenQASM 2 whenever the program can be expressed in
  it, and OpenQASM 3 otherwise. Every program that OpenQASM 2 could express
  before is byte-identical under `auto`.
- `oq2`: always write OpenQASM 2, and fail with an `emit` error rather than
  approximate an inexpressible program.
- `oq3`: always write OpenQASM 3.

OpenQASM 3 output declares `include "stdgates.inc";`, uses `qubit[n]` and
`bit[n]` declarations, writes measurement as `c[i] = measure q[j];`, and writes
a single-bit guard as `if (c[i]) { ... }` or `if (!c[i]) { ... }`. Because
QASMCore only ever guards one classical bit, a whole-register comparison is
emitted as the equivalent chain of per-bit guards rather than reconstructed as
`c == n`. `sxdg` is emitted as a literal `U` rotation, since `stdgates.inc`
does not declare it.

Whatever `qasminfer` writes, `qasminfer` reads back to the same QASMCore
program; re-running `--unoptimize --step 0 --emit oq3` on its own output is a
fixed point.

### Occurrence semantics

`--occurrence K` selects which matched site a rule rewrites. `K` is a 0-based
ordinal over the sites of the *lowered QASMCore program*, not over lines of the
source. Two orderings exist, chosen per rule by its transform strategy:

- **`TransformDeep`** (every built-in except `Insert_Swap`). Sites are the
  positions *before* each instruction, visited in preorder: a position is
  counted, then the subtree of the instruction at that position (an `IfInstr`
  body, or a nested sequence), then the following siblings. There is no site
  after the last instruction of a sequence.
- **`TransformTopLevel`** (`Insert_Swap` only). Only the positions of the
  outermost sequence are sites; the rewrite never descends into an `IfInstr`
  body or a nested sequence.

For example, `Insert_I` on

```qasm
h q[0];
if(c==1) x q[0];
t q[0];
```

reports four sites, which `--occurrence 0` through `3` place before `h`, before
the `if`, before `x` *inside* the guard, and before `t`. Occurrence 2 is the
guard's body: the subtree of the instruction at position 1 comes before that
instruction's siblings. There is no occurrence 4.

`--unoptimize-rules` reports, for each applicable rule, the site count for a
single *representative* parameter -- `qbit1` counted at qubit 0, `qbit2` at
qubits (0, 1), `cbit_instr` at bit 0 with a `nop` payload, and `none` with no
parameter. It is not a sum over all admissible parameters, and a rule whose
representative parameter does not exist (for instance a `qbit2` rule on a
one-qubit program) is omitted from the listing entirely.

### Addressing a rewrite

`--rule NAME` plus its parameters and `--occurrence` pin a rewrite completely,
so repeated runs of the same command agree byte for byte:

```bash
qasminfer --unoptimize --rule Insert_Swap --qbits 0,1 --occurrence 0 in.qasm out.qasm
qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 \
  --instr 'x q[0];' in.qasm out.qasm
```

Rules taking two qubits require them to be **distinct**. The underlying Rocq
transforms do not: `Transform_swap_insert` and `Transform_cnot_cnot` assume only
that each index is in range, and the matrix model is total at equal indices
(`mat_swap q q` and `mat_cnot q q` are both the identity). OpenQASM is the part
that objects -- neither dialect allows naming one qubit twice in a gate -- so
`--qbits 0,0` is refused rather than producing `swap q[0],q[0];`.

`--instr` fixes the payload that `Insert_If_FT` and `Insert_If_TF` insert;
without it the payload is drawn at random and the run is not reproducible. The
payload is parsed against the source program's own register layout, so it
accepts either dialect's statement syntax, may contain several statements, and
may itself be conditional. It names registers by the canonical names the
destination would use -- for an OpenQASM 3 source using physical qubits, that is
the renamed register (`qasm3_physical[0]`), not `$0`. A payload that declares
registers or references an out-of-range index is rejected.

### Exit codes and error classes

| exit | meaning |
| --- | --- |
| 0 | success |
| 1 | domain error: one stderr line, `qasminfer: <class>: <detail>` |
| 2 | argument-shape error: usage text on stderr |

The error classes are stable:

| class | raised by |
| --- | --- |
| `io` | `SOURCE` cannot be read, `DESTINATION` cannot be written |
| `parse` | lexical or syntax error, unsupported or missing QASM version |
| `rule-file` | `--rule-file` is unreadable, malformed, or holds an invalid rule |
| `rule` | unknown rule name, duplicate rule name, rule not applicable |
| `param` | bad `--qbits`/`--cbits`/`--instr` value for the selected rule |
| `occurrence` | `--occurrence` out of range for the selected rule |
| `emit` | the program cannot be expressed in the requested dialect |
| `internal` | an unexpected failure; please report it |

A failing invocation never creates or truncates `DESTINATION`. With `--json`,
a domain error is additionally written to stdout as
`{"error": {"class": ..., "message": ...}}`. The one exception to the table is
a bare `qasminfer` with no arguments, which keeps its legacy exit status of 1
and prints usage.

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

A rule's qubit indices are pattern *variables*, not fixed positions: `I_to_XX`
above rewrites an `id` on **any** qubit, and `Swap_to_3Cnot` rewrites a `swap`
on any ordered pair. Two consequences follow.

- **The left-hand side must bind every qubit the right-hand side rewrites.**
  A rule whose `rhs` names a qubit index absent from its `lhs` can never fire,
  so it is rejected when the file is loaded. In particular an empty `lhs` binds
  nothing and cannot carry a non-empty `rhs`; to insert at an empty site, apply
  the built-in `Insert_I` first and then a rule with `lhs: [{"gate": "id", ...}]`.
- **The rule's width is not capped.** Only per-gate arity is: the grammar has no
  three-qubit gate. Multi-qubit gates outside the grammar are still expressible
  as rules, because the front ends macro-expand them before anything reaches the
  checker. `cz` is `h;cx;h`, `cy` is `sdg;cx;s`, and `ccx` and `cswap` expand
  into the same alphabet, so `cz;cz -> id;id` and friends are ordinary rule-file
  entries today.

Validity is checked up to a global phase drawn from the eight 8th roots of
unity; a rule whose two sides differ by any other phase is rejected.

### Output formats

Execution output:

```
00 : 5.0000000000000011e-01   # probability for creg being [00]
01 : 4.9999999999999989e-01   # probability for creg being [01]
10 : 0.0000000000000000e+00   # probability for creg being [10]
11 : 0.0000000000000000e+00   # probability for creg being [11]
```

Unoptimization writes canonical OpenQASM to the destination file. For example,
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

A rule that produces a nested guard falls back to OpenQASM 3:

```bash
dune exec qasminfer -- --unoptimize --rule Insert_If_FT --cbits 0 \
  --occurrence 0 --instr 'x q[0];' input.qasm output.qasm
```

```qasm
OPENQASM 3.0;
include "stdgates.inc";
qubit[1] q;
bit[1] c;
if (!c[0]) {
  if (c[0]) {
    x q[0];
  }
}
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
QASMINFER_SOURCE_COMMIT="$(theories/extraction/source_commit.sh)" \
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
QASMINFER_SOURCE_COMMIT="$(theories/extraction/source_commit.sh)" \
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
