# QASMInfer vocabulary v2 — first-class qelib1 composites (draft, 2026-10-22)

Status: **draft for 유진 (Rocq) and 강욱 (CLI)**, track 2 of D49. Nothing in this document changes suite v1, which stays on the current engine (D48). Authored by the orchestrator from the engine source at submodule pin `22caa1d` and the explorer at `c2a66ed`; every file:line below was read, not assumed.

Implementation and validation completed in this checkout on 2026-10-22; see [§8](#8-implementation-and-validation). Sections 0–7 preserve the original proposal and its assumptions.

## 0. Summary

Make the parameter-free `qelib1.inc` composite gates that the explorer already enumerates — `cz cy ch csx` on two wires and `ccx cswap rccx` on three — **first-class instructions of QASMInfer**: kept by the parser instead of macro-expanded, expressible in rewrite patterns and rule files under their qelib1 names and wire roles, given exact semantics in the verified core and in the DOmega checker, and printed by name. `cx` and `swap` already are. Then the bench's composite-expansion machinery disappears (the explorer's `qasminfer-expanded` format, the mechanical self-inverse family, the long expanded left-hand sides), the generation surface becomes one sentence — *the explorer's exhaustive search over QASMInfer's vocabulary up to length 4 on at most three wires* — and named multi-controlled gates reach the tools unchanged, which is where ledger C, G and I live.

## 1. Why (bench-side facts, verified 2026-10-22)

- **The engine inlines every composite on input.** `qasminfer --unoptimize --step 0` turns `ccx; ccx; cswap` into 48 primitive gates and `cz; cy; ch` into their bodies; a single `Insert_I` application expands every composite in the program. `rz(pi)`, `rz(pi/2)` become `z`, `s`; other angles become `U(...)`. The core instruction language is `U`, `CX`, `swap`, measure, reset, if (`theories/program/Program.v:68`); all qelib1 gates are macros spliced by `inline_qelib` (`src/lib/qasm2/api.ml:1010`), and one-qubit names are re-sugared from `U` angles on output (`src/lib/qasm2/sugar.ml:513`, `qelib_gate_names`).
- **The rule grammar has 13 names** — `id x y z h s sdg t tdg sx sxdg cx swap` (`src/lib/unoptimize/unoptimize.ml:26`; wire keys `control`/`target`, `q1`/`q2`, `q` at `:130–143`). The explorer restricted its `primitives` alphabet to exactly these (`c2a66ed`, "restrict the search to QASMInfer's own gates").
- **Consequences in the bench.** No rung in any corpus contains a named `ccx`/`cswap` (0 of 4,876 preserved rungs). Composite relations have to be shipped as expansions: the 2-wire composite catalog's left-hand sides are 2–8 primitive gates and do fire (20 % of M-lane rungs), but the 3-wire composite catalog at length 4 is 158,077 rules of which only 12 (the `I → g g` pairs) have an `id` left-hand side; the other 158,065 have expanded left-hand sides of 2–62 gates that never match a random program. The three `SelfInverse_*` family rules exist only because of this (their content is byte-identical to the explorer's `Q3C_I_to_CCX012_CCX012` / `CSWAP012` / `RCCX012`). Named-gate ledger witnesses (C, G, I) cannot be rungs, so D47 ② was withdrawn and they enter suite v1 as seeds.
- **The explorer side is already done.** `--format qasminfer` (the non-expanded form) writes composite letters by name with role-keyed wires: `control`/`target` for `cx cz cy ch csx`, `q1`/`q2` for `swap`, `control1`/`control2`/`target` for `ccx rccx`, `control`/`q1`/`q2` for `cswap` (explorer README, "Wire arguments are keyed by their role"). The explorer's expansion table agrees with QASMInfer's bodies (checked by content identity for `cz`, `ccx`, `cswap`, `rccx`). Catalog sizes do not change between the two forms; only the spelling does: q2 `--gates qelib --max-length 4` = 10,716 composite-involving relations, q3 = 158,077, q3 length 2 = 293, length 3 = 5,751.

## 2. Scope

**Vocabulary v2** = the current 13 names + `cz cy ch csx ccx cswap rccx` = 20 names = the explorer's complete ≤3-wire parameter-free qelib alphabet. All seven are Clifford+T, so their matrices lie in D[ω] and the existing exact checker applies.

Out of scope (unchanged, still macro-expanded): every parametric gate (D18 excludes them from rules anyway); the 4- and 5-wire composites `rc3x c3x c3sqrtx c4x` (beyond the explorer's 3-wire cap; a possible v3); user-declared gates. OpenQASM 3: `stdgates.inc` has `ccx cswap cz cy ch swap` but **not `csx` or `rccx`** (`src/lib/qasm3/api.ml`), so the OQ3 emitter needs a decision for those two (emit a local declaration, or expand only on the OQ3 path).

## 3. Component map

### A. Verified core (Rocq) — 유진

1. **Instruction type** (`theories/program/Program.v:68`). Two options. (a) One constructor per gate, mirroring `CnotInstr`/`SwapInstr`: `CzInstr c t | CyInstr c t | ChInstr c t | CsxInstr c t | ToffoliInstr c1 c2 t | CswapInstr c q1 q2 | RccxInstr c1 c2 t`. (b) One constructor `CompositeInstr : CompositeGate -> list nat -> Instruction` with an enumerated `CompositeGate` and an arity table. (a) lets every proof copy the existing `SwapInstr` case; (b) makes a later v3 cheap but every lemma then cases on arity and list shape. Recommendation: (a) now.
2. **Execution semantics.** `Execute_<g>_instr_branch` / `Execute_<g>_instr` by `den_uop (mat_<g> …)` exactly like `Execute_cnot_instr` (`Program.v:827`), with `mat_cz`, `mat_cy`, `mat_ch`, `mat_csx`, `mat_ccx`, `mat_cswap`, `mat_rccx` as complex matrices. The lemma that makes v2 a **conservative extension**: each `mat_<g>` equals the denotation of the gate's qelib1 body on the same wires (`mat_cz c t = mat_h t · mat_cnot c t · mat_h t`, and so on for the seven bodies in `api.ml`'s `qelib_decl`), so a v1 program and its v2 reading denote the same state transformer.
3. **Well-formedness.** `Instruction_qbits_valid` (`theories/rewrite/RewriteFunction.v:1092`): wires distinct and in bounds; `Instruction_ind'` and every induction that cases on instructions. Today `CnotInstr` is matched at 6 sites in `RewriteFunction.v`, 6 in `theories/domega/StandardValid.v`, 4 in `Program.v`, 2 in `theories/transform/Commute.v`, 1 in `theories/transform/Equiv.v` (plus `Flatten.v`, `Transform.v`, `Valid.v` indirectly); each new constructor adds one case at each.
4. **Rewriting.** `InstructionPattern` (`RewriteFunction.v:292`) gains pattern constructors with `NatPattern` wires (`PCz … PToffoli PCswap PRccx`); matching, substitution, the binding invariant `RewriteRule_safeb` (`theories/rewrite/Validity.v:1243`) and the semantic-preservation theorem get one case each.
5. **Wire renaming.** `swap_qbit_instr` (`Commute.v:41`) and its property lemma, used by `Insert_Swap`.
6. **DOmega checker** (`StandardValid.v`). `StandardPatternGate` (`:38`) gains `SPG_Cz c t | SPG_Cy | SPG_Ch | SPG_Csx | SPG_Toffoli c1 c2 t | SPG_Cswap c q1 q2 | SPG_Rccx c1 c2 t`; `standard_pattern_gate_to_instruction_pattern` (`:60`), `standard_pattern_gate_nqubits` (`:128`), the matrix function (`:168`: in-bounds and distinctness checks, then `domega_matrix_<g>`), and the agreement lemmas `complex_of_domega_matrix_<g>` (like `theories/domega/DOmegaMatrix.v:483`). Cheapest route: define each `domega_matrix_<g>` as the product of the gate's qelib1 body in the existing primitives (`domega_matrix_single`, `domega_matrix_cnot`), the way `domega_matrix_swap` is three `domega_matrix_cnot` (`DOmegaMatrix.v:405`); then the agreement lemma composes the existing per-gate lemmas and item 2's body lemma gives exactness for free.
7. **Extraction** (`theories/extract/Extract.v` → `theories/extracted.ml`): regenerate; the OCaml below consumes the new constructors.

### B. Front end, back end, CLI — 강욱

8. **Parser / desugar.** `inline_qelib` (`api.ml:1010`) and `desugar.ml` must leave the seven names as instructions rather than splicing their `GateDecl` bodies; non-qelib declarations keep today's behaviour.
9. **Rule-file decoder** (`unoptimize.ml:26` name table, `:130–143` wire keys): accept the seven names with the explorer's role keys (`control1`, `control2`, `target`, `control`, `q1`, `q2`), reject duplicate wires.
10. **Emit.** `qelib_gate_names` (`sugar.ml:513`) and the stringifiers print the seven by name; `--step 0` canonicalisation must not expand them; OQ3 path (`src/lib/qasm3/sugar.ml`) per the §2 decision for `csx`/`rccx`.
11. **CLI.** `--unoptimize-rules` site enumeration, `--rule` + `--qbits` addressing for three-wire gates, `--json`, the capability probes (`scripts/triage/fuzz03_capability_probes.py`), one-rule dispatch unchanged.
12. **Tests.** Parse→emit round trip on programs with named composites; `--step 0` is the identity on those gates; the explorer's plain-format catalogs load and are admitted; v1-vs-v2 semantic agreement on a corpus sample (the bench oracle at n ≤ 4, TV = 0).

## 4. Acceptance (what the bench checks before adopting v2)

1. Round trip: the 20 names survive parse → `--step 0` → emit unchanged (modulo canonical spacing).
2. Admission: `--qubits 2|3 --gates qelib --max-length 4 --format qasminfer` catalogs are admitted entirely (10,716 and 158,077 rules; the primitives catalogs 2,271 and 4,336 stay alongside, since qelib mode lists only relations with at least one composite letter).
3. Conservativity: for a sample of v1 corpus programs, v1 and v2 `--step 0` outputs are oracle-equivalent; every rule of the v1 expanded catalogs has an admitted v2 counterpart.
4. Built-ins: `Insert_Swap` remaps composite wires; `Insert_I`, `Insert_Cnot_Cnot`, `Double_Reset`, the conditional built-ins unaffected.
5. Performance: parse/emit no slower than today on composite-heavy inputs; one-time admission of the 158k 3-wire catalog measured and recorded.

## 5. Bench follow-ups once v2 lands (not now)

- **D16 cost.** Keep the base cost `(ast_size, gate_count, n_2q)` on the expanded normalised copy (`src/qasm_opt_bench/measurement.py:253`, `d16_cost_vector`; `n_2q` recurses into bodies at `:174`) so v1 and v2 statistics stay comparable; a "named" cost view can be added as a component. Decision for 강욱.
- **Catalog pins.** The plain-format q2/q3 qelib catalogs replace `rules-q2-composite-m4.json` (expanded) and the family file; `scripts/catalog/gen_self_inverse_family.py` retires; task-63's in-repo provenance layout is reused as is.
- **Sampling.** The applicable-unit scan over ~170 k short rules needs an index by leading gate; the family taxonomy gains a `q3c` bucket with its own weight.
- **Corpora.** Suite v2 = the same seeds (seeds are engine-independent), traces regenerated on v2, new byte-identity anchors, campaigns re-run for v2 numbers. Suite v1 and the paper's campaign numbers stay on v1 and say so.
- **Ledger.** C, G, I become rung-reachable in one step (`I → ccx ccx`, `I → cswap cswap`); A is unaffected.

## 6. Effort and sequencing (estimate; 유진 corrects)

Seven constructors × (semantics + validity + pattern + the five proof files) with an existing template (`SwapInstr`); the DOmega agreement lemmas are the heaviest part, cheapest as body products. OCaml: parser, decoder, emit, OQ3, CLI tests. Recommendation: all seven gates in one branch (same pattern each), three-wire gates not split off. Timeline: independent of the paper; adoption after 2026-11-13 unless 유진 says it is quicker. Owners: 유진 (A), 강욱 (B); the bench orchestrator supplies test corpora, the explorer catalogs in plain form, and the acceptance scripts on request.

## 7. Open questions for 유진

1. Representation (a) per-gate constructors or (b) one composite constructor.
2. DOmega matrices defined directly or as body products.
3. OQ3 emission for `csx` and `rccx`.
4. Whether `swap` stays as it is (recommended: yes).
5. Whether a v3 with `rc3x c3x c3sqrtx c4x` is worth planning now.
6. Timeline.


## 8. Implementation and validation

Implemented 2026-10-22. The representation is seven constructors (`CzInstr`,
`CyInstr`, `ChInstr`, `CsxInstr`, `ToffoliInstr`, `CswapInstr`, `RccxInstr`), with
corresponding pattern and standard-checker constructors. `swap` keeps its
existing representation. Parametric gates, user macros and the four/five-wire
composites retain macro expansion; there is no v3 change in this implementation.

### Semantics and proofs

`theories/operator/Qelib.v` records the seven canonical qelib1 bodies in execution
order and defines `mat_<gate>` as their matrix products. It also proves unitarity,
swap conjugation and extension to larger registers. The single-gate H/X matrix
facts now live there so the instruction semantics do not depend on the checker.

`Matrix_of_qelib_body` and the seven `Execute_<gate>_qelib_body` theorems in
`theories/program/Standard.v` establish the conservative extension: the new
instruction and the old expanded body induce equal state transformers. This
statement deliberately respects the existing SU(2) representation of `U`:
individual old rotation matrices may differ from canonical qelib1 matrices by
a global phase, which disappears in the density-matrix semantics. The canonical
body matrix itself equals `mat_<gate>` exactly.

`theories/domega/StandardValid.v` defines DOmega body products and proves
`complex_of_domega_matrix_<gate>` by composing primitive agreement lemmas.
For valid two/three-wire placements, closed body products are computed with
`Eval vm_compute`; `domega_matrix_<gate>_qelib_body` proves that each cached path
and the arbitrary-width fallback equal the original product. These are ordinary
kernel-checked definitions and proofs. No axioms or admitted obligations were
introduced.

The instruction/pattern inductions, boolean well-formedness specifications,
matching and substitution proofs, binding invariants, semantic rewrite theorem,
wire renaming and extraction all include the seven cases. New composite wires
must be distinct and in bounds. Existing `cx`/`swap` treatment of equal indices
is unchanged.

### Front ends and addressing

Only library declarations introduced from an include receive the internal native
marker. A user macro with the same name and a different body still expands.
Calls within macros, register broadcasting, and guarded calls preserve native
instructions once their wire arguments are instantiated.

OpenQASM 2 emits all seven names through `qelib1.inc`. OpenQASM 3 emits `cz cy ch
ccx cswap` through `stdgates.inc`; it supplies local declarations for `csx` and
`rccx` only when used. The reader recognizes precisely these canonical local
bodies, including on guarded uses, so its own output remains a fixed point.
Other user-declared bodies continue to expand.

JSON wire fields are the explorer's role keys from §1. Duplicate composite wires
are rejected even when the rule would otherwise be skipped for exceeding the
program width. For loaded rules, `--qbits` assigns actual wires to distinct
pattern-variable numbers in ascending order; `--occurrence` counts only matches
with that assignment. The original admitted rule and extracted application
function perform the rewrite. Listing and JSON output retain the existing schema.

Large catalog decoding is tail recursive and duplicate-name checking uses a hash
table, avoiding the previous quadratic scan.

### Validation results

Environment: Rocq 9.1.0, stdlib 9.0.0, proof Dune 3.23.1, consumer Dune 3.24.2,
OCaml 5.2.1. The v1 comparison executable is from engine commit
`22caa1de6e8b03acd4781d27a033d01bf5fee316`. Tests used explorer commit
`c2a66ed0fd24c76cccdb32759696731446f4df7c` and the benchmark checkout at
`382ab75e380aa07fc38f3f7088d32ac121a05e65`; neither checkout was modified.

- `dune build --root theories @proofs` and `@check-extraction`: passed.
- Consumer `dune build`, `dune build @install`, and `dune runtest`: passed.
- All 20 names remain atomic on `--step 0`. Tests cover both dialects, native
  declaration provenance, broadcasting, arity/bounds errors, rule JSON decoding,
  duplicate wires, three-wire manual addressing, JSON listing, swap remapping,
  conditional rewriting, and exact admission against independent literal bodies.
- `csx;csx = I` and `rccx = ccx` are correctly rejected.
- All role permutations on three wires: 84 dialect round trips, 42 comparisons
  in entangled four-wire contexts against v1; maximum TV difference
  `2.723515857283587e-16` (floating-point execution, tolerance `1e-12`).
- Twenty existing measured v1 seeds at width ≤4: TV exactly 0 for every pair of
  v1/v2 step-0 outputs. The sample is the first twenty lexicographically sorted
  `data/t1/seeds/*.qasm` files with `0 < sum(qreg sizes) <= 4` and
  `0 < sum(creg sizes) <= 4` at the benchmark pin above.
- Native counterparts of all 10,716 two-wire and 158,077 three-wire expanded
  composite rules: admitted. With cached body products, one-time CLI admission
  took **0.78 s** and **81.41 s**, respectively. Three-wire peak RSS was
  1,232,196 KiB. Before caching, the three-wire load took 511.00 s.
- Existing primitive catalogs: all 2,271 and 4,336 rules admitted (0.16 s and
  1.48 s in the initial run).
- Composite-heavy parse/emit (3,000 repetitions of the seven names, 21,000 input
  gates, three runs): median **0.836 s v1 → 0.063 s v2**. Output size falls from
  2,040,047 to 360,047 bytes because gates remain named. These are local wall-time
  measurements, not portable performance guarantees.

### Correction to the plain-catalog assumption

The original proposal's claim that `qasminfer` and `qasminfer-expanded` have the
same rule selection/count is false at the pinned explorer revision. For the
stated context-basis/growing search, raw `--format qasminfer` emits **17,588**
(two-wire) and **399,333** (three-wire) rules. It does not perform the expanded
exporter's wire-padding, filtering and wire-renaming deduplication. Respectively
**14** and **378** entries reference RHS wires absent from their LHS, for example
`S1_to_S0_S1_SDG0`. Unmodified plain files therefore cannot be admitted wholesale
under the existing binding contract. The checker continues to reject those
entries; accepting unbound patterns silently would not produce usable rules.

The 10,716/158,077 acceptance fixtures retain the expanded exporter's exact
selection, direction and identity padding, replacing each encoded gate word
with its native names. `scripts/name_expanded_catalog.py` performs this fixture
conversion; every resulting relation is then checked by the exact engine. The
fixture SHA-256 values (compact JSON) are:

| Fixture | Rules | SHA-256 |
| --- | ---: | --- |
| q2 named | 10,716 | `04abdef04440aa462c5f72c9f1eafe1b9465b3b89ceb4a8843a14d299b1d75d2` |
| q3 named | 158,077 | `dec057301d4f0e8eb022f75fb5b8afc3bff07fee6c9adc27a86519b1fd4aea4e` |

To reproduce after generating the expanded catalogs with the pinned explorer:

```sh
python scripts/name_expanded_catalog.py q2-expanded.json q2-named.json
python scripts/name_expanded_catalog.py q3-expanded.json q3-named.json
python scripts/check_vocabulary_v2.py --v1 /path/to/v1/qasminfer \
  --catalog q2-named.json --catalog q3-named.json \
  --corpus /path/to/v1/sample.qasm
```

The engine implementation is complete. Making the explorer's raw plain exporter
satisfy this binding contract and replacing the benchmark's pinned files remain
upstream/benchmark follow-ups; suite v1 and its artifacts were not changed.
