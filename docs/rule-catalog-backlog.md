# Rule catalog backlog: feasibility and design response

Response to item 5 of the unoptimization CLI backlog. That item says to scope the
Rocq lane before implementing, and 5b/5c/5d ask for a design answer rather than
code, so nothing under `theories/` changed. One OCaml-side fix that falls out of
5c did land; it is called out below.

Claims marked **verified** were reproduced against the built CLI. Line-count
estimates come from reading the sources: Rocq is not installed in the
environment this was written in, so no proof was machine-checked.

## How a rule-file rule actually behaves

Four facts drive every recommendation below.

1. **Qubit indices in a rule file are pattern variables, not positions.**
   `standard_pattern_gate_to_instruction_pattern` emits `NatVar` for each index
   (`theories/domega/StandardValid.v:61-71`), so `I_to_XX` rewrites an `id` on
   any qubit, and the indices only express *sharing* between gates.
2. **The lhs must bind every qubit the rhs rewrites.** `RewriteRule_safeb`
   (`theories/rewrite/RewriteFunction.v:601-612`) requires the rhs variables to
   be a subset of the lhs variables. A rule breaking this used to pass the
   DOmega check and then sit silently inert. **Verified**, and now rejected at
   load time.
3. **Rule width is uncapped; only per-gate arity is capped at two.**
   `standard_rule_nqubits` takes a max over the rule's own indices and the only
   width constraint is against the circuit's qubit count
   (`StandardValid.v:152-157`, `:211-216`).
4. **The front ends macro-expand `cz`, `cy`, `ch`, `ccx`, and `cswap` into
   `u3`/`cx` before anything reaches the Rocq IR** (`src/lib/qasm2/api.ml`
   qelib1/stdgates declarations). Only `swap` is special-cased to survive as a
   primitive (`src/lib/qasm2/desugar.ml:206-207`). So a rule written over the
   expansion is exactly what matches real programs.

Validity is checked up to a global phase from the eight 8th roots of unity
(`theories/domega/DOmega.v:620-622`). That is the checker's hard boundary and it
is unaffected by anything below.

## 5a — Alphabet extension: recommend not doing it as specified

**Every catalog entry item 5a wants to unlock is authorable today, with no
QASMInfer change at all.** Because of fact 4, `cz` *is* `h;cx;h` by the time the
checker sees it, and because of fact 3 a three-qubit rule is already fine.

Verified against the built CLI, all accepted by the DOmega checker and all
firing:

| entry | shape | result |
| --- | --- | --- |
| `cz;cz` | `lhs: id q0, id q1` → 6-gate rhs over `{h,cx}` | validates, 1 occurrence |
| `cy` decomposition | rhs over `{sdg,cx,s}` | validates |
| `cz = h;cx;h` | 3-gate lhs and rhs | validates, 2 occurrences |
| `ccx;ccx` | `lhs: id q0, id q1, id q2` → 30-gate rhs | validates, 1 occurrence |

The one trap, which cost a false negative during this investigation, is fact 2:
`lhs: [id q0]` with a two- or three-qubit rhs validates and then never fires.
That is now a load-time error naming the offending qubit.

If what is wanted is the *authoring convenience* of writing
`{"gate": "cz", "control": 0, "target": 1}` instead of the expansion, there are
two designs with very different price tags.

**(A) Expand in the OCaml decoder. Recommended.** `pattern_gate_of_json`
(`src/lib/unoptimize/unoptimize.ml:100-141`) gains five arms returning a
`standardPatternGate list`, and `pattern_gate_list_field` becomes a concat-map.
Roughly 90-130 lines in one file. No Rocq change, no extraction refresh, no
proof work; nothing else in `src/` or `test/` mentions the `SPG_`/`Std_`
constructors. `string_of_pattern_gate` should keep printing the source token so
a `ccx` diagnostic does not spell out fifteen gates.

The honest caveat: under (A) a `ccx` lhs is a 15-17 pattern literal run and
matches *that expansion*, not "any `ccx`".

**(B) Add primitive `SPG_CZ`/`SPG_CCX`/... constructors.** Per two-qubit gate
this is about 95 lines in `StandardValid.v` (8 definition arms plus 6 proof
branches modelled on the `SPG_Cnot` ones) on top of a one-off ~34-line
generalisation of `complex_of_domega_matrix_cnot` into a U-generic version,
which is cheap because `domega_matrix_ctrl_single` is already generic in U.

That is not the real cost. The core IR has no controlled-U and no three-qubit
instruction, so primitives force new `Instruction` and `InstructionPattern`
constructors cascading through `Program.v`, `RewriteFunction.v`, `Commute.v`,
`Equiv.v`, and `Standard.v`, plus desugar/sugar/stringifier cases mirroring the
`swap` special case. `ccx` and `cswap` additionally need arity-3 matrix
machinery built from scratch — a `mat_ctrl_ctrl_single` with unitary, Hermitian,
`_id`, `_eq`, `_out_of_bounds`, and `_extend_right` analogues mirroring a
335-line block of `operator/Multiple.v`, plus a DOmega counterpart. Call it
150-200 lines per two-qubit gate across seven files, and a ~380-line one-off
plus ~200 lines per three-qubit gate.

And (B) is self-defeating unless the front-end macro expansion is *also* turned
off: while `cz` expands to `h;cx;h` on the way in, a primitive `SPG_CZ` pattern
would never match a real program.

**Recommendation.** Author the six entries as ordinary rule files now. Take (A)
only if authoring ergonomics justify it. Take (B) only if a semantic "any `ccx`"
matcher is genuinely required, and budget the front-end change with it.

## 5b — Parametric rotation pairs: feasible, but check the premise first

Two findings come before the design.

- **Pi-rational pairs already work.** `rz(pi/2);rz(-pi/2)` is matched by a plain
  `s;sdg -> id` rule today. The parametric work buys only non-pi-rational or
  symbolic angles.
- **Non-pi-rational angles are blocked deeper than the parameter kind.**
  `Angle_eqb` returns `false` on any `RealAngle`, even against a syntactically
  identical one (`theories/program/Program.v:49-53`). A `RealAngle` rotation in
  a source program therefore cannot be matched by a structural rotation pattern
  at all. Fixing that is a separate prerequisite, not part of adding a
  parameter kind.

Given that, the two designs are:

**Cheap: a parameter-supplied angle on an insertion rule.** `PRotate` already
carries three concrete `Angle` values (`RewriteFunction.v:294`), so
`rule_rhs := [PRotate A0 A0 theta (NatExact q); PRotate A0 A0 (neg theta) (NatExact q)]`
with `rule_lhs := []` is well-typed today — it is exactly the shape of the
already-proved `Rule_Insert_Cnot_Cnot`. Cost: two constructors in
`rewrite/Spec.v` (`ParamKind_angle`, `Param_angle`), one `TransformSpec`, one
validity lemma, a regenerated `theories/extracted.ml`, four exhaustive
param-kind matches in `unoptimize.ml`, and an angle parser in `main.ml` (the
existing `--qbits` parser is integer-only). `RewriteFunction.v` and `Validity.v`
do not change.

The validity lemma is close to free for `rz`: `Transform_P_P`
(`theories/transform/Transform.v:117-131`) is already quantified over real
angles and is exactly the composition lemma needed, because `rz(theta)`
desugars to `u1(theta) = U(0,0,theta) = Gate_P theta`. Angle negation needs no
new Rocq facility — the rational angle arithmetic already exists OCaml-side
(`q_neg`, `q_add`, `q_sub` in `src/lib/qasm2/desugar.ml`).

**Expensive: an angle pattern variable.** This is what a rule-file-authored
parametric rule needs, and what *rewriting* an existing `rz(theta);rz(-theta)`
pair needs. It requires a new `AnglePattern` type, a signature change to
`PRotate`, a fourth map in `PatternMap` (`RewriteFunction.v:78-82`), new cases
in the match/inst/`*_vars` fixpoints and `RewriteRule_safe(b)`, and re-proof
across the `PatternMap` sites in `Validity.v`. An order of magnitude more.

**Recommendation.** Take the cheap design. For unoptimization the operation
wanted is *inserting* a cancelling pair at an empty site, which the cheap design
covers; matching an existing pair is the expensive design and is additionally
blocked by `Angle_eqb`.

**Effort ordering: `rz` < `ry` < `rx`.** Grouping `rz` with `rx` understates
`rx`. `rz` is nearly free via `Transform_P_P`. `ry = mat_rot theta 0 0` needs one
genuinely new cos/sin addition lemma — `operator/Single.v` has only zero-angle
and unitarity facts, with no `mat_rot_y` product lemma. `rx = mat_rot theta
(-pi/2) (pi/2)` needs that same trigonometric content plus z-conjugation
cancellation.

## 5c — Empty-LHS entries: bless the two-step composition

An empty `lhs` is *not* structurally rejected — it is the established insertion
idiom and four shipped built-ins use it (`rewrite/ManualSpec.v:27-75`), and the
DOmega checker passes it because an empty gate sequence is the identity matrix.
The blocker is fact 2: `standard_rewrite_rule` emits `NatVar` for every qubit, so
an empty lhs binds nothing, `RewriteRule_safeb` is false, and `RewriteRule_apply`
short-circuits to `None`. **Verified**: such a rule loaded with exit 0, never
appeared in `--unoptimize-rules`, and `--rule` on it reported "not applicable" —
with nothing pointing at the rule as the cause.

Supporting empty-lhs rule-file entries properly is **both** a Rocq and an OCaml
change: the Rocq side needs a `NatExact`-emitting variant of
`standard_rewrite_rule` with its own soundness proof, and the OCaml side needs a
way to mark indices literal, plus an extraction refresh.

**Recommendation: bless `Insert_I` then `I_to_XX`.** It works today —
**verified** end to end: `Insert_I` emits `RotateInstr A0 A0 A0 q`, which
`I_to_XX`'s `PRotate A0 A0 A0 (NatVar 0)` matches, producing `x q[0]; x q[0];`.

Two things landed or are offered around it:

- **Landed this pass:** the silent case is now a load-time error naming the
  offending qubit, so an author who tries `lhs: []` is told why rather than
  shipping a dead rule.
- **Offered, not implemented:** the composition needs two CLI invocations,
  because `--rule` cannot be combined with `--step`. If that is friction for the
  benchmark, a `--rule A --rule B` chain applying named rules in order is an
  OCaml-only change with no proof impact. Say the word and it can land in the
  same lane as items 1-4.

## 5d — Scope decisions

**`cy;cy`: in.** It is not structurally different from `cz;cz` and the marginal
cost is zero. Neither is a kernel primitive; both are qelib1 macros expanding to
six gates over `{h, s, sdg, cx}`, all already in the rule-file grammar. Both
were authored and **verified** firing during this investigation. Whatever fact 2
costs `cz`, it costs `cy` identically.

**`ry(theta);ry(-theta)`: out of the first cut.** Unlike `cy` it *is* materially
different from the already-listed cases, per the `rz < ry < rx` ordering above:
it needs a new trigonometric addition lemma that does not exist anywhere in
`operator/Single.v`. If 5b proceeds, do `rz` first as a pilot — it is nearly free
— and decide on `ry` and `rx` once the pilot has shown what the parameter-kind
plumbing actually costs. Both should be in only if the benchmark needs
non-pi-rational angles at all, which is the premise question at the top of 5b.

## Environment note

Rocq is not installed in this environment (`which rocq coqc` finds nothing, and
no switch has `rocq-core`), so `dune build --root theories @proofs`, `@extract`,
and `@check-extraction` cannot run here. Nothing under `theories/` was modified,
so `theories/extracted.ml` remains in sync with its recorded source commit and
the CI extraction gate is unaffected.

Implementing any of the above that touches `theories/` needs a dedicated proof
switch: `rocq-core` 9.1.0 requires Dune earlier than 3.24, while the consumer
build now requires 3.24 or newer.
