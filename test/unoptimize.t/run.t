QASM2 and QASM3 conversion is quiet, emits reparsable canonical QASM2, and is
stable when applied a second time.  The three invocations also cover the mode
option before, between, and after the two positional paths.

  $ qasminfer --step 0 --unoptimize qasm2.qasm qasm2.once.qasm >qasm2.stdout 2>qasm2.stderr
  $ test ! -s qasm2.stdout
  $ test ! -s qasm2.stderr
  $ head -n 1 qasm2.once.qasm
  OPENQASM 2.0;
  $ qasminfer --step 0 --unopt qasm2.qasm qasm2.alias.qasm >qasm2-alias.stdout 2>qasm2-alias.stderr
  $ test ! -s qasm2-alias.stdout
  $ test ! -s qasm2-alias.stderr
  $ cmp qasm2.once.qasm qasm2.alias.qasm
  $ qasminfer qasm2.once.qasm --step 0 --unoptimize qasm2.twice.qasm >qasm2-twice.stdout 2>qasm2-twice.stderr
  $ test ! -s qasm2-twice.stdout
  $ test ! -s qasm2-twice.stderr
  $ cmp qasm2.once.qasm qasm2.twice.qasm
  $ cp qasm2.qasm qasm2.in-place.qasm
  $ chmod u+w qasm2.in-place.qasm
  $ qasminfer --step 0 --unoptimize qasm2.in-place.qasm qasm2.in-place.qasm >in-place.stdout 2>in-place.stderr
  $ test ! -s in-place.stdout
  $ test ! -s in-place.stderr
  $ cmp qasm2.once.qasm qasm2.in-place.qasm

Rule files are validated before unoptimization and then added to the extracted
transform spec list.

  $ printf '[{"name":"I_to_XX_from_file","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"x","q":0},{"gate":"x","q":0}]}]\n' > valid-rules.json
  $ qasminfer --rule-file valid-rules.json --step 0 --unoptimize qasm2.qasm qasm2.rules.qasm >rules.stdout 2>rules.stderr
  $ test ! -s rules.stdout
  $ test ! -s rules.stderr
  $ cmp qasm2.once.qasm qasm2.rules.qasm

  $ printf '[{"name":"Cnot3_file_to_Swap","lhs":[{"gate":"cx","control":0,"target":1},{"gate":"cx","control":1,"target":0},{"gate":"cx","control":0,"target":1}],"rhs":[{"gate":"swap","q1":0,"q2":1}]}]\n' > valid-multi-rules.json
  $ cat > applicable-swap.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[2];
  > cx q[0],q[1];
  > cx q[1],q[0];
  > cx q[0],q[1];
  > EOF
  $ qasminfer --rule-file valid-multi-rules.json --unoptimize-rules applicable-swap.qasm | grep -F 'Cnot3_file_to_Swap'
  Cnot3_file_to_Swap: occurrences=1 param=none

The --unoptimize-rules command reports the applicable rule summaries without
performing a rewrite.  Counts are lhs occurrences, and params are reported by
kind rather than by concrete witness values.

  $ qasminfer --unoptimize-rules qasm2.qasm >applicable-rules.stdout 2>applicable-rules.stderr
  $ test ! -s applicable-rules.stderr
  $ cat applicable-rules.stdout
  Insert_I: occurrences=12 param=qbit1
  Insert_Swap: occurrences=9 param=qbit2
  Insert_Cnot_Cnot: occurrences=12 param=qbit2
  Insert_If_FT: occurrences=12 param=cbit_instr
  Insert_If_TF: occurrences=12 param=cbit_instr
  Double_If_False: occurrences=1 param=none
  Double_Reset: occurrences=1 param=none
  $ grep -F 'Swap_To_3Cnot' applicable-rules.stdout; test $? -ne 0
  $ qasminfer --unoptimize-rules qasm2.qasm --output applicable-rules.file >applicable-rules-file.stdout 2>applicable-rules-file.stderr
  $ test ! -s applicable-rules-file.stdout
  $ test ! -s applicable-rules-file.stderr
  $ cmp applicable-rules.stdout applicable-rules.file

  $ cat > applicable-id.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[1];
  > id q[0];
  > EOF
  $ qasminfer --rule-file valid-rules.json --unoptimize-rules applicable-id.qasm | grep -F 'I_to_XX_from_file'
  I_to_XX_from_file: occurrences=1 param=none

  $ printf '[{"name":"Too_wide_rule","lhs":[{"gate":"id","q":1}],"rhs":[{"gate":"x","q":1},{"gate":"x","q":1}]}]\n' > too-wide-rules.json
  $ qasminfer --rule-file too-wide-rules.json --unoptimize-rules applicable-id.qasm >too-wide-rules.stdout 2>too-wide-rules.stderr
  $ test ! -s too-wide-rules.stderr
  $ grep -F 'Too_wide_rule' too-wide-rules.stdout; test $? -ne 0
  $ qasminfer --rule-file too-wide-rules.json --rule Too_wide_rule --unoptimize applicable-id.qasm too-wide-output.qasm >too-wide-rule.stdout 2>too-wide-rule.stderr
  [1]
  $ test ! -e too-wide-output.qasm
  $ test ! -s too-wide-rule.stdout
  $ cat too-wide-rule.stderr
  qasminfer: No transformation rule named 'Too_wide_rule'.

  $ qasminfer --json --unoptimize-rules qasm2.qasm >applicable-rules.json 2>applicable-rules-json.stderr
  $ test ! -s applicable-rules-json.stderr
  $ cat applicable-rules.json
  {
    "source": "qasm2.qasm",
    "qubits": 3,
    "clbits": 3,
    "rules": [
      {
        "name": "Insert_I",
        "occurrences": 12,
        "param": "qbit1"
      },
      {
        "name": "Insert_Swap",
        "occurrences": 9,
        "param": "qbit2"
      },
      {
        "name": "Insert_Cnot_Cnot",
        "occurrences": 12,
        "param": "qbit2"
      },
      {
        "name": "Insert_If_FT",
        "occurrences": 12,
        "param": "cbit_instr"
      },
      {
        "name": "Insert_If_TF",
        "occurrences": 12,
        "param": "cbit_instr"
      },
      {
        "name": "Double_If_False",
        "occurrences": 1,
        "param": "none"
      },
      {
        "name": "Double_Reset",
        "occurrences": 1,
        "param": "none"
      }
    ]
  }

  $ printf '[{"name":"bad_h_to_i","lhs":[{"gate":"h","q":0}],"rhs":[{"gate":"id","q":0}]}]\n' > invalid-rules.json
  $ qasminfer --rule-file invalid-rules.json --step 0 --unoptimize qasm2.qasm invalid-rule-output.qasm >invalid-rules.stdout 2>invalid-rules.stderr
  [1]
  $ test ! -e invalid-rule-output.qasm
  $ test ! -s invalid-rules.stdout
  $ cat invalid-rules.stderr
  qasminfer: invalid rule file invalid-rules.json: rule #1 bad_h_to_i (h 0 -> id 0) is not valid up to global omega phase

  $ printf '[{"name":"old_syntax","lhs":["id"],"rhs":["x","x"]}]\n' > old-syntax-rules.json
  $ qasminfer --rule-file old-syntax-rules.json --step 0 --unoptimize qasm2.qasm old-syntax-output.qasm >old-syntax.stdout 2>old-syntax.stderr
  [1]
  $ test ! -e old-syntax-output.qasm
  $ test ! -s old-syntax.stdout
  $ cat old-syntax.stderr
  qasminfer: invalid rule file old-syntax-rules.json: rule old_syntax field 'lhs' gate entry must be an object

The --rule option restricts unoptimization to a named rule from the combined
built-in and rule-file transform spec list, and it cannot be combined with
--step.

  $ cat > named-rule-target.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[1];
  > id q[0];
  > EOF
  $ qasminfer --rule-file valid-rules.json --rule I_to_XX_from_file --unoptimize named-rule-target.qasm named-rule-output.qasm >named-rule.stdout 2>named-rule.stderr
  $ test ! -s named-rule.stdout
  $ test ! -s named-rule.stderr
  $ grep -F 'x q[0];' named-rule-output.qasm | wc -l | tr -d ' '
  2

  $ qasminfer --rule-file valid-rules.json --rule I_to_XX_from_file --unoptimize qasm2.qasm no-match-rule-output.qasm >no-match-rule.stdout 2>no-match-rule.stderr
  [1]
  $ test ! -e no-match-rule-output.qasm
  $ test ! -s no-match-rule.stdout
  $ cat no-match-rule.stderr
  qasminfer: Transformation rule 'I_to_XX_from_file' is not applicable to the current instruction.

  $ qasminfer --rule Missing_rule --unoptimize qasm2.qasm missing-rule-output.qasm >missing-rule.stdout 2>missing-rule.stderr
  [1]
  $ test ! -e missing-rule-output.qasm
  $ test ! -s missing-rule.stdout
  $ cat missing-rule.stderr
  qasminfer: No transformation rule named 'Missing_rule'.

  $ printf '[{"name":"dup","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"x","q":0},{"gate":"x","q":0}]},{"name":"dup","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"y","q":0},{"gate":"y","q":0}]}]\n' > duplicate-rules.json
  $ qasminfer --rule-file duplicate-rules.json --rule Insert_I --unoptimize named-rule-target.qasm duplicate-rule-output.qasm >duplicate-rule.stdout 2>duplicate-rule.stderr
  [1]
  $ test ! -e duplicate-rule-output.qasm
  $ test ! -s duplicate-rule.stdout
  $ cat duplicate-rule.stderr
  qasminfer: Duplicate transformation rule name 'dup'.

  $ qasminfer --rule Insert_I --step 1 --unoptimize qasm2.qasm rule-step-conflict.qasm >rule-step-conflict.stdout 2>rule-step-conflict.stderr
  [2]
  $ test ! -e rule-step-conflict.qasm
  $ test ! -s rule-step-conflict.stdout
  $ head -n 1 rule-step-conflict.stderr
  --rule cannot be used with --step

Manual --qbits, --cbits, and --occurrence options fix the numeric part of a
named unoptimization parameter.  They are accepted only with --unoptimize
--rule.

  $ cat > manual-target.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[2];
  > creg c[2];
  > x q[0];
  > x q[1];
  > EOF

  $ qasminfer --rule Insert_I --qbits 1 --occurrence 0 --unoptimize manual-target.qasm manual-i.qasm >manual-i.stdout 2>manual-i.stderr
  $ test ! -s manual-i.stdout
  $ test ! -s manual-i.stderr
  $ grep -F 'id q[1];' manual-i.qasm
  id q[1];

  $ qasminfer --rule Insert_Swap --qbits 0,1 --occurrence 0 --unoptimize manual-target.qasm manual-swap.qasm >manual-swap.stdout 2>manual-swap.stderr
  $ test ! -s manual-swap.stdout
  $ test ! -s manual-swap.stderr
  $ grep -F 'swap q[0],q[1];' manual-swap.qasm
  swap q[0],q[1];

  $ qasminfer --rule Insert_Cnot_Cnot --qbits 0,1 --occurrence 0 --unoptimize manual-target.qasm manual-cnot.qasm >manual-cnot.stdout 2>manual-cnot.stderr
  $ test ! -s manual-cnot.stdout
  $ test ! -s manual-cnot.stderr
  $ grep -F 'CX q[0],q[1];' manual-cnot.qasm | wc -l | tr -d ' '
  2

  $ qasminfer --rule Insert_I --qbits 0 --occurrence 99 --unoptimize manual-target.qasm manual-occurrence-fail.qasm >manual-occurrence-fail.stdout 2>manual-occurrence-fail.stderr
  [1]
  $ test ! -e manual-occurrence-fail.qasm
  $ test ! -s manual-occurrence-fail.stdout
  $ cat manual-occurrence-fail.stderr
  qasminfer: Occurrence 99 is out of range for rule 'Insert_I' with 2 occurrence(s).

  $ qasminfer --rule Insert_I --qbits 0,1 --unoptimize manual-target.qasm manual-arity-fail.qasm >manual-arity-fail.stdout 2>manual-arity-fail.stderr
  [1]
  $ test ! -e manual-arity-fail.qasm
  $ test ! -s manual-arity-fail.stdout
  $ cat manual-arity-fail.stderr
  qasminfer: --qbits expects 1 value(s), but got 2.

  $ qasminfer --rule Insert_I --qbits -1 --unoptimize manual-target.qasm manual-negative-fail.qasm >manual-negative-fail.stdout 2>manual-negative-fail.stderr
  [2]
  $ test ! -e manual-negative-fail.qasm
  $ test ! -s manual-negative-fail.stdout
  $ head -n 1 manual-negative-fail.stderr
  qasminfer: --qbits expects non-negative integers.

  $ qasminfer --rule Insert_I --qbits 0, --unoptimize manual-target.qasm manual-empty-fail.qasm >manual-empty-fail.stdout 2>manual-empty-fail.stderr
  [2]
  $ test ! -e manual-empty-fail.qasm
  $ test ! -s manual-empty-fail.stdout
  $ head -n 1 manual-empty-fail.stderr
  qasminfer: --qbits expects comma-separated non-negative integers.

  $ qasminfer --rule Insert_I --qbits '0 1' --unoptimize manual-target.qasm manual-space-fail.qasm >manual-space-fail.stdout 2>manual-space-fail.stderr
  [2]
  $ test ! -e manual-space-fail.qasm
  $ test ! -s manual-space-fail.stdout
  $ head -n 1 manual-space-fail.stderr
  qasminfer: --qbits expects comma-separated non-negative integers.

  $ qasminfer --rule Insert_I --qbits nope --unoptimize manual-target.qasm manual-non-int-fail.qasm >manual-non-int-fail.stdout 2>manual-non-int-fail.stderr
  [2]
  $ test ! -e manual-non-int-fail.qasm
  $ test ! -s manual-non-int-fail.stdout
  $ head -n 1 manual-non-int-fail.stderr
  qasminfer: --qbits expects comma-separated non-negative integers.

  $ qasminfer --rule Insert_I --qbits 0 --qbits 1 --unoptimize manual-target.qasm manual-duplicate-fail.qasm >manual-duplicate-fail.stdout 2>manual-duplicate-fail.stderr
  [2]
  $ test ! -e manual-duplicate-fail.qasm
  $ test ! -s manual-duplicate-fail.stdout
  $ head -n 1 manual-duplicate-fail.stderr
  qasminfer: --qbits cannot be specified more than once.

  $ qasminfer --qbits 0 --unoptimize manual-target.qasm manual-no-rule-fail.qasm >manual-no-rule-fail.stdout 2>manual-no-rule-fail.stderr
  [2]
  $ test ! -e manual-no-rule-fail.qasm
  $ test ! -s manual-no-rule-fail.stdout
  $ head -n 1 manual-no-rule-fail.stderr
  --qbits, --cbits, and --occurrence require --rule

  $ qasminfer --qbits 0 --unoptimize-rules manual-target.qasm >manual-rules-fail.stdout 2>manual-rules-fail.stderr
  [2]
  $ test ! -s manual-rules-fail.stdout
  $ head -n 1 manual-rules-fail.stderr
  --qbits, --cbits, and --occurrence cannot be used with --unoptimize-rules

  $ qasminfer --json qasm2.qasm >qasm2-source.json 2>qasm2-source.stderr
  $ qasminfer --json qasm2.once.qasm >qasm2-generated.json 2>qasm2-generated.stderr
  $ test ! -s qasm2-source.stderr
  $ test ! -s qasm2-generated.stderr
  $ cmp qasm2-source.json qasm2-generated.json

  $ qasminfer qasm3.qasm qasm3.once.qasm --step 0 --unoptimize >qasm3.stdout 2>qasm3.stderr
  $ test ! -s qasm3.stdout
  $ test ! -s qasm3.stderr
  $ head -n 1 qasm3.once.qasm
  OPENQASM 2.0;
  $ grep -F 'qreg qasm3_physical_1[1];' qasm3.once.qasm
  qreg qasm3_physical_1[1];
  $ grep -F '$' qasm3.once.qasm >/dev/null; test $? -ne 0
  $ qasminfer --step 0 --unoptimize qasm3.once.qasm qasm3.twice.qasm >qasm3-twice.stdout 2>qasm3-twice.stderr
  $ test ! -s qasm3-twice.stdout
  $ test ! -s qasm3-twice.stderr
  $ cmp qasm3.once.qasm qasm3.twice.qasm

Verbose conversion diagnostics stay on stderr and do not contaminate either
stdout or the QASM destination.

  $ qasminfer --step 0 --unoptimize qasm2.qasm verbose.qasm --verbose >verbose.stdout 2>verbose.stderr
  $ test ! -s verbose.stdout
  $ test -s verbose.stderr
  $ cmp qasm2.once.qasm verbose.qasm

Invalid path counts and execution-only output flags fail before creating a
destination.

  $ qasminfer --unoptimize qasm2.qasm >missing.stdout 2>missing.stderr
  [2]
  $ test ! -s missing.stdout
  $ head -n 1 missing.stderr
  --unoptimize expects exactly two positional arguments: SOURCE DESTINATION

  $ qasminfer --unoptimize qasm2.qasm extra.qasm unexpected.qasm >extra.stdout 2>extra.stderr
  [2]
  $ test ! -e extra.qasm
  $ test ! -s extra.stdout
  $ head -n 1 extra.stderr
  --unoptimize expects exactly two positional arguments: SOURCE DESTINATION

  $ qasminfer qasm2.qasm accidental-output.qasm >two-paths.stdout 2>two-paths.stderr
  [2]
  $ test ! -e accidental-output.qasm
  $ test ! -s two-paths.stdout
  $ head -n 1 two-paths.stderr
  execution expects exactly one positional SOURCE

  $ qasminfer --unoptimize qasm2.qasm conflict.qasm --output probabilities.txt >conflict.stdout 2>conflict.stderr
  [2]
  $ test ! -e conflict.qasm
  $ test ! -e probabilities.txt
  $ test ! -s conflict.stdout
  $ head -n 1 conflict.stderr
  --output/-o cannot be used with --unoptimize

  $ qasminfer qasm2.qasm --unoptimize short-conflict.qasm -o probabilities-short.txt >short-conflict.stdout 2>short-conflict.stderr; test $? -ne 0
  $ test ! -e short-conflict.qasm
  $ test ! -e probabilities-short.txt
  $ test ! -s short-conflict.stdout
  $ test -s short-conflict.stderr

  $ qasminfer --json qasm2.qasm --unoptimize json-conflict.qasm >json-conflict.stdout 2>json-conflict.stderr
  [2]
  $ test ! -e json-conflict.qasm
  $ test ! -s json-conflict.stdout
  $ head -n 1 json-conflict.stderr
  --json cannot be used with --unoptimize

No-argument invocation retains its legacy exit status and displays usage.

  $ qasminfer >no-arguments.stdout 2>no-arguments.stderr
  [1]
  $ test ! -s no-arguments.stdout
  $ head -n 1 no-arguments.stderr
  usage: qasminfer [OPTIONS] SOURCE

A conversion failure leaves an existing destination untouched.

  $ printf 'sentinel\n' > protected.qasm
  $ qasminfer --unoptimize conversion_error.qasm protected.qasm >conversion-error.stdout 2>conversion-error.stderr; test $? -ne 0
  $ cat protected.qasm
  sentinel
  $ test ! -s conversion-error.stdout
  $ test -s conversion-error.stderr

Lexical failures in both parsers return a clear diagnostic without creating or
overwriting a destination.

  $ printf 'sentinel\n' > lexical-protected.qasm
  $ qasminfer --unoptimize lexical_error_qasm2.qasm lexical-protected.qasm >lexical-qasm2.stdout 2>lexical-qasm2.stderr
  [1]
  $ cat lexical-protected.qasm
  sentinel
  $ test ! -s lexical-qasm2.stdout
  $ cat lexical-qasm2.stderr
  qasminfer: lexical_error_qasm2.qasm:3:1: Unexpected char: @

  $ qasminfer --unoptimize lexical_error_qasm3.qasm lexical-created.qasm >lexical-qasm3.stdout 2>lexical-qasm3.stderr
  [1]
  $ test ! -e lexical-created.qasm
  $ test ! -s lexical-qasm3.stdout
  $ cat lexical-qasm3.stderr
  qasminfer: lexical_error_qasm3.qasm:3:1: Unexpected char: @

The pre-existing execution interface retains its exact text and JSON output,
file redirection, and verbose stream separation.

  $ qasminfer execution.qasm >execution.stdout 2>execution.stderr
  $ cat execution.stdout
  00 : 5.0000000000000011e-01
  01 : 4.9999999999999989e-01
  10 : 0.0000000000000000e+00
  11 : 0.0000000000000000e+00
  $ test ! -s execution.stderr

  $ qasminfer --json execution.qasm >execution.json 2>json.stderr
  $ cat execution.json
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
  $ test ! -s json.stderr

  $ qasminfer execution.qasm --output execution.file >output.stdout 2>output.stderr
  $ test ! -s output.stdout
  $ test ! -s output.stderr
  $ cmp execution.stdout execution.file

  $ qasminfer --json execution.qasm --output execution-json.file >json-output.stdout 2>json-output.stderr
  $ test ! -s json-output.stdout
  $ test ! -s json-output.stderr
  $ cmp execution.json execution-json.file

  $ qasminfer execution.qasm --verbose >execution-verbose.stdout 2>execution-verbose.stderr
  $ cmp execution.stdout execution-verbose.stdout
  $ grep -F 'QASMCore ========================================' execution-verbose.stderr
  QASMCore ========================================
  $ grep -F 'RESULT ==========================================' execution-verbose.stderr
  RESULT ==========================================
