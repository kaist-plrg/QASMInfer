The CLI classifies every failure it can reach.  Exit 2 is reserved for
argument-shape problems detected before any work starts; every domain failure
exits 1 and prints a single stderr line of the form
"qasminfer: <class>: <detail>".  No invocation may escape with an uncaught
exception, and no failing invocation may create a DESTINATION.

  $ cat > ok.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[2];
  > creg c[2];
  > x q[0];
  > EOF

Argument-shape errors keep exit 2.

  $ qasminfer --unoptimize ok.qasm >shape-arity.stdout 2>shape-arity.stderr
  [2]
  $ test ! -s shape-arity.stdout
  $ head -n 1 shape-arity.stderr
  --unoptimize expects exactly two positional arguments: SOURCE DESTINATION

  $ qasminfer --not-an-option ok.qasm >shape-flag.stdout 2>shape-flag.stderr
  [2]
  $ test ! -s shape-flag.stdout
  $ head -n 1 shape-flag.stderr
  qasminfer: unknown option '--not-an-option'.

  $ qasminfer --rule Insert_I --qbits nope --unoptimize ok.qasm shape-value.qasm >shape-value.stdout 2>shape-value.stderr
  [2]
  $ test ! -e shape-value.qasm
  $ head -n 1 shape-value.stderr
  qasminfer: --qbits expects comma-separated non-negative integers.

An unreadable SOURCE is a domain error, not a crash.

  $ qasminfer --unoptimize no-such-file.qasm io-missing.qasm >io-missing.stdout 2>io-missing.stderr
  [1]
  $ test ! -e io-missing.qasm
  $ test ! -s io-missing.stdout
  $ cat io-missing.stderr
  qasminfer: io: no-such-file.qasm: No such file or directory

  $ qasminfer no-such-file.qasm >io-exec.stdout 2>io-exec.stderr
  [1]
  $ test ! -s io-exec.stdout
  $ cat io-exec.stderr
  qasminfer: io: no-such-file.qasm: No such file or directory

An undeclared QASM version and a lexical failure are both parse errors.

  $ printf 'qreg q[1];\n' > no-version.qasm
  $ qasminfer --unoptimize no-version.qasm parse-version.qasm >parse-version.stdout 2>parse-version.stderr
  [1]
  $ test ! -e parse-version.qasm
  $ cat parse-version.stderr
  qasminfer: parse: Unsupported QASM version: qreg q[1];

  $ printf 'OPENQASM 2.0;\nqreg q[1];\n@\n' > lex.qasm
  $ qasminfer --unoptimize lex.qasm parse-lex.qasm >parse-lex.stdout 2>parse-lex.stderr
  [1]
  $ test ! -e parse-lex.qasm
  $ cat parse-lex.stderr
  qasminfer: parse: lex.qasm:3:1: Unexpected char: @

Rule-file problems are reported under their own class.

  $ qasminfer --rule-file no-such-rules.json --unoptimize-rules ok.qasm >rf-missing.stdout 2>rf-missing.stderr
  [1]
  $ test ! -s rf-missing.stdout
  $ cat rf-missing.stderr
  qasminfer: rule-file: no-such-rules.json: no-such-rules.json: No such file or directory

  $ printf '[{"name":"bad","lhs":[{"gate":"h","q":0}],"rhs":[{"gate":"id","q":0}]}]\n' > bad-rules.json
  $ qasminfer --rule-file bad-rules.json --unoptimize-rules ok.qasm >rf-invalid.stdout 2>rf-invalid.stderr
  [1]
  $ test ! -s rf-invalid.stdout
  $ cat rf-invalid.stderr
  qasminfer: rule-file: bad-rules.json: rule #1 bad (h 0 -> id 0) is not valid up to global omega phase

Rule selection problems share the "rule" class.

  $ qasminfer --rule No_Such_Rule --unoptimize ok.qasm rule-unknown.qasm >rule-unknown.stdout 2>rule-unknown.stderr
  [1]
  $ test ! -e rule-unknown.qasm
  $ cat rule-unknown.stderr
  qasminfer: rule: No transformation rule named 'No_Such_Rule'.

  $ printf '[{"name":"I_to_XX","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"x","q":0},{"gate":"x","q":0}]}]\n' > id-rules.json
  $ qasminfer --rule-file id-rules.json --rule I_to_XX --unoptimize ok.qasm rule-inapplicable.qasm >rule-inapplicable.stdout 2>rule-inapplicable.stderr
  [1]
  $ test ! -e rule-inapplicable.qasm
  $ cat rule-inapplicable.stderr
  qasminfer: rule: Transformation rule 'I_to_XX' is not applicable to the current instruction.

  $ printf '[{"name":"dup","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"x","q":0},{"gate":"x","q":0}]},{"name":"dup","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"y","q":0},{"gate":"y","q":0}]}]\n' > dup-rules.json
  $ qasminfer --rule-file dup-rules.json --rule Insert_I --unoptimize ok.qasm rule-dup.qasm >rule-dup.stdout 2>rule-dup.stderr
  [1]
  $ test ! -e rule-dup.qasm
  $ cat rule-dup.stderr
  qasminfer: rule: Duplicate transformation rule name 'dup'.

Parameter problems share the "param" class.

  $ qasminfer --rule Insert_I --qbits 0,1 --unoptimize ok.qasm param-arity.qasm >param-arity.stdout 2>param-arity.stderr
  [1]
  $ test ! -e param-arity.qasm
  $ cat param-arity.stderr
  qasminfer: param: --qbits expects 1 value(s), but got 2.

  $ qasminfer --rule Insert_If_FT --cbits 9 --unoptimize ok.qasm param-range.qasm >param-range.stdout 2>param-range.stderr
  [1]
  $ test ! -e param-range.qasm
  $ cat param-range.stderr
  qasminfer: param: Manual cbit 9 is out of range for 2 cbit(s).

  $ qasminfer --rule Insert_I --qbits 9 --unoptimize ok.qasm param-invalid.qasm >param-invalid.stdout 2>param-invalid.stderr
  [1]
  $ test ! -e param-invalid.qasm
  $ cat param-invalid.stderr
  qasminfer: param: Manual parameters are invalid for rule 'Insert_I'.

An out-of-range occurrence has its own class.

  $ qasminfer --rule Insert_I --qbits 0 --occurrence 99 --unoptimize ok.qasm occ.qasm >occ.stdout 2>occ.stderr
  [1]
  $ test ! -e occ.qasm
  $ cat occ.stderr
  qasminfer: occurrence: Occurrence 99 is out of range for rule 'Insert_I' with 1 occurrence(s).

A destination that cannot be written is an io error, not a crash.

  $ mkdir -p locked
  $ chmod a-w locked
  $ qasminfer --step 0 --unoptimize ok.qasm locked/out.qasm >io-write.stdout 2>io-write.stderr
  [1]
  $ test ! -e locked/out.qasm
  $ test ! -s io-write.stdout
  $ grep -c '^qasminfer: io: locked/out.qasm: ' io-write.stderr
  1
  $ chmod u+w locked

With --json, a domain error is also reported as a structured object on stdout.

  $ qasminfer --json --rule-file bad-rules.json --unoptimize-rules ok.qasm >json-error.stdout 2>json-error.stderr
  [1]
  $ cat json-error.stdout
  {
    "error": {
      "class": "rule-file",
      "message": "bad-rules.json: rule #1 bad (h 0 -> id 0) is not valid up to global omega phase"
    }
  }
  $ cat json-error.stderr
  qasminfer: rule-file: bad-rules.json: rule #1 bad (h 0 -> id 0) is not valid up to global omega phase
