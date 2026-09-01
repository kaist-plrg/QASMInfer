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

  $ qasminfer --step 1 ok.qasm >shape-step.stdout 2>shape-step.stderr
  [2]
  $ test ! -s shape-step.stdout
  $ head -n 1 shape-step.stderr
  --step can only be used with --unoptimize

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
  qasminfer: rule-file: no-such-rules.json: No such file or directory

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

A rule-file rule whose right-hand side names a qubit its left-hand side does not
bind can never fire: the checker turns every JSON qubit index into a pattern
variable, and RewriteRule_safeb requires the right-hand side's variables to be
bound by the left-hand side.  Such a rule used to load, validate, and then sit
silently inert.

  $ printf '[{"name":"unbound","lhs":[{"gate":"id","q":0}],"rhs":[{"gate":"h","q":1},{"gate":"cx","control":0,"target":1},{"gate":"h","q":1},{"gate":"h","q":1},{"gate":"cx","control":0,"target":1},{"gate":"h","q":1}]}]\n' > unbound-rules.json
  $ qasminfer --rule-file unbound-rules.json --unoptimize-rules ok.qasm >unbound.stdout 2>unbound.stderr
  [1]
  $ test ! -s unbound.stdout
  $ cat unbound.stderr
  qasminfer: rule-file: unbound-rules.json: rule #1 unbound rewrites qubit 1, which its lhs does not bind

An empty lhs is the same failure in its most extreme form: nothing is bound, so
nothing can be rewritten.

  $ printf '[{"name":"empty","lhs":[],"rhs":[{"gate":"x","q":0},{"gate":"x","q":0}]}]\n' > empty-lhs-rules.json
  $ qasminfer --rule-file empty-lhs-rules.json --unoptimize-rules ok.qasm >empty-lhs.stdout 2>empty-lhs.stderr
  [1]
  $ test ! -s empty-lhs.stdout
  $ cat empty-lhs.stderr
  qasminfer: rule-file: empty-lhs-rules.json: rule #1 empty rewrites qubit 0, which its lhs does not bind

A rule whose lhs binds every qubit its rhs rewrites is accepted, including one
that is wider than any built-in.

  $ printf '[{"name":"II_to_CZCZ","lhs":[{"gate":"id","q":0},{"gate":"id","q":1}],"rhs":[{"gate":"h","q":1},{"gate":"cx","control":0,"target":1},{"gate":"h","q":1},{"gate":"h","q":1},{"gate":"cx","control":0,"target":1},{"gate":"h","q":1}]}]\n' > czcz-rules.json
  $ cat > two-ids.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[2];
  > id q[0];
  > id q[1];
  > EOF
  $ qasminfer --rule-file czcz-rules.json --unoptimize-rules two-ids.qasm | grep -F II_to_CZCZ
  II_to_CZCZ: occurrences=1 param=none

Every io diagnostic names the path, even when the underlying system error does
not (opening a directory reports only "Is a directory" on some platforms).

  $ mkdir -p adir
  $ qasminfer --step 0 --unoptimize adir dir-source.qasm >dir-source.stdout 2>dir-source.stderr
  [1]
  $ test ! -e dir-source.qasm
  $ grep -c '^qasminfer: io: adir: ' dir-source.stderr
  1

  $ qasminfer --step 0 --unoptimize ok.qasm adir >dir-dest.stdout 2>dir-dest.stderr
  [1]
  $ grep -c '^qasminfer: io: adir: ' dir-dest.stderr
  1

A diagnostic that quotes the source stays one printable line: the quoted text is
bounded and non-printable bytes are replaced, so a binary file cannot smuggle
control characters or newlines into the error stream.

  $ printf 'not a qasm file at all, and this first line runs on for quite a while\n' > notqasm.qasm
  $ qasminfer --step 0 --unoptimize notqasm.qasm notqasm.out.qasm >notqasm.stdout 2>notqasm.stderr
  [1]
  $ test ! -e notqasm.out.qasm
  $ cat notqasm.stderr
  qasminfer: parse: Unsupported QASM version: not a qasm file at all, and this first line runs on for quit...

  $ printf 'not\346a\377qasm\n' > highbytes.qasm
  $ qasminfer --step 0 --unoptimize highbytes.qasm highbytes.out.qasm >highbytes.stdout 2>highbytes.stderr
  [1]
  $ test ! -e highbytes.out.qasm
  $ cat highbytes.stderr
  qasminfer: parse: Unsupported QASM version: not?a?qasm
  $ LC_ALL=C grep -c '[^ -~]' highbytes.stderr
  0
  [1]

  $ printf 'OPENQASM \001\002\r\n bad\n' > control.qasm
  $ qasminfer --step 0 --unoptimize control.qasm control.out.qasm >control.stdout 2>control.stderr
  [1]
  $ test ! -e control.out.qasm
  $ cat control.stderr
  qasminfer: parse: Unsupported QASM version: OPENQASM ???
  $ wc -l < control.stderr | tr -d ' '
  1

An --instr payload cannot smuggle in a degenerate two-qubit gate.  The --qbits
path already refuses equal operands; the payload is another way the caller asks
this tool to emit a gate, so it is held to the same rule.  (A degenerate gate
already present in SOURCE is still passed through: that is the user's own
program, not something asked for on the command line.)

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'swap q[0],q[0];' ok.qasm degen-swap.qasm >degen-swap.stdout 2>degen-swap.stderr
  [1]
  $ test ! -e degen-swap.qasm
  $ test ! -s degen-swap.stdout
  $ cat degen-swap.stderr
  qasminfer: param: --instr: swap names qubit 0 twice, which OpenQASM does not allow

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'cx q[1],q[1];' ok.qasm degen-cx.qasm >degen-cx.stdout 2>degen-cx.stderr
  [1]
  $ test ! -e degen-cx.qasm
  $ cat degen-cx.stderr
  qasminfer: param: --instr: cx names qubit 1 twice, which OpenQASM does not allow

Calling a gate with the wrong number of arguments is a malformed program, not an
internal failure, and the diagnostic says which gate and what it expected.

  $ printf 'OPENQASM 2.0;\ninclude "qelib1.inc";\nqreg q[2];\ncx q[0];\n' > arity.qasm
  $ qasminfer --step 0 --unoptimize arity.qasm arity.out.qasm >arity.stdout 2>arity.stderr
  [1]
  $ test ! -e arity.out.qasm
  $ cat arity.stderr
  qasminfer: parse: arity.qasm: gate cx expects 2 argument(s) but got 1

  $ printf 'OPENQASM 2.0;\ninclude "qelib1.inc";\nqreg q[1];\nrz(1,2) q[0];\n' > arity2.qasm
  $ qasminfer --step 0 --unoptimize arity2.qasm arity2.out.qasm >arity2.stdout 2>arity2.stderr
  [1]
  $ cat arity2.stderr
  qasminfer: parse: arity2.qasm: gate rz expects 1 parameter(s) but got 2

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'cx q[0];' ok.qasm arity3.qasm >arity3.stdout 2>arity3.stderr
  [1]
  $ test ! -e arity3.qasm
  $ cat arity3.stderr
  qasminfer: param: --instr: gate cx expects 2 argument(s) but got 1

A --instr-file diagnostic names --instr-file, not --instr.

  $ printf 'x q[9];\n' > bad-payload.txt
  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr-file bad-payload.txt ok.qasm from-file.qasm >from-file.stdout 2>from-file.stderr
  [1]
  $ test ! -e from-file.qasm
  $ cat from-file.stderr
  qasminfer: param: --instr-file: U: q[9] is out of range

Both streams stay decodable as UTF-8, whatever bytes the source contains.

  $ printf 'OPENQASM 2.0;\nqreg q[1];\n\351\n' > highbyte.qasm
  $ qasminfer --json --unoptimize-rules highbyte.qasm >hb.stdout 2>hb.stderr
  [1]
  $ cat hb.stderr
  qasminfer: parse: highbyte.qasm:3:1: Unexpected char: ?
  $ cat hb.stdout
  {
    "error": {
      "class": "parse",
      "message": "highbyte.qasm:3:1: Unexpected char: ?"
    }
  }

Selecting a rule twice is an argument error, not a silent last-one-wins.

  $ qasminfer --unoptimize --rule Insert_Swap --rule Insert_I ok.qasm dup-rule.qasm >dup-rule.stdout 2>dup-rule.stderr
  [2]
  $ test ! -e dup-rule.qasm
  $ head -n 1 dup-rule.stderr
  qasminfer: --rule cannot be specified more than once.

  $ qasminfer --rule-file id-rules.json --rule-file dup-rules.json --unoptimize-rules ok.qasm >dup-rf.stdout 2>dup-rf.stderr
  [2]
  $ head -n 1 dup-rf.stderr
  qasminfer: --rule-file cannot be specified more than once.

A closed output stream is an io error like any other, not a crash after the
work is already done.

  $ qasminfer ok.qasm >&- 2>closed.stderr
  [1]
  $ cat closed.stderr
  qasminfer: io: <stdout>: Bad file descriptor

The same holds when --json would have put a second copy of the diagnostic on the
stream that just failed.

  $ qasminfer --json ok.qasm >&- 2>closed-json.stderr
  [1]
  $ cat closed-json.stderr
  qasminfer: io: <stdout>: Bad file descriptor

  $ qasminfer --json --unoptimize-rules no-such.qasm >&- 2>closed-domain.stderr
  [1]
  $ cat closed-domain.stderr
  qasminfer: io: no-such.qasm: No such file or directory
