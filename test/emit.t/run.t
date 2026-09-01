Conditional rules produce a nested guard, which OpenQASM 2 cannot spell.  The
default --emit auto keeps OpenQASM 2 whenever the program fits in it and falls
back to OpenQASM 3 only when it does not.

  $ cat > measured.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[1];
  > creg c[1];
  > x q[0];
  > measure q[0] -> c[0];
  > EOF

  $ cat > guarded.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[1];
  > creg c[1];
  > if(c==1) x q[0];
  > EOF

  $ cat > guarded-false.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[1];
  > creg c[1];
  > if(c==0) x q[0];
  > EOF

All four conditional built-ins now write a DESTINATION.

  $ for rule in Insert_If_FT Insert_If_TF; do
  >   qasminfer --unoptimize --rule "$rule" --cbits 0 --occurrence 0 measured.qasm "out-$rule.qasm" || echo "FAILED $rule"
  >   head -n 1 "out-$rule.qasm"
  > done
  OPENQASM 3.0;
  OPENQASM 3.0;

  $ qasminfer --unoptimize --rule Double_If_True --occurrence 0 guarded.qasm out-Double_If_True.qasm
  $ head -n 1 out-Double_If_True.qasm
  OPENQASM 3.0;
  $ qasminfer --unoptimize --rule Double_If_False --occurrence 0 guarded-false.qasm out-Double_If_False.qasm
  $ head -n 1 out-Double_If_False.qasm
  OPENQASM 3.0;

The inserted payload is still drawn at random (see --instr), so only the guard
structure is pinned here.

  $ head -n 6 out-Insert_If_FT.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[1] q;
  bit[1] c;
  if (!c[0]) {
    if (c[0]) {
  $ head -n 6 out-Insert_If_TF.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[1] q;
  bit[1] c;
  if (c[0]) {
    if (!c[0]) {

  $ cat out-Double_If_True.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[1] q;
  bit[1] c;
  if (c[0]) {
    if (c[0]) {
      x q[0];
    }
  }

  $ cat out-Double_If_False.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[1] q;
  bit[1] c;
  if (!c[0]) {
    if (!c[0]) {
      x q[0];
    }
  }

Each output reparses through the OpenQASM 3 front end to the same program, so
re-emitting it is a fixed point.

  $ for rule in Insert_If_FT Insert_If_TF Double_If_True Double_If_False; do
  >   qasminfer --step 0 --unoptimize --emit oq3 "out-$rule.qasm" "again-$rule.qasm"
  >   cmp "out-$rule.qasm" "again-$rule.qasm" || echo "NOT STABLE $rule"
  > done

Round-tripping an OpenQASM 3 conditional preserves the execution distribution.

  $ cat > distribution.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[2];
  > creg c[2];
  > h q[0];
  > measure q[0] -> c[0];
  > if(c==1) x q[1];
  > measure q[1] -> c[1];
  > EOF
  $ qasminfer --unoptimize --rule Double_If_True --occurrence 0 distribution.qasm distribution.oq3.qasm
  $ head -n 1 distribution.oq3.qasm
  OPENQASM 3.0;
  $ qasminfer --json distribution.qasm > distribution.before.json
  $ qasminfer --json distribution.oq3.qasm > distribution.after.json
  $ cmp distribution.before.json distribution.after.json

--emit auto is the default and leaves OpenQASM 2 output byte-identical.

  $ qasminfer --step 0 --unoptimize measured.qasm auto-default.qasm
  $ qasminfer --step 0 --unoptimize --emit auto measured.qasm auto-explicit.qasm
  $ cmp auto-default.qasm auto-explicit.qasm
  $ head -n 1 auto-default.qasm
  OPENQASM 2.0;

--emit oq3 always emits OpenQASM 3, even for programs OpenQASM 2 could express.

  $ qasminfer --step 0 --unoptimize --emit oq3 measured.qasm forced-oq3.qasm
  $ cat forced-oq3.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[1] q;
  bit[1] c;
  x q[0];
  c[0] = measure q[0];

--emit oq2 refuses programs OpenQASM 2 cannot express, cleanly and without
creating a destination.

  $ qasminfer --unoptimize --emit oq2 --rule Insert_If_FT --cbits 0 --occurrence 0 measured.qasm refused.qasm >refused.stdout 2>refused.stderr
  [1]
  $ test ! -e refused.qasm
  $ test ! -s refused.stdout
  $ cat refused.stderr
  qasminfer: emit: cannot express the program in OpenQASM 2: unrepresentable conditional: condition does not cover a whole classical register

An unknown dialect is an argument-shape error.

  $ qasminfer --unoptimize --emit oq4 measured.qasm bad-emit.qasm >bad-emit.stdout 2>bad-emit.stderr
  [2]
  $ test ! -e bad-emit.qasm
  $ head -n 1 bad-emit.stderr
  qasminfer: --emit expects auto, oq2, or oq3.

--emit only applies to --unoptimize.

  $ qasminfer --emit oq3 --unoptimize-rules measured.qasm >emit-rules.stdout 2>emit-rules.stderr
  [2]
  $ head -n 1 emit-rules.stderr
  --emit can only be used with --unoptimize

  $ qasminfer --emit oq3 measured.qasm >emit-exec.stdout 2>emit-exec.stderr
  [2]
  $ head -n 1 emit-exec.stderr
  --emit can only be used with --unoptimize
