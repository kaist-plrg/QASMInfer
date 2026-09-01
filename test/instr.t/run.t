The instruction a conditional rule inserts is drawn at random by default, so a
fully-addressed invocation was still not reproducible.  --instr fixes the
payload, which makes --rule + --cbits + --occurrence + --instr deterministic.

  $ cat > target.qasm <<'EOF'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[2];
  > creg c[2];
  > h q[0];
  > measure q[0] -> c[0];
  > EOF

Three fresh processes agree byte for byte.

  $ for run in 1 2 3; do
  >   qasminfer --unoptimize --rule Insert_If_FT --cbits 1 --occurrence 0 --instr 'x q[1];' target.qasm "run$run.qasm"
  > done
  $ cmp run1.qasm run2.qasm
  $ cmp run2.qasm run3.qasm
  $ cat run1.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  bit[2] c;
  if (!c[1]) {
    if (c[1]) {
      x q[1];
    }
  }
  h q[0];
  c[0] = measure q[0];

The payload may be several statements, and may use OpenQASM 3 syntax.

  $ qasminfer --unoptimize --rule Insert_If_TF --cbits 0 --occurrence 1 --instr 'reset q[0]; c[1] = measure q[1];' target.qasm multi.qasm
  $ cat multi.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  bit[2] c;
  h q[0];
  if (c[0]) {
    if (!c[0]) {
      reset q[0];
      c[1] = measure q[1];
    }
  }
  c[0] = measure q[0];

A conditional payload nests inside the inserted guard.

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'if (c[1]) { x q[0]; }' target.qasm nested.qasm
  $ cat nested.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  bit[2] c;
  if (!c[0]) {
    if (c[0]) {
      if (c[1]) {
        x q[0];
      }
    }
  }
  h q[0];
  c[0] = measure q[0];

--instr-file reads the same payload from a file.

  $ printf 'x q[1];\n' > payload.txt
  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 1 --occurrence 0 --instr-file payload.txt target.qasm from-file.qasm
  $ cmp run1.qasm from-file.qasm

Out-of-range references in the payload are a clean domain error.

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'x q[9];' target.qasm oor.qasm >oor.stdout 2>oor.stderr
  [1]
  $ test ! -e oor.qasm
  $ test ! -s oor.stdout
  $ grep -c '^qasminfer: param: --instr: ' oor.stderr
  1

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'measure q[0] -> c[9];' target.qasm oor-c.qasm >oor-c.stdout 2>oor-c.stderr
  [1]
  $ test ! -e oor-c.qasm
  $ grep -c '^qasminfer: param: --instr: ' oor-c.stderr
  1

A payload that does not parse is reported against the payload, not the source.

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'x q[0]' target.qasm syntax.qasm >syntax.stdout 2>syntax.stderr
  [1]
  $ test ! -e syntax.qasm
  $ grep -c '^qasminfer: param: --instr:' syntax.stderr
  1

A payload may not introduce registers.

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'qubit[3] extra; x extra[0];' target.qasm decl.qasm >decl.stdout 2>decl.stderr
  [1]
  $ test ! -e decl.qasm
  $ cat decl.stderr
  qasminfer: param: --instr: the payload must not declare registers

Rules that take no instruction payload reject --instr.

  $ qasminfer --unoptimize --rule Insert_I --qbits 0 --occurrence 0 --instr 'x q[0];' target.qasm wrong-rule.qasm >wrong-rule.stdout 2>wrong-rule.stderr
  [1]
  $ test ! -e wrong-rule.qasm
  $ cat wrong-rule.stderr
  qasminfer: param: rule Insert_I takes no instruction payload; --instr applies to cbit_instr rules

Argument-shape checks.

  $ qasminfer --unoptimize --instr 'x q[0];' target.qasm no-rule.qasm >no-rule.stdout 2>no-rule.stderr
  [2]
  $ test ! -e no-rule.qasm
  $ head -n 1 no-rule.stderr
  --instr and --instr-file require --rule

  $ qasminfer --unoptimize --rule Insert_If_FT --instr 'x q[0];' --instr-file payload.txt target.qasm both.qasm >both.stdout 2>both.stderr
  [2]
  $ test ! -e both.qasm
  $ head -n 1 both.stderr
  qasminfer: --instr and --instr-file cannot be combined.

  $ qasminfer --instr 'x q[0];' --unoptimize-rules target.qasm >rules.stdout 2>rules.stderr
  [2]
  $ head -n 1 rules.stderr
  --instr and --instr-file can only be used with --unoptimize

Without --instr the payload is still random, so the old behaviour is intact.

  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 target.qasm random.qasm
  $ head -n 1 random.qasm
  OPENQASM 3.0;
