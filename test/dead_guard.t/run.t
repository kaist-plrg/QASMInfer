The contextual rule uses the ordinary deep empty-LHS ordinals. Listing counts
syntactic sites; addressing an unsafe site is a typed refusal without output.

  $ cat > source.qasm <<'QASM'
  > OPENQASM 3.0;
  > include "stdgates.inc";
  > qubit[2] q;
  > bit[2] c;
  > h q[0];
  > c[0] = measure q[0];
  > x q[1];
  > c[1] = measure q[1];
  > QASM
  $ qasminfer --unoptimize-rules source.qasm | grep Insert_Dead_If_Bit
  Insert_Dead_If_Bit: occurrences=4 param=cbit_instr
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 1 --emit oq3 --trace choice.json source.qasm before.qasm
  $ cat before.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  bit[2] c;
  h q[0];
  if (c[0]) {
    id q[0];
  }
  c[0] = measure q[0];
  x q[1];
  c[1] = measure q[1];
  $ grep 'payload_policy' choice.json
    "payload_policy": "id",
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 2 source.qasm refused.qasm
  qasminfer: rule: rule Insert_Dead_If_Bit precondition failed at occurrence 2: a preceding measurement may write c[0]
  [1]
  $ test ! -e refused.qasm
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 4 source.qasm refused.qasm
  qasminfer: occurrence: Occurrence 4 is out of range for rule 'Insert_Dead_If_Bit' with 4 occurrence(s).
  [1]

A measurement into another bit is allowed. Explicit payloads use the existing
parser and are recorded in the trace. Even a self-writing body is dead.

  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 1 --occurrence 2 --instr 'measure q[1] -> c[1];' --emit oq3 --trace explicit.json source.qasm other.qasm
  $ grep 'payload_policy' explicit.json
    "payload_policy": "explicit",
  $ qasminfer --json source.qasm > original.json
  $ qasminfer --json other.qasm > other.json
  $ cmp original.json other.json
  $ qasminfer --unoptimize --step 0 --emit oq3 other.qasm roundtrip.qasm
  $ cmp other.qasm roundtrip.qasm

OQ2 behaviour is the existing emitter's behaviour: partial-register guards
are refused, but a guard covering a one-bit register is representable.

  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 0 --emit oq2 source.qasm oq2.qasm
  qasminfer: emit: cannot express the program in OpenQASM 2: unrepresentable conditional: condition does not cover a whole classical register
  [1]
  $ test ! -e oq2.qasm
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 0 source.qasm auto.qasm
  $ head -1 auto.qasm
  OPENQASM 3.0;
  $ cat > one.qasm <<'QASM'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[1];
  > creg c[1];
  > h q[0];
  > measure q[0] -> c[0];
  > QASM
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 1 --emit oq2 one.qasm one-out.qasm
  $ grep 'if' one-out.qasm
  if(c==1) id q[0];
  $ qasminfer --unoptimize --step 0 --emit oq2 one-out.qasm one-again.qasm
  $ cmp one-out.qasm one-again.qasm

A guarded write in an earlier prefix counts even if that guard itself is dead.
Inside a body, only its preceding siblings and enclosing prefixes matter.

  $ cat > deep.qasm <<'QASM'
  > OPENQASM 3.0;
  > include "stdgates.inc";
  > qubit[2] q;
  > bit[2] c;
  > if (c[1]) {
  >   h q[0];
  >   c[0] = measure q[0];
  >   x q[1];
  > }
  > h q[1];
  > QASM
  $ qasminfer --unoptimize-rules deep.qasm | grep Insert_Dead_If_Bit
  Insert_Dead_If_Bit: occurrences=5 param=cbit_instr
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 2 --instr 'x q[0];' --emit oq3 deep.qasm deep-out.qasm
  $ cat deep-out.qasm
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  bit[2] c;
  if (c[1]) {
    h q[0];
    if (c[0]) {
      x q[0];
    }
    c[0] = measure q[0];
    x q[1];
  }
  h q[1];
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 3 deep.qasm refused.qasm
  qasminfer: rule: rule Insert_Dead_If_Bit precondition failed at occurrence 3: a preceding measurement may write c[0]
  [1]
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --occurrence 4 deep.qasm refused.qasm
  qasminfer: rule: rule Insert_Dead_If_Bit precondition failed at occurrence 4: a preceding measurement may write c[0]
  [1]

Random one-qubit payload selection is seed-reproducible, including its trace.

  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --random-1q --seed 79 --trace random1.json source.qasm random1.qasm
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --random-1q --seed 79 --trace random2.json source.qasm random2.qasm
  $ cmp random1.qasm random2.qasm
  $ cmp random1.json random2.json
  $ grep 'payload_policy' random1.json
    "payload_policy": "random-1q",
  $ qasminfer --json random1.qasm > random.json
  $ cmp original.json random.json
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 2 source.qasm invalid.qasm
  qasminfer: param: Manual cbit 2 is out of range for 2 cbit(s).
  [1]
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --cbits 0 --instr 'x q[2];' source.qasm invalid.qasm 2>invalid.err
  [1]
  $ grep -o 'qasminfer: param:' invalid.err
  qasminfer: param:
  $ qasminfer --unoptimize --rule Insert_Dead_If_Bit --random-1q --instr 'id q[0];' source.qasm invalid.qasm 2>args.err
  [2]
  $ head -1 args.err
  --random-1q cannot be combined with --instr or --instr-file
