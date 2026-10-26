Named gates survive canonicalization, and rule addressing respects three wire roles.

  $ cat > input.qasm <<'QASM'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[3];
  > cz q[0],q[1];
  > cy q[0],q[1];
  > ch q[0],q[1];
  > csx q[0],q[1];
  > ccx q[0],q[1],q[2];
  > cswap q[0],q[1],q[2];
  > rccx q[0],q[1],q[2];
  > QASM
  $ qasminfer --unoptimize --step 0 input.qasm output.qasm
  $ cat output.qasm
  OPENQASM 2.0;
  include "qelib1.inc";
  qreg q[3];
  cz q[0],q[1];
  cy q[0],q[1];
  ch q[0],q[1];
  csx q[0],q[1];
  ccx q[0],q[1],q[2];
  cswap q[0],q[1],q[2];
  rccx q[0],q[1],q[2];
  $ cat > rules.json <<'JSON'
  > [{"name":"expand_ccx","lhs":[{"gate":"ccx","control1":0,"control2":1,"target":2}],"rhs":[{"gate":"ccx","control1":0,"control2":1,"target":2},{"gate":"ccx","control1":0,"control2":1,"target":2},{"gate":"ccx","control1":0,"control2":1,"target":2}]}]
  > JSON
  $ qasminfer --unoptimize-rules --json --rule-file rules.json input.qasm | grep -A 2 '"name": "expand_ccx"'
        "name": "expand_ccx",
        "occurrences": 1,
        "param": "none"
  $ qasminfer --unoptimize --rule-file rules.json --rule expand_ccx --qbits 0,1,2 --occurrence 0 input.qasm expanded.qasm
  $ grep '^ccx' expanded.qasm
  ccx q[0],q[1],q[2];
  ccx q[0],q[1],q[2];
  ccx q[0],q[1],q[2];
  $ qasminfer --unoptimize --rule-file rules.json --rule expand_ccx --qbits 0,0,2 input.qasm bad.qasm
  qasminfer: param: rule expand_ccx requires distinct qubits
  [1]
  $ test ! -e bad.qasm

The instruction payload grammar includes the OQ3-local native gates too.

  $ cat > payload.qasm <<'QASM'
  > OPENQASM 2.0;
  > include "qelib1.inc";
  > qreg q[3];
  > creg c[1];
  > h q[0];
  > QASM
  $ qasminfer --unoptimize --rule Insert_If_FT --cbits 0 --occurrence 0 --instr 'csx q[0],q[1]; rccx q[0],q[1],q[2];' payload.qasm guarded.qasm
  $ grep '^    csx\|^    rccx' guarded.qasm
      csx q[0],q[1];
      rccx q[0],q[1],q[2];
