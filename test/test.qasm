OPENQASM 2.0;
include "qelib1.inc";

qreg q[10];
creg c[2];

id q[0];
h q[0];
if(c == 0) id q[0];
cx q[0], q[1];
measure q[1] -> c[0];
