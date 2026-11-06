// Name of Experiment: stable CLI execution fixture

OPENQASM 2.0;
include "qelib1.inc";

qreg q[1];
creg c[2];

h q[0];
measure q[0] -> c[0];
