OPENQASM 2.0;
include "qelib1.inc";

qreg left[2];
qreg right[1];
creg flags[2];
creg result[1];

h left[0];
x left[1];
cx left[0],right[0];
rz(pi/3) left[1];
measure left -> flags;
if (flags==2) measure left -> flags;
measure right[0] -> result[0];
reset right[0];
