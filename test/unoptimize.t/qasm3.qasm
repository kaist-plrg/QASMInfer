OPENQASM 3.0;

qubit[1] qasm3_physical;
bit[1] result;

U(pi,0,pi) $0;
CX $0,qasm3_physical[0];
result[0] = measure $0;
