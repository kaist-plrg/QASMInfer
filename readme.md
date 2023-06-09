# Verified QASM Interpreter

First theoretical quantum computing simulator
* that can simulate all OpenQASM 2.0 circuits (measurements don't have to be at the end of the circuit).
* whose quantum mechanical consistency is verified via Coq.


## Build
```
coq_makefile -f _CoqProject -o Makefile
make
```

## Source Files
```
 src
 ├── Util.v         # for utilities
 ├── Complex.v      # for complex numbers
 ├── Matrix.v       # for complex matrices
 ├── Tensor.v       # for tensor product operations
 ├── Operator.v     # for unitary operators
 ├── Qubit.v        # for quantum qubit states
 ├── Density.v      # for density matrices and measurement
 └── Physics.v      # for physical consistency
```
