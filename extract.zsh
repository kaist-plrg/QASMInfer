#!/bin/zsh

# Step 1: Go to the "core" directory
cd core

# Step 2: Run the "make" command
coq_makefile -f _CoqProject -o Makefile
make

# Step 3: Add "open Complex" at the beginning of "../qasm/lib/quantum_core.ml"
sed -i '' '1s/^/open Complex\n/' ../qasm/lib/core/quantum_core.ml

# Step 4: Leave the "core" directory
cd ..
