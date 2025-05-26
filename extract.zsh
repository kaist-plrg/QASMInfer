#!/bin/zsh

# Step 1: Go to the "core" directory
cd core

# Step 2: Run the "make" command
coq_makefile -f _CoqProject -o Makefile
make clean
make COQFLAGS="-w -all"

# Step 3: Add "open Complex" at the beginning of "../qasm/lib/quantum_core.ml"

# < What is added >
# open Complex

FILE="../qasm/lib/core/quantum_core.ml"

if [[ "$OSTYPE" == "darwin"* ]]; then
  # macOS (BSD sed)
  sed -i '' $'1s/^/open Complex\\\n\\\n/' "$FILE"
else
  # Linux (GNU sed)
  sed -i '1s/^/open Complex\n\n/' "$FILE"
fi

# Step 5: Leave the "core" directory
cd ..
