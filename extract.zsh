#!/bin/zsh

# Step 1: Go to the "core" directory
cd core

# Step 2: Run the "make" command
coq_makefile -f _CoqProject -o Makefile
make

# Step 3: Add "open Complex" at the beginning of "../qasm/lib/quantum_core.ml"

# < What is added >
# open Complex

# let memoize2 f =
#   let b = 8 in
#   let memo_table = Hashtbl.create (Int.shift_left 1 (b + b)) in
#   fun x y ->
#     let xy = Int.shift_left x b + y in
#     try Hashtbl.find memo_table xy
#     with Not_found ->
#       let result = f x y in
#       Hashtbl.add memo_table xy result;
#       result

sed -i '' '1s/^/open Complex\n\nlet memoize2 f =\n  let b = 8 in\n  let memo_table = Hashtbl.create (Int.shift_left 1 (b + b)) in\n  fun x y ->\n    let xy = Int.shift_left x b + y in\n    try Hashtbl.find memo_table xy\n    with Not_found ->\n      let result = f x y in\n      Hashtbl.add memo_table xy result;\n      result\n\n/' ../qasm/lib/core/quantum_core.ml


# Step 4: using cache
# Find and replace "minner = (fun i j" with "minner = memoize2 (fun i j"
sed -i '' 's/minner = (fun i j/minner = memoize2 (fun i j/' ../qasm/lib/core/quantum_core.ml

# Step 5: Leave the "core" directory
cd ..
