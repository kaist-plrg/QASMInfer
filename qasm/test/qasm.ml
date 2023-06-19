open Quantum_core

let () = print_endline "Hello, Test!"
let a = eye 3
let c = a.minner 2 2
let _ = Printf.printf ": %f\n%!" c.re