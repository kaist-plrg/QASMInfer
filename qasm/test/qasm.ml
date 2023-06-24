open Quantum_core
open OpenQASM2.OpenQASM
open OpenQASM2.Stringifier

let () = print_endline "Hello, Test!"
let a = eye 3
let c = a.minner 2 2
let _ = Printf.printf ": %f\n%!" c.re

(* let () =
  let current_dir = Sys.getcwd () in
  print_endline current_dir *)


let ast = get_ast "/Users/p51lee/dev/quantum-coq/qasm/example/teleport.qasm"

let s = string_of_program ast

let () = print_endline s
