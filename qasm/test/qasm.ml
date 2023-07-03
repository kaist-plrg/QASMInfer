open Quantum_core
open OpenQASM2.OpenQASM
open OpenQASM2.Stringifier
open Desugarer.Desugar
open Desugarer.Stringify

let horizontal_line = "==========================================="
let () = print_endline horizontal_line
let () = print_endline "Quantum core Test"
let () = print_endline horizontal_line
let a = eye 3
let c = a.minner 2 2
let _ = Printf.printf ": %f\n%!" c.re

(* parsing test *)

let () = print_endline horizontal_line
let () = print_endline "Parsing Test"
let () = print_endline horizontal_line

(* let () =
   let current_dir = Sys.getcwd () in
   print_endline current_dir *)

(* let ast = get_ast "/Users/p51lee/dev/quantum-coq/qasm/example/basic.qasm" *)
(* let ast = get_ast "/Users/p51lee/dev/quantum-coq/qasm/example/parallel.qasm" *)
let ast =
  get_ast
    "/Users/p51lee/dev/quantum-coq/qasm/example/spec/quantum_teleportation.qasm"

let s = string_of_program ast
let () = print_endline s

(* desugar parallel test *)

let () = print_endline horizontal_line
let () = print_endline "Desugar parallel Test"
let () = print_endline horizontal_line
let ast_dp = desugar_parallel ast
let () = print_endline (string_of_program_dp ast_dp)

(* desugar macro test *)

let () = print_endline horizontal_line
let () = print_endline "Desugar macro Test"
let () = print_endline horizontal_line
let ast_dm = desugar_macro ast
let () = print_endline (string_of_program_dp ast_dm)

(* desugar qasm test *)

let () = print_endline horizontal_line
let () = print_endline "Desugar qasm Test"
let () = print_endline horizontal_line
let ast_qc_ir = desugar_qasm ast
let () = print_endline (string_of_qc_ir ast_qc_ir)

(* desugar qc_ir test *)

let () = print_endline horizontal_line
let () = print_endline "Desugar qc_ir Test"
let () = print_endline horizontal_line
let p, _, _ = desugar ast
let () = print_endline (string_of_instruction p.iP_instrs)
let () = print_int p.iP_num_qbits
