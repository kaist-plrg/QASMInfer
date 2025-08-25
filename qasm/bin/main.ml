open Quantum_core
open OpenQASM2.OpenQASM
open Desugarer.Desugar
open Desugarer.Desugar_option
open Desugarer.Stringify
module OpenQASM3 = OpenQASM3.OpenQASM
module Desugar3 = Desugarer3.Desugar

type version = V2 | V3

let rec to_binary n =
  if n = 0 then "0"
  else if n = 1 then "1"
  else to_binary (n / 2) ^ string_of_int (n mod 2)

let int_to_binary_fixed_width n width =
  let binary = to_binary n in
  let len = String.length binary in
  if len >= width then binary
  else
    let padding = String.make (width - len) '0' in
    padding ^ binary

let check_qasm_version file_path =
  let ch = open_in file_path in
  let first_line =
    try input_line ch
    with End_of_file ->
      close_in ch;
      failwith "File is empty"
  in
  close_in ch;
  if String.length first_line >= 10 then
    let prefix = String.sub first_line 0 10 in
    if prefix = "OPENQASM 2" then V2
    else if prefix = "OPENQASM 3" then V3
    else
      failwith
        ("Unsupported QASM version. Expected 'OPENQASM 2.x' or 'OPENQASM 3.x', \
          but found: " ^ first_line)
  else failwith ("Invalid QASM file format. First line too short: " ^ first_line)

let main () =
  let file_path = Sys.argv.(1) in
  let ast =
    (match check_qasm_version file_path with
    | V2 -> get_ast file_path
    | V3 -> OpenQASM3.get_ast file_path |> Desugar3.desugar3_program)
    |> inline_qelib
  in
  let success = desugar_option ast |> Option.is_some in
  let () =
    if not success then print_endline "Desugaring_opt returned None" else ()
  in
  let nq, program, _, _ = desugar ast in
  let () = print_endline "QASMCore ========================================" in
  let () = print_endline (string_of_instruction program.iP_instrs) in
  let () = print_endline "RESULT ==========================================" in
  let prob_map = execute_and_calculate_prob nq program in
  List.init (Int.shift_left 1 program.iP_num_cbits) (fun x ->
      x |> prob_map |> RbaseSymbolsImpl.coq_Rrepr)
  |> List.iteri (fun i prob ->
         Printf.printf "%s : %.16e\n"
           (int_to_binary_fixed_width i program.iP_num_cbits)
           prob)

let _ = main ()
