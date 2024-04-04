open Quantum_core
open OpenQASM2.OpenQASM
open Desugarer.Desugar
open Desugarer.Desugar_option
open Desugarer.Stringify

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

let main () =
  let file_path = Sys.argv.(1) in
  let ast = get_ast file_path |> inline_qelib in
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
