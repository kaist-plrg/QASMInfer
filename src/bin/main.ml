open Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api

type version = V2 | V3

let usage () =
  prerr_endline "usage: qasminfer <qasm_file>";
  exit 1

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
  let rec find_version_line () =
    try
      let line = input_line ch in
      let trimmed = String.trim line in
      (* Skip empty lines or lines that are just whitespace *)
      if trimmed = "" then find_version_line ()
        (* Skip comment-only lines (lines that start with // after trimming) *)
      else if String.length trimmed >= 2 && String.sub trimmed 0 2 = "//" then
        find_version_line ()
      else line
    with End_of_file ->
      close_in ch;
      failwith "File is empty or contains only whitespace/comments"
  in
  let first_meaningful_line =
    try find_version_line ()
    with e ->
      close_in ch;
      raise e
  in
  close_in ch;
  if String.length first_meaningful_line >= 10 then
    let prefix = String.sub first_meaningful_line 0 10 in
    if prefix = "OPENQASM 2" then V2
    else if prefix = "OPENQASM 3" then V3
    else
      failwith
        ("Unsupported QASM version. Expected 'OPENQASM 2.x' or 'OPENQASM 3.x', \
          but found: " ^ first_meaningful_line)
  else
    failwith
      ("Invalid QASM file format. First line too short: "
     ^ first_meaningful_line)

let main () =
  if Array.length Sys.argv < 2 then usage ();
  let file_path = Sys.argv.(1) in
  let ast =
    (match check_qasm_version file_path with
    | V2 -> Q2.get_ast file_path
    | V3 -> Q3.get_ast file_path |> Q3.desugar)
    |> Q2.inline_qelib
  in
  let nq, program, _, _ = Q2.desugar ast in
  let () = print_endline "QASMCore ========================================" in
  let () = print_endline (Q2.string_of_instruction program.iP_instrs) in
  let () = print_endline "RESULT ==========================================" in
  let prob_map = execute_and_calculate_prob nq program in
  List.init (Int.shift_left 1 program.iP_num_cbits) (fun x ->
      x |> prob_map |> RbaseSymbolsImpl.coq_Rrepr)
  |> List.iteri (fun i prob ->
         Printf.printf "%s : %.16e\n"
           (int_to_binary_fixed_width i program.iP_num_cbits)
           prob)

let _ = main ()
