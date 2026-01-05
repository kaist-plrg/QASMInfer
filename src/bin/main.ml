open Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api

module IntMap = Map.Make(Int)

type version = V2 | V3

(* 1. Define a reference for the verbose flag *)
let verbose = ref false
let input_file = ref ""

(* 2. Define the usage message *)
let usage_msg = "usage: qasminfer <qasm_file> [--verbose]"

(* 3. Define the list of options *)
let speclist = [
  ("--verbose", Arg.Set verbose, "Print intermediate QASMCore representation");
  ("-v", Arg.Set verbose, "Short for --verbose");
]

(* 4. Define what to do with anonymous arguments (the file path) *)
let set_input_file s =
  if !input_file = "" then input_file := s
  else raise (Arg.Bad "Multiple input files are not supported")

let rec to_binary n =
  if n = 0 then "0"
  else if n = 1 then "1"
  else to_binary (n / 2) ^ string_of_int (n mod 2)

let to_map = List.fold_left (fun acc (k, v) -> IntMap.add k v acc) IntMap.empty

let dense_list (nc: int) (exec_res: (int * float) list): float list =
  let sparse_map = to_map exec_res in
  (* interpreted value of IH of Rocq's positive, also # of possible classical states *)
  let num_classical_states = Int.shift_left 1 nc in
  let positive_base = Int.shift_left 1 nc in
  let full_list =
    List.init num_classical_states (fun i ->
      match IntMap.find_opt (positive_base + i) sparse_map with
      | Some v -> v
      | None -> 0.0) in
  full_list

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
      if trimmed = "" then find_version_line ()
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
      failwith ("Unsupported QASM version: " ^ first_meaningful_line)
  else
    failwith ("Invalid QASM file format: " ^ first_meaningful_line)

let main () =
  (* 5. Parse arguments *)
  Arg.parse speclist set_input_file usage_msg;

  (* Check if a file was actually provided *)
  if !input_file = "" then (
    Arg.usage speclist usage_msg;
    exit 1
  );

  let file_path = !input_file in
  let ast =
    (match check_qasm_version file_path with
    | V2 -> Q2.get_ast file_path
    | V3 -> Q3.get_ast file_path |> Q3.desugar)
    |> Q2.inline_qelib
  in
  let nq, nc, instr, _, _ = Q2.desugar ast in

  (* 6. Optional Part: Only run if !verbose is true *)
  if !verbose then (
    print_endline "QASMCore ========================================";
    print_endline (Q2.string_of_instruction instr)
  );

  (* Always run execution part *)
  if !verbose then print_endline "RESULT ==========================================";

  let prob_map = execute_and_calculate_prob nq nc instr in
  prob_map
  |> dense_list nc
  |> List.iteri (
    fun i prob -> Printf.printf "%s : %.16e\n" (int_to_binary_fixed_width i nc) prob
    )

let _ = main ()