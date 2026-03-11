open Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api

module IntMap = Map.Make(Int)

type version = V2 | V3

let verbose = ref false
let emit_json = ref false
let input_file = ref ""
let output_file = ref None

type result_entry = {
  state : string;
  probability : float;
}

let usage_msg = "usage: qasminfer <qasm_file> [--verbose] [--json] [--output FILE]"

let set_output_file path =
  match !output_file with
  | None -> output_file := Some path
  | Some _ -> raise (Arg.Bad "Multiple output files are not supported")

let speclist = [
  ("--verbose", Arg.Set verbose, "Print intermediate QASMCore representation");
  ("-v", Arg.Set verbose, "Short for --verbose");
  ("--json", Arg.Set emit_json, "Emit result as JSON");
  ("--output", Arg.String set_output_file, "Write result to FILE instead of stdout");
  ("-o", Arg.String set_output_file, "Short for --output");
]

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

let result_entries nc probabilities =
  List.mapi
    (fun i probability ->
      { state = int_to_binary_fixed_width i nc; probability })
    probabilities

let format_probability probability =
  Printf.sprintf "%.16e" probability

let json_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (function
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\b' -> Buffer.add_string buf "\\b"
      | '\012' -> Buffer.add_string buf "\\f"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | c when Char.code c < 0x20 ->
          Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char buf c)
    s;
  Buffer.contents buf

let text_of_result entries =
  entries
  |> List.map (fun { state; probability } ->
         Printf.sprintf "%s : %s" state (format_probability probability))
  |> String.concat "\n"
  |> fun body -> body ^ "\n"

let json_of_result nq nc entries =
  let probabilities =
    entries
    |> List.map (fun { state; probability } ->
           Printf.sprintf
             "    {\"state\": \"%s\", \"probability\": %s}"
             (json_escape state)
             (format_probability probability))
    |> String.concat ",\n"
  in
  if probabilities = "" then
    Printf.sprintf
      "{\n  \"qubits\": %d,\n  \"clbits\": %d,\n  \"probabilities\": []\n}\n"
      nq nc
  else
    Printf.sprintf
      "{\n  \"qubits\": %d,\n  \"clbits\": %d,\n  \"probabilities\": [\n%s\n  ]\n}\n"
      nq nc probabilities

let write_result output =
  match !output_file with
  | None -> output_string stdout output
  | Some path ->
      let channel = open_out path in
      Fun.protect
        ~finally:(fun () -> close_out channel)
        (fun () -> output_string channel output)

let log_line line =
  output_string stderr line;
  output_char stderr '\n'

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
  Arg.parse speclist set_input_file usage_msg;

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

  if !verbose then (
    log_line "QASMCore ========================================";
    log_line (Q2.string_of_instruction instr)
  );

  if !verbose then log_line "RESULT ==========================================";

  let result =
    execute_and_calculate_prob nq nc instr
    |> dense_list nc
    |> result_entries nc
    |> if !emit_json then json_of_result nq nc else text_of_result
  in
  write_result result

let _ = main ()
