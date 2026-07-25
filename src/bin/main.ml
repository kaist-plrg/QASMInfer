open Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api

module IntMap = Map.Make(Int)

type version = V2 | V3

exception Cli_error of string

type command =
  | Execute of {
      source : string;
      verbose : bool;
      emit_json : bool;
      output_file : string option;
    }
  | Unoptimize of {
      source : string;
      destination : string;
      verbose : bool;
    }

type result_entry = {
  state : string;
  probability : float;
}

let usage_msg =
  "usage: qasminfer [OPTIONS] SOURCE\n\
   \       qasminfer --unoptimize [--verbose] SOURCE DESTINATION"

let parse_args argv =
  let verbose = ref false in
  let emit_json = ref false in
  let unoptimize = ref false in
  let output_file = ref None in
  let positionals = ref [] in
  let set_output_file path =
    match !output_file with
    | None -> output_file := Some path
    | Some _ -> raise (Arg.Bad "Multiple output files are not supported")
  in
  let speclist =
    [ ( "--unoptimize",
        Arg.Set unoptimize,
        "Rewrite SOURCE as canonical OpenQASM 2 in DESTINATION" );
      ("--unopt", Arg.Set unoptimize, "Short for --unoptimize");
      ( "--verbose",
        Arg.Set verbose,
        "Print intermediate QASMCore representation" );
      ("-v", Arg.Set verbose, "Short for --verbose");
      ("--json", Arg.Set emit_json, "Emit result as JSON");
      ( "--output",
        Arg.String set_output_file,
        "Write result to FILE instead of stdout" );
      ("-o", Arg.String set_output_file, "Short for --output") ]
  in
  let argv = Array.copy argv in
  if Array.length argv > 0 then argv.(0) <- "qasminfer";
  Arg.parse_argv ~current:(ref 0) argv speclist
    (fun positional -> positionals := positional :: !positionals)
    usage_msg;
  let positionals = List.rev !positionals in
  let usage_error message =
    raise (Arg.Bad (message ^ "\n" ^ Arg.usage_string speclist usage_msg))
  in
  if Array.length argv <= 1 then
    raise (Arg.Bad (Arg.usage_string speclist usage_msg));
  match (!unoptimize, positionals) with
  | true, _ when !emit_json ->
      usage_error "--json cannot be used with --unoptimize"
  | true, _ when Option.is_some !output_file ->
      usage_error "--output/-o cannot be used with --unoptimize"
  | true, [ source; destination ] ->
      Unoptimize { source; destination; verbose = !verbose }
  | true, _ ->
      usage_error
        "--unoptimize expects exactly two positional arguments: SOURCE DESTINATION"
  | false, [ source ] ->
      Execute
        {
          source;
          verbose = !verbose;
          emit_json = !emit_json;
          output_file = !output_file;
        }
  | false, _ -> usage_error "execution expects exactly one positional SOURCE"

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

let write_result output_file output =
  match output_file with
  | None -> output_string stdout output
  | Some path ->
      let channel = open_out path in
      Fun.protect
        ~finally:(fun () -> close_out channel)
        (fun () -> output_string channel output)

let log_line line =
  output_string stderr line;
  output_char stderr '\n'

let check_qasm_version source =
  let rec find_version_line = function
    | [] -> failwith "File is empty or contains only whitespace/comments"
    | line :: rest ->
      let trimmed = String.trim line in
      if trimmed = "" then find_version_line rest
      else if String.length trimmed >= 2 && String.sub trimmed 0 2 = "//" then
        find_version_line rest
      else line
  in
  let first_meaningful_line =
    source |> String.split_on_char '\n' |> find_version_line
  in
  if String.length first_meaningful_line >= 10 then
    let prefix = String.sub first_meaningful_line 0 10 in
    if prefix = "OPENQASM 2" then V2
    else if prefix = "OPENQASM 3" then V3
    else
      failwith ("Unsupported QASM version: " ^ first_meaningful_line)
  else
    failwith ("Invalid QASM file format: " ^ first_meaningful_line)

let parse_and_desugar file_path =
  let source = In_channel.with_open_bin file_path In_channel.input_all in
  let ast =
    match check_qasm_version source with
    | V2 -> Q2.parse_string_result ~filename:file_path source
    | V3 ->
        Q3.parse_string_result ~filename:file_path source |> Result.map Q3.desugar
  in
  let ast =
    match ast with
    | Ok program -> program
    | Error message -> raise (Cli_error message)
  in
  let ast = Q2.inline_qelib ast in
  Q2.desugar ast

let log_instruction verbose instruction =
  if verbose then (
    log_line "QASMCore ========================================";
    log_line (Q2.string_of_instruction instruction)
  )

let execute source verbose emit_json output_file =
  let nq, nc, instr, _, _ = parse_and_desugar source in

  log_instruction verbose instr;

  if verbose then log_line "RESULT ==========================================";

  let result =
    execute_and_calculate_prob nq nc instr
    |> dense_list nc
    |> result_entries nc
    |> if emit_json then json_of_result nq nc else text_of_result
  in
  write_result output_file result

let unoptimize source destination verbose =
  let nq, nc, instr, q_assignment, c_assignment =
    parse_and_desugar source
  in
  let transformed = Unoptimize.unoptimize instr nq in
  log_instruction verbose transformed;
  let output =
    match Q2.sugar nq nc q_assignment c_assignment transformed with
    | Ok program -> Q2.string_of_program program
    | Error message -> failwith ("cannot sugar OpenQASMCore: " ^ message)
  in
  write_result (Some destination) output

let output_message channel message =
  output_string channel message;
  if message = "" || message.[String.length message - 1] <> '\n' then
    output_char channel '\n'

let main argv =
  let no_arguments = Array.length argv <= 1 in
  try
    match parse_args argv with
    | Execute { source; verbose; emit_json; output_file } ->
        execute source verbose emit_json output_file;
        0
    | Unoptimize { source; destination; verbose } ->
        unoptimize source destination verbose;
        0
  with
  | Arg.Help message ->
      output_message stdout message;
      0
  | Cli_error message ->
      output_message stderr ("qasminfer: " ^ message);
      1
  | Arg.Bad message ->
      output_message stderr message;
      if no_arguments then 1 else 2

let () = exit (main Sys.argv)
