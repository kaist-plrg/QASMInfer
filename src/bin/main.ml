open Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api

module IntMap = Map.Make(Int)

type version = V2 | V3

(* Which OpenQASM dialect --unoptimize writes.  [Emit_auto] keeps OpenQASM 2
   whenever the transformed program fits in it, so existing outputs stay
   byte-identical, and falls back to OpenQASM 3 for the nested conditionals only
   OpenQASM 3 can spell. *)
type emit_mode = Emit_auto | Emit_oq2 | Emit_oq3

(* Where the --instr payload comes from.  It is kept as text until SOURCE has
   been read, because it is parsed against SOURCE's register layout. *)
type instr_source = Instr_text of string | Instr_file of string

let emit_mode_of_string = function
  | "auto" -> Some Emit_auto
  | "oq2" -> Some Emit_oq2
  | "oq3" -> Some Emit_oq3
  | _ -> None

(* A failure the user can act on.  The first field is the error class, which is
   part of the CLI contract; see the "Exit codes and error classes" section of
   the README. *)
exception Cli_error of string * string

let cli_error error_class format =
  Printf.ksprintf (fun detail -> raise (Cli_error (error_class, detail))) format

(* System error messages usually carry the path, but not always: reading a
   directory reports a bare "Is a directory" on some platforms.  Make every io
   diagnostic name the file exactly once. *)
let io_error file_path message =
  if String.starts_with ~prefix:(file_path ^ ":") message then
    cli_error "io" "%s" message
  else cli_error "io" "%s: %s" file_path message

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
      step: int option;
      rule_file : string option;
      rule_name : string option;
      manual : Unoptimize.manual_parameters option;
      emit : emit_mode;
      instr_source : instr_source option;
      seed : int option;
    }
  | UnoptimizeRules of {
      source : string;
      verbose : bool;
      emit_json : bool;
      output_file : string option;
      rule_file : string option;
    }

type result_entry = {
  state : string;
  probability : float;
}

let usage_msg =
  "usage: qasminfer [--verbose] [--json] [--output FILE] SOURCE\n\
   \       qasminfer --unoptimize [--verbose] [--step N] [--seed N]\n\
   \                 [--emit auto|oq2|oq3] [--rule-file FILE]\n\
   \                 [--rule NAME [--qbits Q[,Q]] [--cbits C]\n\
   \                 [--instr TEXT | --instr-file FILE] [--occurrence K]]\n\
   \                 SOURCE DESTINATION\n\
   \       qasminfer --unoptimize-rules [--verbose] [--json] [--output FILE]\n\
   \                 [--rule-file FILE] SOURCE"

let parse_args argv =
  let verbose = ref false in
  let emit_json = ref false in
  let unoptimize = ref false in
  let unoptimize_rules = ref false in
  let output_file = ref None in
  let step = ref None in
  let rule_file = ref None in
  let rule_name = ref None in
  let qbits = ref None in
  let cbits = ref None in
  let occurrence = ref None in
  let emit = ref None in
  let seed = ref None in
  let instr_text = ref None in
  let instr_file = ref None in
  let positionals = ref [] in
  let parse_int_list option_name raw =
    let parse_token token =
      let token = String.trim token in
      if token = "" then
        raise
          (Arg.Bad
             (Printf.sprintf "%s expects comma-separated non-negative integers"
                option_name));
      try
        let value = int_of_string token in
        if value < 0 then
          raise
            (Arg.Bad
               (Printf.sprintf "%s expects non-negative integers" option_name));
        value
      with Failure _ ->
        raise
          (Arg.Bad
             (Printf.sprintf "%s expects comma-separated non-negative integers"
                option_name))
    in
    String.split_on_char ',' raw |> List.map parse_token
  in
  let set_int_list option_name target raw =
    match !target with
    | None -> target := Some (parse_int_list option_name raw)
    | Some _ -> raise (Arg.Bad (option_name ^ " cannot be specified more than once"))
  in
  let set_occurrence value =
    if value < 0 then raise (Arg.Bad "--occurrence must be non-negative");
    match !occurrence with
    | None -> occurrence := Some value
    | Some _ -> raise (Arg.Bad "--occurrence cannot be specified more than once")
  in
  let set_instr option_name target value =
    if Option.is_some !target then
      raise (Arg.Bad (option_name ^ " cannot be specified more than once"))
    else if Option.is_some !instr_text || Option.is_some !instr_file then
      raise (Arg.Bad "--instr and --instr-file cannot be combined")
    else target := Some value
  in
  let set_emit raw =
    match emit_mode_of_string raw with
    | None -> raise (Arg.Bad "--emit expects auto, oq2, or oq3")
    | Some _ when Option.is_some !emit ->
        raise (Arg.Bad "--emit cannot be specified more than once")
    | Some mode -> emit := Some mode
  in
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
      ( "--unoptimize-rules",
        Arg.Set unoptimize_rules,
        "List unoptimization rules applicable to SOURCE" );
      ( "--verbose",
        Arg.Set verbose,
        "Print intermediate QASMCore representation" );
      ("-v", Arg.Set verbose, "Short for --verbose");
      ("--step", Arg.Int (fun n -> step := Some n), "Set step number of unoptimization");
      ( "--rule",
        Arg.String (fun name -> rule_name := Some name),
        "Apply only the transform rule named NAME once" );
      ( "--qbits",
        Arg.String (set_int_list "--qbits" qbits),
        "Set comma-separated qbit parameter(s) for --unoptimize --rule" );
      ( "--cbits",
        Arg.String (set_int_list "--cbits" cbits),
        "Set comma-separated cbit parameter(s) for --unoptimize --rule" );
      ( "--occurrence",
        Arg.Int set_occurrence,
        "Set rewrite occurrence for --unoptimize --rule" );
      ( "--rule-file",
        Arg.String (fun path -> rule_file := Some path),
        "Read standard-gate rewrite rules from JSON FILE" );
      ( "--emit",
        Arg.String set_emit,
        "Choose the DESTINATION dialect: auto (default), oq2, or oq3" );
      ( "--seed",
        Arg.Int
          (fun value ->
            if Option.is_some !seed then
              raise (Arg.Bad "--seed cannot be specified more than once");
            seed := Some value),
        "Seed the generator that picks random rewrites" );
      ( "--instr",
        Arg.String (set_instr "--instr" instr_text),
        "Fix the instruction a cbit_instr rule inserts, as QASM TEXT" );
      ( "--instr-file",
        Arg.String (set_instr "--instr-file" instr_file),
        "Read the --instr payload from FILE" );
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
  let instr_source =
    match (!instr_text, !instr_file) with
    | Some text, _ -> Some (Instr_text text)
    | None, Some path -> Some (Instr_file path)
    | None, None -> None
  in
  let manual_options_used =
    Option.is_some !qbits || Option.is_some !cbits || Option.is_some !occurrence
    || Option.is_some instr_source
  in
  let manual =
    if manual_options_used then
      Some
        {
          Unoptimize.qbits = !qbits;
          cbits = !cbits;
          occurrence = !occurrence;
          instr = None;
        }
    else None
  in
  match (!unoptimize, !unoptimize_rules, positionals) with
  | true, true, _ ->
      usage_error "--unoptimize cannot be used with --unoptimize-rules"
  | false, _, _ when Option.is_some !emit ->
      usage_error "--emit can only be used with --unoptimize"
  | false, _, _ when Option.is_some !seed ->
      usage_error "--seed can only be used with --unoptimize"
  | false, _, _ when Option.is_some instr_source ->
      usage_error "--instr and --instr-file can only be used with --unoptimize"
  | false, true, _ when manual_options_used ->
      usage_error
        "--qbits, --cbits, and --occurrence cannot be used with --unoptimize-rules"
  | true, false, _ when !emit_json ->
      usage_error "--json cannot be used with --unoptimize"
  | true, false, _ when Option.is_some !output_file ->
      usage_error "--output/-o cannot be used with --unoptimize"
  | true, false, _ when Option.is_some !rule_name && Option.is_some !step ->
      usage_error "--rule cannot be used with --step"
  | true, false, _
    when Option.is_some instr_source && Option.is_none !rule_name ->
      usage_error "--instr and --instr-file require --rule"
  | true, false, _ when manual_options_used && Option.is_none !rule_name ->
      usage_error "--qbits, --cbits, and --occurrence require --rule"
  | true, false, [ source; destination ] ->
      Unoptimize
        {
          source;
          destination;
          verbose = !verbose;
          step = !step;
          rule_file = !rule_file;
          rule_name = !rule_name;
          manual;
          emit = Option.value !emit ~default:Emit_auto;
          instr_source;
          seed = !seed;
        }
  | true, false, _ ->
      usage_error
        "--unoptimize expects exactly two positional arguments: SOURCE DESTINATION"
  | false, true, _ when Option.is_some !step ->
      usage_error "--step cannot be used with --unoptimize-rules"
  | false, true, _ when Option.is_some !rule_name ->
      usage_error "--rule cannot be used with --unoptimize-rules"
  | false, true, [ source ] ->
      UnoptimizeRules
        {
          source;
          verbose = !verbose;
          emit_json = !emit_json;
          output_file = !output_file;
          rule_file = !rule_file;
        }
  | false, true, _ ->
      usage_error "--unoptimize-rules expects exactly one positional SOURCE"
  | false, false, _ when manual_options_used ->
      usage_error "--qbits, --cbits, and --occurrence can only be used with --unoptimize --rule"
  | false, false, _ when Option.is_some !step ->
      usage_error "--step can only be used with --unoptimize"
  | false, false, _ when Option.is_some !rule_file ->
      usage_error "--rule-file can only be used with --unoptimize or --unoptimize-rules"
  | false, false, _ when Option.is_some !rule_name ->
      usage_error "--rule can only be used with --unoptimize"
  | false, false, [ source ] ->
      Execute
        {
          source;
          verbose = !verbose;
          emit_json = !emit_json;
          output_file = !output_file;
        }
  | false, false, _ -> usage_error "execution expects exactly one positional SOURCE"

let rec to_binary n =
  if n = 0 then "0"
  else if n = 1 then "1"
  else to_binary (n / 2) ^ string_of_int (n mod 2)

let int_of_cstate = Big_int_Z.int_of_big_int

let to_map =
  List.fold_left
    (fun acc (k, v) -> IntMap.add (int_of_cstate k) v acc)
    IntMap.empty

let dense_list (nc: int) exec_res : float list =
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

let text_of_applicable_rules rules =
  rules
  |> List.map (fun { Unoptimize.name; occurrences; param } ->
         Printf.sprintf "%s: occurrences=%d param=%s" name occurrences param)
  |> String.concat "\n"
  |> fun body -> if body = "" then body else body ^ "\n"

let json_of_applicable_rules source nq nc rules =
  let rules_json =
    rules
    |> List.map (fun { Unoptimize.name; occurrences; param } ->
           Printf.sprintf
             "    {\n      \"name\": \"%s\",\n      \"occurrences\": %d,\n      \"param\": \"%s\"\n    }"
             (json_escape name) occurrences (json_escape param))
    |> String.concat ",\n"
  in
  if rules_json = "" then
    Printf.sprintf
      "{\n  \"source\": \"%s\",\n  \"qubits\": %d,\n  \"clbits\": %d,\n  \"rules\": []\n}\n"
      (json_escape source) nq nc
  else
    Printf.sprintf
      "{\n  \"source\": \"%s\",\n  \"qubits\": %d,\n  \"clbits\": %d,\n  \"rules\": [\n%s\n  ]\n}\n"
      (json_escape source) nq nc rules_json

let write_result output_file output =
  match output_file with
  | None -> (
      try output_string stdout output with
      | Sys_error message -> cli_error "io" "<stdout>: %s" message)
  | Some path -> (
      try
        let channel = open_out path in
        Fun.protect
          ~finally:(fun () -> close_out channel)
          (fun () -> output_string channel output)
      with Sys_error message -> io_error path message)

let log_line line =
  output_string stderr line;
  output_char stderr '\n'

(* Quoting a line of the source back to the user must not let the source dictate
   the shape of a diagnostic: a domain error is one printable line, so bound the
   quotation and replace anything non-printable. *)
let quote_source_line line =
  let limit = 60 in
  let visible =
    String.map
      (fun character ->
        let code = Char.code character in
        if code < 0x20 || code = 0x7f then '?' else character)
      line
  in
  if String.length visible <= limit then visible
  else String.sub visible 0 limit ^ "..."

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
      failwith
        ("Unsupported QASM version: " ^ quote_source_line first_meaningful_line)
  else
    failwith
      ("Invalid QASM file format: " ^ quote_source_line first_meaningful_line)

let read_source file_path =
  try In_channel.with_open_bin file_path In_channel.input_all with
  | Sys_error message -> io_error file_path message

let parse_and_desugar_string ~filename source =
  let version =
    try check_qasm_version source with
    | Failure message -> cli_error "parse" "%s" message
  in
  let ast =
    match version with
    | V2 -> Q2.parse_string_result ~filename source
    | V3 -> Q3.parse_string_result ~filename source |> Result.map Q3.desugar
  in
  let ast =
    match ast with
    | Ok program -> program
    | Error message -> cli_error "parse" "%s" message
  in
  let ast = Q2.inline_qelib ast in
  try Q2.desugar ast with
  | Failure message -> cli_error "parse" "%s: %s" filename message

let parse_and_desugar file_path =
  parse_and_desugar_string ~filename:file_path (read_source file_path)

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

let specs_of_rule_file_option nq rule_file =
  match rule_file with
  | None -> None
  | Some path -> (
      match Unoptimize.specs_of_rule_file nq path with
      | Ok specs -> Some specs
      (* specs_of_rule_file surfaces Sys_error messages verbatim, and those
         already name the file. *)
      | Error message when String.starts_with ~prefix:(path ^ ":") message ->
          cli_error "rule-file" "%s" message
      | Error message -> cli_error "rule-file" "%s: %s" path message)

(* Render the transformed program in the requested dialect.  OpenQASM 3 can
   express every QASMCore instruction, so it is always available as the
   fallback; OpenQASM 2 cannot spell nested or single-bit guards. *)
let render_program emit nq nc q_assignment c_assignment instruction =
  let as_oq2 () = Q2.sugar nq nc q_assignment c_assignment instruction in
  let as_oq3 () =
    match Q3.sugar nq nc q_assignment c_assignment instruction with
    | Ok program -> Q3.string_of_program program
    | Error message ->
        cli_error "emit" "cannot express the program in OpenQASM 3: %s" message
  in
  match emit with
  | Emit_oq3 -> as_oq3 ()
  | Emit_oq2 -> (
      match as_oq2 () with
      | Ok program -> Q2.string_of_program program
      | Error message ->
          cli_error "emit" "cannot express the program in OpenQASM 2: %s" message)
  | Emit_auto -> (
      match as_oq2 () with
      | Ok program -> Q2.string_of_program program
      | Error _ -> as_oq3 ())

(* Parse an --instr payload against SOURCE's own register layout.

   The payload names registers by the canonical names the sugar would print, so
   for an OpenQASM 3 source using physical qubits it names the renamed register
   ("qasm3_physical[0]"), not "$0".  The generated preamble is one line, so a
   diagnostic's line number is the payload's own except on the first line, where
   the column is shifted. *)
let instruction_of_payload nq nc q_assignment c_assignment payload =
  let declarations =
    match Q3.sugar nq nc q_assignment c_assignment Extracted.NopInstr with
    | Ok program -> program
    | Error message -> cli_error "param" "--instr: %s" message
  in
  let preamble =
    Q3.Ast.Include "stdgates.inc" :: declarations
    |> Q3.string_of_program |> String.split_on_char '\n'
    |> List.filter (fun line -> line <> "")
    |> String.concat " "
  in
  let payload_nq, payload_nc, instruction, _, _ =
    try
      parse_and_desugar_string ~filename:"--instr" (preamble ^ " " ^ payload ^ "\n")
    with Cli_error (_, detail) -> cli_error "param" "%s" detail
  in
  if payload_nq <> nq || payload_nc <> nc then
    cli_error "param" "--instr: the payload must not declare registers";
  instruction

let payload_text = function
  | Instr_text text -> text
  | Instr_file path -> read_source path

let unoptimize source destination step verbose rule_file rule_name manual emit
    instr_source seed =
  let nq, nc, instr, q_assignment, c_assignment =
    parse_and_desugar source
  in
  let specs = specs_of_rule_file_option nq rule_file in
  let manual =
    match instr_source with
    | None -> manual
    | Some instr_source ->
        let instruction =
          instruction_of_payload nq nc q_assignment c_assignment
            (payload_text instr_source)
        in
        let manual =
          Option.value manual
            ~default:
              { Unoptimize.qbits = None; cbits = None; occurrence = None; instr = None }
        in
        Some { manual with Unoptimize.instr = Some instruction }
  in
  let transformed =
    try Unoptimize.unoptimize ?specs ?rule_name ?manual ?seed instr step nq nc with
    | Unoptimize.Domain_error (error_class, detail) ->
        raise (Cli_error (error_class, detail))
  in
  log_instruction verbose transformed;
  let output =
    render_program emit nq nc q_assignment c_assignment transformed
  in
  write_result (Some destination) output

let unoptimize_rules source verbose emit_json output_file rule_file =
  let nq, nc, instr, _, _ = parse_and_desugar source in
  let specs = specs_of_rule_file_option nq rule_file in
  log_instruction verbose instr;
  let rules =
    try Unoptimize.applicable_rules ?specs instr nq nc with
    | Unoptimize.Domain_error (error_class, detail) ->
        raise (Cli_error (error_class, detail))
  in
  let output =
    if emit_json then json_of_applicable_rules source nq nc rules
    else text_of_applicable_rules rules
  in
  write_result output_file output

let output_message channel message =
  output_string channel message;
  if message = "" || message.[String.length message - 1] <> '\n' then
    output_char channel '\n'

let json_of_error error_class detail =
  Printf.sprintf
    "{\n  \"error\": {\n    \"class\": \"%s\",\n    \"message\": \"%s\"\n  }\n}\n"
    (json_escape error_class) (json_escape detail)

(* Every domain failure prints exactly one stderr line, and, when the caller
   asked for JSON, the same failure as a structured object on stdout. *)
let one_line detail =
  String.map
    (fun character ->
      let code = Char.code character in
      if code < 0x20 || code = 0x7f then ' ' else character)
    detail

let report_domain_error emit_json error_class detail =
  (* The JSON object keeps the detail verbatim, escaped; the stderr line is
     flattened so the one-line contract holds whatever the detail contains. *)
  if emit_json then output_string stdout (json_of_error error_class detail);
  output_message stderr
    (Printf.sprintf "qasminfer: %s: %s" error_class (one_line detail));
  1

let run_command = function
  | Execute { source; verbose; emit_json; output_file } ->
      execute source verbose emit_json output_file
  | Unoptimize
      {
        source;
        destination;
        step;
        verbose;
        rule_file;
        rule_name;
        manual;
        emit;
        instr_source;
        seed;
      } ->
      let step = Option.value step ~default:1 in
      unoptimize source destination step verbose rule_file rule_name manual emit
        instr_source seed
  | UnoptimizeRules { source; verbose; emit_json; output_file; rule_file } ->
      unoptimize_rules source verbose emit_json output_file rule_file

let emits_json = function
  | Execute { emit_json; _ } | UnoptimizeRules { emit_json; _ } -> emit_json
  | Unoptimize _ -> false

let main argv =
  let no_arguments = Array.length argv <= 1 in
  match parse_args argv with
  | exception Arg.Help message ->
      output_message stdout message;
      0
  | exception Arg.Bad message ->
      output_message stderr message;
      (* A bare "qasminfer" keeps its legacy exit status; every other
         argument-shape error exits 2. *)
      if no_arguments then 1 else 2
  | command -> (
      let emit_json = emits_json command in
      let fail = report_domain_error emit_json in
      match run_command command with
      | () -> 0
      | exception Cli_error (error_class, detail) -> fail error_class detail
      | exception Unoptimize.Domain_error (error_class, detail) ->
          fail error_class detail
      | exception Sys_error message -> fail "io" message
      | exception Failure message -> fail "internal" message
      | exception Stack_overflow -> fail "internal" "stack overflow"
      | exception Out_of_memory -> fail "internal" "out of memory"
      | exception exn -> fail "internal" (Printexc.to_string exn))

let () = exit (main Sys.argv)
