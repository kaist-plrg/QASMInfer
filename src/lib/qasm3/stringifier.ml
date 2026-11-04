open Ast

(* Renders the OpenQASM 3 subset this front end parses.  Everything printed here
   must reparse through Parser to the same AST; the round-trip is covered by
   test/unoptimize_unit.ml. *)

let string_of_float_round_trip value =
  if not (Float.is_finite value) then
    invalid_arg "OpenQASM 3 cannot represent non-finite floats";
  let rendered = Printf.sprintf "%.17g" value in
  if
    String.contains rendered '.'
    || String.contains rendered 'e'
    || String.contains rendered 'E'
  then rendered
  else rendered ^ ".0"

let string_of_binaryop = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Pow -> "^"

let string_of_unaryop = function
  | Sin -> "sin"
  | Cos -> "cos"
  | Tan -> "tan"
  | Exp -> "exp"
  | Ln -> "ln"
  | Sqrt -> "sqrt"
  | UMinus -> "-"

let rec string_of_exp = function
  | Real value -> string_of_float_round_trip value
  | Nninteger value -> string_of_int value
  | Pi -> "pi"
  | Id id -> id
  | BinaryOp (operator, left, right) ->
      Printf.sprintf "(%s %s %s)" (string_of_exp left)
        (string_of_binaryop operator) (string_of_exp right)
  | UnaryOp (UMinus, expression) -> "-(" ^ string_of_exp expression ^ ")"
  | UnaryOp (operator, expression) ->
      Printf.sprintf "%s(%s)" (string_of_unaryop operator)
        (string_of_exp expression)

let string_of_argument (id, index) =
  match index with
  | None -> id
  | Some index -> Printf.sprintf "%s[%d]" id index

let string_of_exp_list expressions =
  String.concat "," (List.map string_of_exp expressions)

let string_of_argument_list arguments =
  String.concat "," (List.map string_of_argument arguments)

let string_of_id_list ids = String.concat "," ids

let gate_head keyword (id, parameters, arguments) =
  let parameters =
    match parameters with
    | [] -> ""
    | _ -> "(" ^ string_of_id_list parameters ^ ")"
  in
  Printf.sprintf "%s %s%s %s" keyword id parameters (string_of_id_list arguments)

let string_of_uop = function
  | CX (control, target) ->
      Printf.sprintf "CX %s,%s;" (string_of_argument control)
        (string_of_argument target)
  | U (expressions, argument) ->
      Printf.sprintf "U(%s) %s;" (string_of_exp_list expressions)
        (string_of_argument argument)
  | Gate (id, expressions, arguments) ->
      let parameters =
        match expressions with
        | [] -> ""
        | _ -> "(" ^ string_of_exp_list expressions ^ ")"
      in
      Printf.sprintf "%s%s %s;" id parameters (string_of_argument_list arguments)

let string_of_qop = function
  | Uop uop -> string_of_uop uop
  (* OpenQASM 3 spells measurement as an assignment. *)
  | Meas (qubit, cbit) ->
      Printf.sprintf "%s = measure %s;" (string_of_argument cbit)
        (string_of_argument qubit)
  | Reset argument -> Printf.sprintf "reset %s;" (string_of_argument argument)

let string_of_gop = function
  | GUop uop -> string_of_uop uop
  | GBarrier ids -> "barrier " ^ string_of_id_list ids ^ ";"

let string_of_cond = function
  | CondReg (id, value) -> Printf.sprintf "%s == %d" id value
  | CondBit (id, index, true) -> Printf.sprintf "%s[%d]" id index
  | CondBit (id, index, false) -> Printf.sprintf "!%s[%d]" id index

let rec lines_of_statement indent statement =
  let pad = String.make (indent * 2) ' ' in
  match statement with
  | Include filename -> [ Printf.sprintf "%sinclude %S;" pad filename ]
  | Decl (QReg (id, size)) -> [ Printf.sprintf "%squbit[%d] %s;" pad size id ]
  | Decl (CReg (id, size)) -> [ Printf.sprintf "%sbit[%d] %s;" pad size id ]
  | GateDecl (declaration, body) ->
      (Printf.sprintf "%s%s {" pad (gate_head "gate" declaration)
      :: List.map
           (fun operation -> pad ^ "  " ^ string_of_gop operation)
           body)
      @ [ pad ^ "}" ]
  | OpaqueDecl declaration -> [ pad ^ gate_head "opaque" declaration ^ ";" ]
  | Qop qop -> [ pad ^ string_of_qop qop ]
  | If (cond, body) ->
      (Printf.sprintf "%sif (%s) {" pad (string_of_cond cond)
      :: List.concat_map (lines_of_statement (indent + 1)) body)
      @ [ pad ^ "}" ]
  | Barrier arguments ->
      [ pad ^ "barrier " ^ string_of_argument_list arguments ^ ";" ]

let string_of_program program =
  match program with
  | [] -> "OPENQASM 3.0;\n"
  | _ ->
      "OPENQASM 3.0;\n"
      ^ String.concat "\n" (List.concat_map (lines_of_statement 0) program)
      ^ "\n"
