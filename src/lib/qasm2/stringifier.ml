open Ast
open Desugar
open Extracted

let string_of_float_round_trip value =
  if not (Float.is_finite value) then
    invalid_arg "OpenQASM 2 cannot represent non-finite floats";
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
  Printf.sprintf "%s %s%s %s" keyword id parameters
    (string_of_id_list arguments)

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
      Printf.sprintf "%s%s %s;" id parameters
        (string_of_argument_list arguments)

let string_of_qop = function
  | Uop uop -> string_of_uop uop
  | Meas (qubit, cbit) ->
      Printf.sprintf "measure %s -> %s;" (string_of_argument qubit)
        (string_of_argument cbit)
  | Reset argument -> Printf.sprintf "reset %s;" (string_of_argument argument)

let string_of_gop = function
  | GUop uop -> string_of_uop uop
  | GBarrier ids -> "barrier " ^ string_of_id_list ids ^ ";"

let string_of_statement = function
  | Include filename -> Printf.sprintf "include %S;" filename
  | Decl (QReg (id, size)) -> Printf.sprintf "qreg %s[%d];" id size
  | Decl (CReg (id, size)) -> Printf.sprintf "creg %s[%d];" id size
  | GateDecl (declaration, body) ->
      let body =
        body |> List.map (fun operation -> "  " ^ string_of_gop operation)
        |> String.concat "\n"
      in
      if body = "" then gate_head "gate" declaration ^ " {\n}"
      else gate_head "gate" declaration ^ " {\n" ^ body ^ "\n}"
  | OpaqueDecl declaration -> gate_head "opaque" declaration ^ ";"
  | Qop qop -> string_of_qop qop
  | If (id, value, qop) ->
      Printf.sprintf "if(%s==%d) %s" id value (string_of_qop qop)
  | Barrier arguments ->
      "barrier " ^ string_of_argument_list arguments ^ ";"

let string_of_program program =
  match program with
  | [] -> "OPENQASM 2.0;\n"
  | _ ->
      "OPENQASM 2.0;\n"
      ^ String.concat "\n" (List.map string_of_statement program)
      ^ "\n"

  (****************************)
(* OpenQASMCore stringifier *)
(****************************)

let rec string_of_instruction = function
  | NopInstr -> "NopInstr"
  | RotateInstr (x, y, z, i) ->
      Printf.sprintf "RotateInstr (%f, %f, %f, %d)"
        (RbaseSymbolsImpl.coq_Rrepr x)
        (RbaseSymbolsImpl.coq_Rrepr y)
        (RbaseSymbolsImpl.coq_Rrepr z)
        i
  | CnotInstr (i, j) -> Printf.sprintf "CnotInstr (%d, %d)" i j
  | SwapInstr (i, j) -> Printf.sprintf "SwapInstr (%d, %d)" i j
  | MeasureInstr (i, j) -> Printf.sprintf "MeasureInstr (%d, %d)" i j
  (* JYJ TODO : temp *)
  | SeqInstr [] -> failwith "Empty SeqInstr"
  | SeqInstr (h :: t) ->
      string_of_instruction h ^ "\n" ^ string_of_instruction (SeqInstr t)
  | IfInstr (i, b, instr) ->
      Printf.sprintf "IfInstr (%d, %b, \n%s)" i b (string_of_instruction instr)
  | ResetInstr i -> Printf.sprintf "ResetInstr %d" i

(*******************************)
(* OpenQASMCore_ir stringifier *)
(*******************************)

let rec string_of_qc_ir = function
  | NopIr -> "NopIr"
  | RotateIr (x, y, z, i) ->
      Printf.sprintf "RotateIr (%f, %f, %f, %d)"
        (RbaseSymbolsImpl.coq_Rrepr x)
        (RbaseSymbolsImpl.coq_Rrepr y)
        (RbaseSymbolsImpl.coq_Rrepr z)
        i
  | CnotIr (i, j) -> Printf.sprintf "CnotIr (%d, %d)" i j
  | MeasureIr (i, j) -> Printf.sprintf "MeasureIr (%d, %d)" i j
  | ResetIr i -> Printf.sprintf "ResetIr %d" i
  | SeqIr (ir1, ir2) -> string_of_qc_ir ir1 ^ "\n" ^ string_of_qc_ir ir2
  | IfIr (i, b, ir) ->
      Printf.sprintf "IfIr (%d, %b, \n%s)" i b (string_of_qc_ir ir)

(***************************)
(* OpenQASM_dp stringifier *)
(***************************)

let string_of_binaryop = function
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Div -> "Div"
  | Pow -> "Pow"

let string_of_unaryop = function
  | Sin -> "Sin"
  | Cos -> "Cos"
  | Tan -> "Tan"
  | Exp -> "Exp"
  | Ln -> "Ln"
  | Sqrt -> "Sqrt"
  | UMinus -> "UMinus"

let rec string_of_exp = function
  | Real f -> Printf.sprintf "Real %f" f
  | Nninteger i -> Printf.sprintf "Nninteger %d" i
  | Pi -> "Pi"
  | Id id -> Printf.sprintf "Id %s" id
  | BinaryOp (op, e1, e2) ->
      Printf.sprintf "BinaryOp (%s, %s, %s)" (string_of_binaryop op)
        (string_of_exp e1) (string_of_exp e2)
  | UnaryOp (op, e) ->
      Printf.sprintf "UnaryOp (%s, %s)" (string_of_unaryop op) (string_of_exp e)

let string_of_argument_dp (id, i) = Printf.sprintf "(%s, %d)" id i

let string_of_uop_dp = function
  | CX_dp (a1, a2) ->
      Printf.sprintf "CX_dp (%s, %s)" (string_of_argument_dp a1)
        (string_of_argument_dp a2)
  | U_dp (exps, a) ->
      Printf.sprintf "U_dp (%s, %s)"
        (String.concat ", " (List.map string_of_exp exps))
        (string_of_argument_dp a)
  | Gate_dp (id, exps, args) ->
      Printf.sprintf "Gate_dp (%s, [%s], [%s])" id
        (String.concat ", " (List.map string_of_exp exps))
        (String.concat ", " (List.map string_of_argument_dp args))

let string_of_qop_dp = function
  | Uop_dp u -> Printf.sprintf "Uop_dp (%s)" (string_of_uop_dp u)
  | Meas_dp (a1, a2) ->
      Printf.sprintf "Meas_dp (%s, %s)" (string_of_argument_dp a1)
        (string_of_argument_dp a2)
  | Reset_dp a -> Printf.sprintf "Reset_dp (%s)" (string_of_argument_dp a)

let string_of_statement_dp = function
  | Qop_dp q -> Printf.sprintf "Qop_dp (%s)" (string_of_qop_dp q)
  | IfList_dp (id, i, qlist) ->
      Printf.sprintf "IfList_dp (%s, %d, [%s])" id i
        (String.concat ", " (List.map string_of_qop_dp qlist))

let string_of_program_dp prog =
  String.concat "\n" (List.map string_of_statement_dp prog)
