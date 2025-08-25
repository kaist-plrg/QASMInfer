open AST

let rec string_of_program prog =
  String.concat "\n" (List.map string_of_statement prog)

and string_of_statement = function
  | Include filename -> "include \"" ^ filename ^ "\""
  | Decl decl -> string_of_decl decl
  | GateDecl (gatedecl, gop_list) ->
      string_of_gatedecl gatedecl ^ " { " ^ string_of_gop_list gop_list ^ " }"
  | OpaqueDecl gatedecl -> string_of_gatedecl gatedecl
  | Qop qop -> string_of_qop qop
  | If (id, int, qops) ->
      "if " ^ id ^ " " ^ string_of_int int ^ " " ^ string_of_qop_list qops
  | Barrier argument_list -> "barrier " ^ string_of_argument_list argument_list

and string_of_decl = function
  | QReg (id, int) -> "qreg " ^ id ^ " " ^ string_of_int int
  | CReg (id, int) -> "creg " ^ id ^ " " ^ string_of_int int

and string_of_gatedecl (id, id_list1, id_list2) =
  "gate " ^ id ^ " " ^ string_of_id_list id_list1 ^ ", "
  ^ string_of_id_list id_list2

and string_of_qop = function
  | Uop uop -> string_of_uop uop
  | Meas (arg1, arg2) ->
      "meas " ^ string_of_argument arg1 ^ ", " ^ string_of_argument arg2
  | Reset arg -> "reset " ^ string_of_argument arg

and string_of_uop = function
  | CX (arg1, arg2) ->
      "cx " ^ string_of_argument arg1 ^ ", " ^ string_of_argument arg2
  | U (exp_list, arg) ->
      "u (" ^ string_of_exp_list exp_list ^ ") " ^ string_of_argument arg
  | Gate (id, exp_list, arg_list) ->
      "gate " ^ id ^ " "
      ^ string_of_exp_list exp_list
      ^ ", "
      ^ string_of_argument_list arg_list

and string_of_argument (id, int_opt) =
  match int_opt with
  | Some int -> id ^ "[" ^ string_of_int int ^ "]"
  | None -> id

and string_of_exp = function
  | Real f -> string_of_float f
  | Nninteger i -> string_of_int i
  | Pi -> "pi"
  | Id id -> id
  | BinaryOp (bop, exp1, exp2) ->
      string_of_binaryop bop ^ " " ^ string_of_exp exp1 ^ ", "
      ^ string_of_exp exp2
  | UnaryOp (uop, exp) -> string_of_unaryop uop ^ " " ^ string_of_exp exp

and string_of_binaryop = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Pow -> "^"

and string_of_unaryop = function
  | Sin -> "sin"
  | Cos -> "cos"
  | Tan -> "tan"
  | Exp -> "exp"
  | Ln -> "ln"
  | Sqrt -> "sqrt"
  | UMinus -> "-"

and string_of_exp_list exp_list =
  String.concat ", " (List.map string_of_exp exp_list)

and string_of_argument_list arg_list =
  String.concat ", " (List.map string_of_argument arg_list)

and string_of_id_list id_list = String.concat ", " id_list

and string_of_gop_list gop_list =
  String.concat "\n" (List.map string_of_gop gop_list)

and string_of_qop_list qop_list =
  String.concat "\n" (List.map string_of_qop qop_list)

and string_of_gop = function
  | GUop uop -> string_of_uop uop
  | GBarrier id_list -> "barrier " ^ string_of_id_list id_list
