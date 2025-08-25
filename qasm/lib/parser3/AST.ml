type id = string
type ty = TVal | TCReg of int | TQReg of int | TGate of int * int
type binaryop = Plus | Minus | Times | Div | Pow
type unaryop = Sin | Cos | Tan | Exp | Ln | Sqrt | UMinus

type exp =
  | Real of float
  | Nninteger of int
  | Pi
  | Id of id
  | BinaryOp of binaryop * exp * exp
  | UnaryOp of unaryop * exp

type argument = id * int option

type uop =
  | CX of argument * argument
  | U of exp list * argument
  | Gate of id * exp list * argument list

type qop = Uop of uop | Meas of argument * argument | Reset of argument
type gop = GUop of uop | GBarrier of id list
type gatedecl = id * id list * id list
type decl = QReg of id * int | CReg of id * int

type statement =
  | Include of string
  | Decl of decl
  | GateDecl of gatedecl * gop list
  | OpaqueDecl of gatedecl
  | Qop of qop
  | If of id * int * qop list
  | Barrier of argument list

type program = statement list

(* OCaml code version of stringifier *)

let code_of_id id = "\"" ^ id ^ "\""

let code_of_ty = function
  | TVal -> "TVal"
  | TCReg i -> Printf.sprintf "TCReg %d" i
  | TQReg i -> Printf.sprintf "TQReg %d" i
  | TGate (a, b) -> Printf.sprintf "TGate (%d, %d)" a b

let code_of_binaryop = function
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Div -> "Div"
  | Pow -> "Pow"

let code_of_unaryop = function
  | Sin -> "Sin"
  | Cos -> "Cos"
  | Tan -> "Tan"
  | Exp -> "Exp"
  | Ln -> "Ln"
  | Sqrt -> "Sqrt"
  | UMinus -> "UMinus"

let rec code_of_exp = function
  | Real f -> Printf.sprintf "Real (%f)" f
  | Nninteger i -> Printf.sprintf "Nninteger (%d)" i
  | Pi -> "Pi"
  | Id id -> Printf.sprintf "Id (%s)" (code_of_id id)
  | BinaryOp (op, e1, e2) ->
      Printf.sprintf "BinaryOp (%s, %s, %s)" (code_of_binaryop op)
        (code_of_exp e1) (code_of_exp e2)
  | UnaryOp (op, e) ->
      Printf.sprintf "UnaryOp (%s, %s)" (code_of_unaryop op) (code_of_exp e)

let code_of_argument (id, opt) =
  match opt with
  | None -> Printf.sprintf "(%s, None)" (code_of_id id)
  | Some i -> Printf.sprintf "(%s, Some %d)" (code_of_id id) i

let code_of_uop = function
  | CX (arg1, arg2) ->
      Printf.sprintf "CX (%s, %s)" (code_of_argument arg1)
        (code_of_argument arg2)
  | U (exps, arg) ->
      Printf.sprintf "U ([%s], %s)"
        (String.concat "; " (List.map code_of_exp exps))
        (code_of_argument arg)
  | Gate (id, exps, args) ->
      Printf.sprintf "Gate (%s, [%s], [%s])" (code_of_id id)
        (String.concat "; " (List.map code_of_exp exps))
        (String.concat "; " (List.map code_of_argument args))

let code_of_qop = function
  | Uop uop -> Printf.sprintf "Uop (%s)" (code_of_uop uop)
  | Meas (arg1, arg2) ->
      Printf.sprintf "Meas (%s, %s)" (code_of_argument arg1)
        (code_of_argument arg2)
  | Reset arg -> Printf.sprintf "Reset (%s)" (code_of_argument arg)

let code_of_gop = function
  | GUop uop -> Printf.sprintf "GUop (%s)" (code_of_uop uop)
  | GBarrier ids ->
      Printf.sprintf "GBarrier [%s]"
        (String.concat "; " (List.map code_of_id ids))

let code_of_gatedecl (id, id_list1, id_list2) =
  Printf.sprintf "(%s, [%s], [%s])" (code_of_id id)
    (String.concat "; " (List.map code_of_id id_list1))
    (String.concat "; " (List.map code_of_id id_list2))

let code_of_decl = function
  | QReg (id, i) -> Printf.sprintf "QReg (%s, %d)" (code_of_id id) i
  | CReg (id, i) -> Printf.sprintf "CReg (%s, %d)" (code_of_id id) i

let code_of_statement = function
  | Include s -> Printf.sprintf "Include \"%s\"" s
  | Decl decl -> Printf.sprintf "Decl (%s)" (code_of_decl decl)
  | GateDecl (gdecl, gops) ->
      Printf.sprintf "GateDecl (%s, [%s])" (code_of_gatedecl gdecl)
        (String.concat "; " (List.map code_of_gop gops))
  | OpaqueDecl gdecl ->
      Printf.sprintf "OpaqueDecl (%s)" (code_of_gatedecl gdecl)
  | Qop qop -> Printf.sprintf "Qop (%s)" (code_of_qop qop)
  | If (id, i, qops) ->
      Printf.sprintf "If (%s, %d, [%s])" (code_of_id id) i
        (String.concat "; " (List.map code_of_qop qops))
  | Barrier args ->
      Printf.sprintf "Barrier [%s]"
        (String.concat "; " (List.map code_of_argument args))

let code_of_program program =
  Printf.sprintf "[%s]"
    (String.concat "; " (List.map code_of_statement program))
