open Quantum_core
open OpenQASM2.AST
open Desugar

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
  | SeqInstr (instr1, instr2) ->
      string_of_instruction instr1 ^ "\n" ^ string_of_instruction instr2
  | IfInstr (i, b, instr) ->
      Printf.sprintf "IfInstr (%d, %b, \n%s)" i b (string_of_instruction instr)

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
