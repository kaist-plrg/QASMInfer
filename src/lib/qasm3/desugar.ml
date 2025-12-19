open Ast
module Ast2 = Qasm2.Ast

(******************************)
(* 1. Desugar physical qubits *)
(******************************)

let rec extract_physical_idx prog =
  match prog with
  | [] -> []
  | stmt :: rest -> (
      match stmt with
      | Qop (Uop (CX ((name1, Some idx1), (name2, Some idx2)))) ->
          if name1 = "$" && name2 = "$" then
            [ idx1; idx2 ] @ extract_physical_idx rest
          else if name1 = "$" then idx1 :: extract_physical_idx rest
          else if name2 = "$" then idx2 :: extract_physical_idx rest
          else extract_physical_idx rest
      | Qop (Uop (U (_, (name, Some idx)))) ->
          if name = "$" then idx :: extract_physical_idx rest
          else extract_physical_idx rest
      | Qop (Uop (Gate (_, _, args))) ->
          let physical_indices =
            List.fold_left
              (fun acc (arg_name, opt_idx) ->
                if arg_name = "$" then
                  match opt_idx with Some idx -> idx :: acc | None -> acc
                else acc)
              [] args
          in
          physical_indices @ extract_physical_idx rest
      | Qop (Meas ((name, Some idx), _)) | Qop (Reset (name, Some idx)) ->
          if name = "$" then idx :: extract_physical_idx rest
          else extract_physical_idx rest
      | _ -> extract_physical_idx rest)

let desugar_physical_qubits prog =
  let physical_indices = extract_physical_idx prog in
  match physical_indices with
  | [] -> prog
  | _ ->
      let max_idx = List.fold_left max 0 physical_indices in
      let qreg_decl = QReg ("$", max_idx + 1) in
      Decl qreg_decl :: prog

(**************************)
(* 2. unroll if statement *)
(**************************)

let desugar3_ty = function
  | TVal -> Ast2.TVal
  | TCReg i -> Ast2.TCReg i
  | TQReg i -> Ast2.TQReg i
  | TGate (a, b) -> Ast2.TGate (a, b)

let desugar3_binaryop = function
  | Plus -> Ast2.Plus
  | Minus -> Ast2.Minus
  | Times -> Ast2.Times
  | Div -> Ast2.Div
  | Pow -> Ast2.Pow

let desugar3_unaryop = function
  | Sin -> Ast2.Sin
  | Cos -> Ast2.Cos
  | Tan -> Ast2.Tan
  | Exp -> Ast2.Exp
  | Ln -> Ast2.Ln
  | Sqrt -> Ast2.Sqrt
  | UMinus -> Ast2.UMinus

let rec desugar3_exp = function
  | Real f -> Ast2.Real f
  | Nninteger i -> Ast2.Nninteger i
  | Pi -> Ast2.Pi
  | Id id -> Ast2.Id id
  | BinaryOp (bop, exp1, exp2) ->
      Ast2.BinaryOp (desugar3_binaryop bop, desugar3_exp exp1, desugar3_exp exp2)
  | UnaryOp (uop, exp) -> Ast2.UnaryOp (desugar3_unaryop uop, desugar3_exp exp)

let desugar3_uop = function
  | CX (arg1, arg2) -> Ast2.CX (arg1, arg2)
  | U (exp_list, arg) -> Ast2.U (List.map desugar3_exp exp_list, arg)
  | Gate (id, exp_list, arg_list) ->
      Ast2.Gate (id, List.map desugar3_exp exp_list, arg_list)

let desugar3_qop = function
  | Uop uop -> Ast2.Uop (desugar3_uop uop)
  | Meas (arg1, arg2) -> Ast2.Meas (arg1, arg2)
  | Reset arg -> Ast2.Reset arg

let desugar3_gop = function
  | GUop uop -> Ast2.GUop (desugar3_uop uop)
  | GBarrier args -> Ast2.GBarrier args

let desugar3_decl = function
  | QReg (id, i) -> Ast2.QReg (id, i)
  | CReg (id, i) -> Ast2.CReg (id, i)

let desugar3_statement = function
  | Include dep -> [ Ast2.Include dep ]
  | Decl decl -> [ Ast2.Decl (desugar3_decl decl) ]
  | GateDecl (gdecl, gop_list) ->
      [ Ast2.GateDecl (gdecl, List.map desugar3_gop gop_list) ]
  | OpaqueDecl gdecl -> [ Ast2.OpaqueDecl gdecl ]
  | Qop qop -> [ Ast2.Qop (desugar3_qop qop) ]
  | If (id, i, qops) ->
      List.map (fun qop -> Ast2.If (id, i, desugar3_qop qop)) qops
  | Barrier args -> [ Ast2.Barrier args ]

let desugar3_program prog =
  let prog = desugar_physical_qubits prog in
  List.flatten (List.map desugar3_statement prog)

(*******************************)
(* 2. desugar classical control *)
(*******************************)

(********************)
(* 5. for debugging *)
(********************)

(* let desugar_parallel qasm =
     let qreg_size_map = extract_qreg_size qasm in
     let creg_size_map = extract_creg_size qasm in
     desugar_parallel_program qasm qreg_size_map creg_size_map

   let desugar_macro qasm =
     let qreg_size_map = extract_qreg_size qasm in
     let creg_size_map = extract_creg_size qasm in
     let gate_decls = extract_gate_decl_rev qasm in
     let qasm_dp = desugar_parallel_program qasm qreg_size_map creg_size_map in
     desugar_macro_program qasm_dp gate_decls

   let desugar_qasm qasm =
     let qreg_order = extract_qreg_order qasm in
     let creg_order = extract_creg_order qasm in
     let qreg_size_map = extract_qreg_size qasm in
     let creg_size_map = extract_creg_size qasm in
     let gate_decls = extract_gate_decl_rev qasm in
     let qasm_dp = desugar_parallel_program qasm qreg_size_map creg_size_map in
     let qasm_dm = desugar_macro_program qasm_dp gate_decls in
     let assignment_q_seq = assign_seq qreg_order qreg_size_map in
     let assignment_q_rev = assign_arg_int assignment_q_seq in
     let assignment_c_seq = assign_seq creg_order creg_size_map in
     let assignment_c_rev = assign_arg_int assignment_c_seq in
     desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev qasm_dm *)
