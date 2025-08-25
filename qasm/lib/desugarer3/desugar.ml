open OpenQASM3.AST
module AST2 = OpenQASM2.AST

(**************************)
(* 1. unroll if statement *)
(**************************)

let desugar3_ty = function
  | TVal -> AST2.TVal
  | TCReg i -> AST2.TCReg i
  | TQReg i -> AST2.TQReg i
  | TGate (a, b) -> AST2.TGate (a, b)

let desugar3_binaryop = function
  | Plus -> AST2.Plus
  | Minus -> AST2.Minus
  | Times -> AST2.Times
  | Div -> AST2.Div
  | Pow -> AST2.Pow

let desugar3_unaryop = function
  | Sin -> AST2.Sin
  | Cos -> AST2.Cos
  | Tan -> AST2.Tan
  | Exp -> AST2.Exp
  | Ln -> AST2.Ln
  | Sqrt -> AST2.Sqrt
  | UMinus -> AST2.UMinus

let rec desugar3_exp = function
  | Real f -> AST2.Real f
  | Nninteger i -> AST2.Nninteger i
  | Pi -> AST2.Pi
  | Id id -> AST2.Id id
  | BinaryOp (bop, exp1, exp2) ->
      AST2.BinaryOp (desugar3_binaryop bop, desugar3_exp exp1, desugar3_exp exp2)
  | UnaryOp (uop, exp) -> AST2.UnaryOp (desugar3_unaryop uop, desugar3_exp exp)

let desugar3_uop = function
  | CX (arg1, arg2) -> AST2.CX (arg1, arg2)
  | U (exp_list, arg) -> AST2.U (List.map desugar3_exp exp_list, arg)
  | Gate (id, exp_list, arg_list) ->
      AST2.Gate (id, List.map desugar3_exp exp_list, arg_list)

let desugar3_qop = function
  | Uop uop -> AST2.Uop (desugar3_uop uop)
  | Meas (arg1, arg2) -> AST2.Meas (arg1, arg2)
  | Reset arg -> AST2.Reset arg

let desugar3_gop = function
  | GUop uop -> AST2.GUop (desugar3_uop uop)
  | GBarrier args -> AST2.GBarrier args

let desugar3_decl = function
  | QReg (id, i) -> AST2.QReg (id, i)
  | CReg (id, i) -> AST2.CReg (id, i)

let desugar3_statement = function
  | Include dep -> [ AST2.Include dep ]
  | Decl decl -> [ AST2.Decl (desugar3_decl decl) ]
  | GateDecl (gdecl, gop_list) ->
      [ AST2.GateDecl (gdecl, List.map desugar3_gop gop_list) ]
  | OpaqueDecl gdecl -> [ AST2.OpaqueDecl gdecl ]
  | Qop qop -> [ AST2.Qop (desugar3_qop qop) ]
  | If (id, i, qops) ->
      List.map (fun qop -> AST2.If (id, i, desugar3_qop qop)) qops
  | Barrier args -> [ AST2.Barrier args ]

let desugar3_program prog = List.flatten (List.map desugar3_statement prog)

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
