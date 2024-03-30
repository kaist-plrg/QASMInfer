Require Import AST.
Require Export Program.
Import ListNotations.

Open Scope nat_scope.

Definition argument_dp : Set := qasm_id * nat.

Inductive uop_dp : Set :=
| CX_dp : argument_dp -> argument_dp -> uop_dp
| U_dp : list qasm_exp -> argument_dp -> uop_dp
| Gate_dp :
  qasm_id -> list qasm_exp -> list argument_dp -> uop_dp.

Inductive qop_dp : Set :=
| Uop_dp : uop_dp -> qop_dp
| Meas_dp : argument_dp -> argument_dp -> qop_dp
| Reset_dp : argument_dp -> qop_dp.

Inductive statement_dp : Set :=
| Qop_dp : qop_dp -> statement_dp
| IfList_dp : qasm_id -> nat -> list qop_dp -> statement_dp.

Definition program_dp : Set := list statement_dp.

Definition IdMap := fun t => list_map qasm_id t.

Definition IdMap_empty {t} : IdMap t := [].

Definition IdMap_add {t} (key : qasm_id) (value : t) (map : IdMap t) : IdMap t :=
  lm_add key value map.

Definition IdMap_find {t} (map : IdMap t) (key : qasm_id) : option t :=
  lm_find qasm_id_eqb map key.

Fixpoint extract_qreg_order (qasm: qasm_program) : list qasm_id :=
  match qasm with
  | [] => nil
  | cons (QASM_Decl (QASM_QReg reg_id _)) tail =>
    cons reg_id (extract_qreg_order tail)
  | cons _ tail => extract_qreg_order tail
  end.

Fixpoint extract_creg_order (qasm : qasm_program) : list qasm_id :=
  match qasm with
  | [] => nil
  | cons (QASM_Decl (QASM_CReg reg_id _)) tail =>
    cons reg_id (extract_creg_order tail)
  | cons _ tail => extract_creg_order tail
  end.

Fixpoint extract_qreg_size (qasm : qasm_program) : IdMap nat :=
  match qasm with
  | [] => IdMap_empty
  | cons (QASM_Decl (QASM_QReg reg_id reg_size)) tail =>
    IdMap_add reg_id reg_size (extract_qreg_size tail)
  | cons _ tail => extract_qreg_size tail
  end.

Fixpoint extract_creg_size (qasm : qasm_program) : IdMap nat :=
  match qasm with
  | [] => IdMap_empty
  | cons (QASM_Decl (QASM_CReg reg_id reg_size)) tail =>
    IdMap_add reg_id reg_size (extract_creg_size tail)
  | cons _ tail => extract_creg_size tail
  end.

Fixpoint get_same_elem_opt (lst : list nat) : option nat :=
  match lst with
  | [] => Some 1
  | cons x t => ( match t with
    | [] => Some x
    | cons y _ => if x =? y then get_same_elem_opt t else None
    end)
  end.

Fixpoint index_arg_list (arg_list : list qasm_argument) (index : nat)
  : list argument_dp :=
  match arg_list with
  | [] => nil
  | cons (qid, None) tail => cons (qid, index) (index_arg_list tail index)
  | cons (qid, Some i_value) tail => cons (qid, i_value) (index_arg_list tail index)
  end.

Definition desugar_parallel_arg_list (arg_list : list qasm_argument) (qreg_size : IdMap nat)
  : option (list (list argument_dp)) :=
  arg_list
  |> option_l_concat_map (fun arg =>
    match arg with
    | (qid, None) => IdMap_find qreg_size qid >>| fun s => [ s ]
    | _ => Some []
    end)
  >>= get_same_elem_opt
  >>| fun s => list_init s (fun i => index_arg_list arg_list i).

Definition desugar_parallel_uop
  (operation : qasm_uop) (qreg_size : IdMap nat)
  : option (list uop_dp) :=
  match operation with
  | QASM_CX (qid1, None) (qid2, None) =>
    IdMap_find qreg_size qid1 >>= fun s1 =>
    IdMap_find qreg_size qid2 >>= fun s2 =>
    if s1 =? s2 then
      Some (list_init s1 (fun i => CX_dp (qid1, i) (qid2, i)))
    else None
  | QASM_CX (qid1, Some i1) (qid2, Some i2) => Some [ CX_dp (qid1, i1) (qid2, i2) ]
  | QASM_CX _ _ => None
  | QASM_U exp_list (qid, None) =>
    IdMap_find qreg_size qid >>| fun s =>
    list_init s (fun i => U_dp exp_list (qid, i))
  | QASM_U exp_list (qid, Some i_value) => Some [ U_dp exp_list (qid, i_value) ]
  | QASM_Gate gid exp_list arg_list =>
    desugar_parallel_arg_list arg_list qreg_size
    >>| map (fun arg_list_instantiated => Gate_dp gid exp_list arg_list_instantiated)
  end.

Definition desugar_parallel_qop
  (operation : qasm_qop) (qreg_size : IdMap nat)
  (creg_size : IdMap nat) : option (list qop_dp) :=
  match operation with
  | QASM_Uop uop => desugar_parallel_uop uop qreg_size >>| map Uop_dp
  | QASM_Meas (qid, None) (cid, None) =>
    IdMap_find qreg_size qid >>= fun s1 =>
    IdMap_find creg_size cid >>= fun s2 =>
    if s1 =? s2 then
      Some (list_init s1 (fun i => Meas_dp (qid, i) (cid, i)))
    else None
  | QASM_Meas (qid, Some i) (cid, Some j) => Some [ Meas_dp (qid, i) (cid, j) ]
  | QASM_Meas _ _ => None
  | QASM_Reset (qid, None) =>
    IdMap_find qreg_size qid >>| fun s =>
    list_init s (fun i => Reset_dp (qid, i))
  | QASM_Reset (qid, Some i) => Some [ Reset_dp (qid, i) ]
  end.

Fixpoint desugar_parallel_program
  (qasm_program : qasm_program) (qreg_size : IdMap nat)
  (creg_size : IdMap nat) : option program_dp :=
  match qasm_program with
  | [] => Some []
  | QASM_Qop qop :: tail =>
    desugar_parallel_qop qop qreg_size creg_size >>= fun qop_dp_list =>
    desugar_parallel_program tail qreg_size creg_size >>| fun tail_dp_list =>
    map Qop_dp qop_dp_list ++ tail_dp_list
  | QASM_If cid i_value qop :: tail =>
    desugar_parallel_qop qop qreg_size creg_size >>= fun qop_dp_list =>
    desugar_parallel_program tail qreg_size creg_size >>| fun tail_dp_list =>
    IfList_dp cid i_value qop_dp_list :: tail_dp_list
  | QASM_Decl _ :: t_value
  | QASM_GateDecl _ _ :: t_value
  | QASM_Include _ :: t_value
  | QASM_OpaqueDecl _ :: t_value
  | QASM_Barrier _ :: t_value =>
    desugar_parallel_program t_value qreg_size creg_size
  end.

Definition create_param_map {a : Set}
  (params : list qasm_id) (args : list a) : IdMap a :=
  fold_left
    (fun acc kv => IdMap_add (fst kv) (snd kv) acc)
    (combine params args) IdMap_empty.

Definition instantiate_arg
  (arg_map : IdMap argument_dp) (arg : qasm_argument) : option argument_dp :=
  match arg with
  | (qid, None) => IdMap_find arg_map qid
  | _ => None
  end.

Fixpoint instantiate_exp (exp_map : IdMap qasm_exp) (expr : qasm_exp) : option qasm_exp :=
  match expr with
  | QASM_Id id_expr => IdMap_find exp_map id_expr
  | QASM_BinaryOp b_value e1 e2 =>
    instantiate_exp exp_map e1 >>= fun e1' =>
    instantiate_exp exp_map e2 >>| fun e2' => QASM_BinaryOp b_value e1' e2'
  | QASM_UnaryOp u e =>
    instantiate_exp exp_map e >>| fun e => QASM_UnaryOp u e
  | e => Some e
  end.

Definition instantiate_gop
  (exp_map : IdMap qasm_exp) (arg_map : IdMap argument_dp)
  (operation : qasm_gop) : option (list uop_dp) :=
  match operation with
  | QASM_GUop (QASM_CX arg1 arg2) =>
    instantiate_arg arg_map arg1 >>= fun arg1' =>
    instantiate_arg arg_map arg2 >>| fun arg2' => [ CX_dp arg1' arg2' ]
  | QASM_GUop (QASM_U exp_list arg) =>
    option_l_map (instantiate_exp exp_map) exp_list >>= fun exp_list' =>
    instantiate_arg arg_map arg >>| fun arg' => [ U_dp exp_list' arg' ]
  | QASM_GUop (QASM_Gate id exp_list arg_list) =>
    option_l_map (instantiate_exp exp_map) exp_list >>= fun exp_list' =>
    option_l_map (instantiate_arg arg_map) arg_list >>| fun arg_list' =>
    [ Gate_dp id exp_list' arg_list' ]
  | QASM_GBarrier _ => Some []
  end.

Definition instantiate_gate_decl
  (decl_head : qasm_gatedecl) (decl_body : list qasm_gop)
  (exp_list : list qasm_exp) (arg_list : list argument_dp) : option (list uop_dp) :=
  let '(_, exp_params, arg_params) := decl_head in
  let exp_map := create_param_map exp_params exp_list in
  let arg_map := create_param_map arg_params arg_list in
  decl_body |> option_l_concat_map (instantiate_gop exp_map arg_map).

Definition extract_gate_decl_rev (qasm : qasm_program)
  : list (qasm_gatedecl * list qasm_gop) :=
  let fix helper_rev
    (acc : list (qasm_gatedecl * list qasm_gop))
    (qasm : list qasm_statement)
    : list (qasm_gatedecl * list qasm_gop) :=
    match qasm with
    | [] => acc
    | QASM_GateDecl decl_head decl_body :: tail =>
      helper_rev ((decl_head, decl_body) :: acc) tail
    | _ :: tail => helper_rev acc tail
    end in
  helper_rev [] qasm.

Definition desugar_macro_uop
  (decl_head : qasm_gatedecl) (decl_body : list qasm_gop)
  (op : uop_dp) : option (list uop_dp) :=
  let '(this_id, _, _) := decl_head in
  match op with
  | Gate_dp gate_id exp_list arg_list =>
    if qasm_id_eqb this_id gate_id then
      instantiate_gate_decl decl_head decl_body exp_list arg_list
    else Some [ Gate_dp gate_id exp_list arg_list ]
  | _ => Some [ op ]
  end.

Fixpoint desugar_macro_qop_list
  (decl_head : qasm_gatedecl) (decl_body : list qasm_gop)
  (qop_list : list qop_dp) : option (list qop_dp) :=
  match qop_list with
  | [] => Some []
  | Uop_dp op :: tail =>
    desugar_macro_uop decl_head decl_body op >>| map Uop_dp >>= fun x =>
    desugar_macro_qop_list decl_head decl_body tail >>| fun tail' => x ++ tail'
  | x :: tail =>
    desugar_macro_qop_list decl_head decl_body tail >>| fun tail' => x :: tail'
  end.

Fixpoint desugar_macro_program
  (qasm_dp : program_dp)
  (gate_decls : list (qasm_gatedecl * list qasm_gop)) : option program_dp :=
  let fix inline
    (decl_head : qasm_gatedecl) (decl_body : list qasm_gop)
    (qasm_dp : list statement_dp) : option (list statement_dp) :=
    match qasm_dp with
    | [] => Some []
    | Qop_dp (Uop_dp op) :: tail =>
      desugar_macro_uop decl_head decl_body op
      >>| map (fun x => Qop_dp (Uop_dp x)) >>= fun x =>
      inline decl_head decl_body tail >>| fun tail' => x ++ tail'
    | IfList_dp cid i_value qop_list :: tail =>
      desugar_macro_qop_list decl_head decl_body qop_list >>= fun qop_list' =>
      inline decl_head decl_body tail >>| fun tail' =>
      IfList_dp cid i_value qop_list' :: tail'
    | x :: tail =>
      inline decl_head decl_body tail >>| fun tail' => x :: tail'
    end in
  match gate_decls with
  | [] => Some qasm_dp
  | (decl_head, decl_body) :: tail =>
    inline decl_head decl_body qasm_dp >>= fun qasm_dp' =>
    desugar_macro_program qasm_dp' tail
  end.

Inductive qc_ir : Set :=
| NopIr : qc_ir
| RotateIr : R -> R -> R -> nat -> qc_ir
| CnotIr : nat -> nat -> qc_ir
| MeasureIr : nat -> nat -> qc_ir
| ResetIr : nat -> qc_ir
| SeqIr : qc_ir -> qc_ir -> qc_ir
| IfIr : nat -> bool -> qc_ir -> qc_ir.

Definition QASMArg : Set := qasm_id * nat.

Definition QASMArg_eqb (arg1 arg2 : QASMArg) : bool :=
  let '(id1, i1) := arg1 in
  let '(id2, i2) := arg2 in
  qasm_id_eqb id1 id2 && (i1 =? i2).

Definition QASMArgMap := fun t => list_map QASMArg t.

Definition QASMArgMap_find {t} (map : QASMArgMap t) (key : QASMArg) : option t :=
  lm_find QASMArg_eqb map key.

Definition IntMap := fun t => list_map nat t.

Definition IntMap_find {t} (map : IntMap t) (key : nat) : option t :=
  lm_find Nat.eqb map key.

Definition assign_seq
  (reg_order : list qasm_id)
  (reg_size_map : IdMap nat)
  : option (list (nat * (qasm_id * nat))) :=
  reg_order
  |> option_l_concat_map (fun reg_id =>
    IdMap_find reg_size_map reg_id
    >>| fun reg_size' => list_init reg_size' (fun i => (reg_id, i)))
  >>| mapi (fun i arg => (i, arg)).

Definition assign_arg_int
  (assign_seq : list (nat * (qasm_id * nat))) : QASMArgMap nat :=
  assign_seq |> map (fun '(a, b) => (b, a)).

Definition assign_int_arg
  (assign_seq : list (nat * (qasm_id * nat))) : IntMap QASMArg := assign_seq.

Definition unfold_if
  (creg_size_map : IdMap nat)
  (assingment_c_rev : QASMArgMap nat)
  (creg_id : qasm_id) (cmp : nat) : option (list (nat * bool)) :=
  let fix to_binary (n : nat) (s : nat) : option (list bool) :=
    match (n, s) with
    | (0, _) => Some (list_init s (fun _ => false))
    | (_, 0) => None
    | (S n', S s') => to_binary (Nat.div n 2) s' >>| fun tail' => (Nat.modulo n 2 =? 1) :: tail'
    end in
  IdMap_find creg_size_map creg_id >>= fun reg_size' =>
  list_init reg_size' (fun i => i)
  |> option_l_map (fun i => QASMArgMap_find assingment_c_rev (creg_id, i)) >>= fun cbits' =>
  to_binary cmp reg_size' >>| fun cmp_bits' => combine cbits' cmp_bits'.

Open Scope R_scope.

Fixpoint eval_exp (expr : qasm_exp) : option R :=
  let eval_bop
    (bop : qasm_binaryop) (e1 : qasm_exp) (e2 : qasm_exp) : option R :=
    eval_exp e1 >>= fun e1' =>
    eval_exp e2 >>| fun e2' =>
    match bop with
    | QASM_Plus => e1' + e2'
    | QASM_Minus => e1' - e2'
    | QASM_Times => e1' * e2'
    | QASM_Div => e1' / e2'
    | QASM_Pow => Rpower e1' e2'
    end in
  let eval_uop (uop : qasm_unaryop) (e : qasm_exp) : option R :=
    eval_exp e >>| fun e' =>
    match uop with
    | QASM_Sin => sin e'
    | QASM_Cos => cos e'
    | QASM_Tan => tan e'
    | QASM_Exp => exp e'
    | QASM_Ln => ln e'
    | QASM_Sqrt => R_sqrt.sqrt e'
    | QASM_UMinus => - e'
    end in
  match expr with
  | QASM_Real f => Some f
  | QASM_Nninteger i => Some (IZR i)
  | QASM_Pi => Some PI
  | QASM_Id _ => None
  | QASM_BinaryOp bop e1 e2 => eval_bop bop e1 e2
  | QASM_UnaryOp uop e_value => eval_uop uop e_value
  end.

Close Scope R_scope.

Definition eval_exp_list (exp_list : list qasm_exp) : option (R * R * R) :=
  match exp_list with
  | theta_exp :: phi_exp :: lambda_exp :: [] =>
    eval_exp theta_exp >>= fun theta_exp' =>
    eval_exp phi_exp >>= fun phi_exp' =>
    eval_exp lambda_exp >>| fun lambda_exp' => (theta_exp', phi_exp', lambda_exp')
  | _ => None
  end.

Definition desugar_qasm_qop
  (assignment_q_rev : QASMArgMap nat)
  (assignment_c_rev : QASMArgMap nat) (qasm_qop : qop_dp) : option qc_ir :=
  match qasm_qop with
  | Uop_dp (CX_dp arg1 arg2) =>
    QASMArgMap_find assignment_q_rev arg1 >>= fun arg1' =>
    QASMArgMap_find assignment_q_rev arg2 >>| fun arg2' => CnotIr arg1' arg2'
  | Uop_dp (U_dp exp_list arg) =>
    eval_exp_list exp_list >>= fun '(theta, phi, lambda) =>
    QASMArgMap_find assignment_q_rev arg >>| fun arg' => RotateIr theta phi lambda arg'
  | Meas_dp qarg carg =>
    QASMArgMap_find assignment_q_rev qarg >>= fun qarg' =>
    QASMArgMap_find assignment_c_rev carg >>| fun carg' => MeasureIr qarg' carg'
  | Reset_dp arg =>
    QASMArgMap_find assignment_q_rev arg >>| fun arg' => ResetIr arg'
  | Uop_dp (Gate_dp _ _ _) => None
  end.

Fixpoint desugar_qasm_if (cond_list : list (nat * bool)) (qop_ir : qc_ir)
  : qc_ir :=
  match cond_list with
  | [] => qop_ir
  | (c, b) :: t_value => IfIr c b(desugar_qasm_if t_value qop_ir)
  end.

Fixpoint desugar_qasm_qop_list
  (assignment_q_rev : QASMArgMap nat)
  (assignment_c_rev : QASMArgMap nat) (qop_list : list qop_dp) : option qc_ir :=
  match qop_list with
  | [] => Some NopIr
  | h :: t =>
    desugar_qasm_qop assignment_q_rev assignment_c_rev h >>= fun h' =>
    desugar_qasm_qop_list assignment_q_rev assignment_c_rev t >>| fun t' => SeqIr h' t'
  end.

Fixpoint desugar_qasm_program
  (creg_size_map : IdMap nat)
  (assignment_q_rev : QASMArgMap nat)
  (assignment_c_rev : QASMArgMap nat) (qasm_dm : program_dp) : option qc_ir :=
  match qasm_dm with
  | [] => Some NopIr
  | Qop_dp op :: tail =>
    desugar_qasm_qop assignment_q_rev assignment_c_rev op >>= fun op_ir' =>
    desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev tail >>| fun tail' =>
    SeqIr op_ir' tail'
  | IfList_dp cid comp qop_list :: tail =>
    unfold_if creg_size_map assignment_c_rev cid comp >>= fun cond_list =>
    desugar_qasm_qop_list assignment_q_rev assignment_c_rev qop_list >>= fun qop_ir =>
    desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev tail >>| fun tail' =>
    SeqIr (desugar_qasm_if cond_list qop_ir) tail'
  end.

Fixpoint desugar_qcir_program (qc_ir_program : qc_ir) (acc : nat)
  : Instruction * nat :=
  match qc_ir_program with
  | NopIr => (NopInstr, acc)
  | RotateIr t_value p_value l_value q_value =>
    ((RotateInstr t_value p_value l_value q_value), acc)
  | CnotIr a1 a2 => ((CnotInstr a1 a2), acc)
  | MeasureIr q_value c_value =>
    ((MeasureInstr q_value c_value), acc)
  | ResetIr q_value => ((ResetInstr q_value), acc)
  | SeqIr ir1 ir2 =>
    let '(qc1, acc1) := desugar_qcir_program ir1 acc in
    let '(qc2, acc2) := desugar_qcir_program ir2 acc1 in
    ((SeqInstr qc1 qc2), acc2)
  | IfIr i_value b_value ir =>
    let '(qc1, acc1) := desugar_qcir_program ir acc in
    ((IfInstr i_value b_value qc1), acc1)
  end.

Definition count_bits (size_map : IdMap nat) : nat :=
  fold_left (fun acc kv => acc + snd kv) size_map 0.

Definition ocaml_max_int := 0.

Definition desugar (qasm : qasm_program)
  : option (nat * InlinedProgram * IntMap QASMArg * IntMap QASMArg) :=
  let qreg_order := extract_qreg_order qasm in
  let creg_order := extract_creg_order qasm in
  let qreg_size_map := extract_qreg_size qasm in
  let creg_size_map := extract_creg_size qasm in
  let gate_decls := extract_gate_decl_rev qasm in
  desugar_parallel_program qasm qreg_size_map creg_size_map >>= fun qasm_dp =>
  desugar_macro_program qasm_dp gate_decls >>= fun qasm_dm =>
  assign_seq qreg_order qreg_size_map >>= fun assignment_q_seq =>
  let assignment_q_rev := assign_arg_int assignment_q_seq in
  let assignment_q := assign_int_arg assignment_q_seq in
  assign_seq creg_order creg_size_map >>= fun assignment_c_seq =>
  let assignment_c_rev := assign_arg_int assignment_c_seq in
  let assignment_c := assign_int_arg assignment_c_seq in
  desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev qasm_dm
  >>| fun qasm_core_ir =>
  let num_qbits_tmp := count_bits qreg_size_map in
  let num_cbits := count_bits creg_size_map in
  let '(qasm_core, num_qbits) := desugar_qcir_program qasm_core_ir num_qbits_tmp
    in
  let qc_program :=
    {|IP_num_cbits := num_cbits;
      IP_num_subinstrs := ocaml_max_int;
      IP_instrs := qasm_core; |} in
  (num_qbits, qc_program, assignment_q, assignment_c).

(* Definition desugar_parallel (qasm : OpenQASM2.AST.program) : program_dp :=
  let qreg_size_map := extract_qreg_size qasm in
  let creg_size_map := extract_creg_size qasm in
  desugar_parallel_program qasm qreg_size_map creg_size_map.

Definition desugar_macro (qasm : OpenQASM2.AST.program) : program_dp :=
  let qreg_size_map := extract_qreg_size qasm in
  let creg_size_map := extract_creg_size qasm in
  let gate_decls := extract_gate_decl_rev qasm in
  let qasm_dp := desugar_parallel_program qasm qreg_size_map creg_size_map in
  desugar_macro_program qasm_dp gate_decls.

Definition desugar_qasm (qasm : OpenQASM2.AST.program) : qc_ir :=
  let qreg_order := extract_qreg_order qasm in
  let creg_order := extract_creg_order qasm in
  let qreg_size_map := extract_qreg_size qasm in
  let creg_size_map := extract_creg_size qasm in
  let gate_decls := extract_gate_decl_rev qasm in
  let qasm_dp := desugar_parallel_program qasm qreg_size_map creg_size_map in
  let qasm_dm := desugar_macro_program qasm_dp gate_decls in
  let assignment_q_seq := assign_seq qreg_order qreg_size_map in
  let assignment_q_rev := assign_arg_int assignment_q_seq in
  let assignment_c_seq := assign_seq creg_order creg_size_map in
  let assignment_c_rev := assign_arg_int assignment_c_seq in
  desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev qasm_dm. *)
