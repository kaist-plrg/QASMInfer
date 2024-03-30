open Quantum_core
open OpenQASM2.AST

let ( >>= ) = Option.bind
let ( >>| ) x f = Option.map f x

let option_l_map f =
  List.fold_left
    (fun acc x ->
      f x >>= fun y ->
      acc >>| fun _acc -> y :: _acc)
    (Some [])

let option_l_concat_map f l = option_l_map f l >>| List.concat

let option_s_map f =
  Seq.fold_left
    (fun acc x ->
      f x >>= fun y ->
      acc >>| fun _acc -> Seq.cons y _acc)
    (Some Seq.empty)

let option_s_concat_map f s = option_s_map f s >>| Seq.concat

(*********************************)
(* 1. desugar parallel execution *)
(*********************************)

type argument_dp = id * int

type uop_dp =
  | CX_dp of argument_dp * argument_dp
  | U_dp of exp list * argument_dp
  | Gate_dp of id * exp list * argument_dp list

type qop_dp =
  | Uop_dp of uop_dp
  | Meas_dp of argument_dp * argument_dp
  | Reset_dp of argument_dp

type statement_dp = Qop_dp of qop_dp | IfList_dp of id * int * qop_dp list
type program_dp = statement_dp list

module IdMap = Map.Make (struct
  type t = id

  let compare = compare
end)

let rec extract_qreg_order (qasm_program : program) : id list =
  match qasm_program with
  | [] -> []
  | Decl (QReg (reg_id, _)) :: tail -> reg_id :: extract_qreg_order tail
  | _ :: tail -> extract_qreg_order tail

let rec extract_creg_order (qasm_program : program) : id list =
  match qasm_program with
  | [] -> []
  | Decl (CReg (reg_id, _)) :: tail -> reg_id :: extract_creg_order tail
  | _ :: tail -> extract_creg_order tail

let rec extract_qreg_size (qasm_program : program) : int IdMap.t =
  match qasm_program with
  | [] -> IdMap.empty
  | Decl (QReg (reg_id, reg_size)) :: tail ->
      IdMap.add reg_id reg_size (extract_qreg_size tail)
  | _ :: tail -> extract_qreg_size tail

let rec extract_creg_size (qasm_program : program) : int IdMap.t =
  match qasm_program with
  | [] -> IdMap.empty
  | Decl (CReg (reg_id, reg_size)) :: tail ->
      IdMap.add reg_id reg_size (extract_creg_size tail)
  | _ :: tail -> extract_creg_size tail

(* let get_or_fail key msg map =
   match IdMap.find_opt key map with Some value -> value | None -> failwith msg *)

let rec get_same_elem_opt lst =
  match lst with
  | [] -> Some 1
  | x :: [] -> Some x
  | x :: y :: tl -> if x = y then get_same_elem_opt (y :: tl) else None

let rec index_arg_list (arg_list : argument list) (index : int) :
    argument_dp list =
  match arg_list with
  | [] -> []
  | (qid, None) :: tail -> (qid, index) :: index_arg_list tail index
  | (qid, Some i) :: tail -> (qid, i) :: index_arg_list tail index

let desugar_parallel_arg_list (arg_list : argument list)
    (qreg_size : int IdMap.t) : argument_dp list list option =
  arg_list
  |> option_l_concat_map (fun arg ->
         match arg with
         | qid, None -> IdMap.find_opt qid qreg_size >>| fun s -> [ s ]
         | _ -> Some [])
  >>= get_same_elem_opt
  >>| fun s -> List.init s (fun i -> index_arg_list arg_list i)

let desugar_parallel_uop (operation : uop) (qreg_size : int IdMap.t) :
    uop_dp list option =
  match operation with
  | CX ((qid1, None), (qid2, None)) ->
      IdMap.find_opt qid1 qreg_size >>= fun s1 ->
      IdMap.find_opt qid2 qreg_size >>= fun s2 ->
      if s1 = s2 then
        Some (List.init s1 (fun i -> CX_dp ((qid1, i), (qid2, i))))
      else None
  | CX ((qid1, Some i1), (qid2, Some i2)) ->
      Some [ CX_dp ((qid1, i1), (qid2, i2)) ]
  | CX _ -> None
  | U (exp_list, (qid, None)) ->
      IdMap.find_opt qid qreg_size >>| fun s ->
      List.init s (fun i -> U_dp (exp_list, (qid, i)))
  | U (exp_list, (qid, Some i)) -> Some [ U_dp (exp_list, (qid, i)) ]
  | Gate (gid, exp_list, arg_list) ->
      desugar_parallel_arg_list arg_list qreg_size
      >>| map (fun arg_list_instantiated ->
              Gate_dp (gid, exp_list, arg_list_instantiated))

let desugar_parallel_qop (operation : qop) (qreg_size : int IdMap.t)
    (creg_size : int IdMap.t) : qop_dp list option =
  match operation with
  | Uop uop -> desugar_parallel_uop uop qreg_size >>| map (fun u -> Uop_dp u)
  | Meas ((qid, None), (cid, None)) ->
      IdMap.find_opt qid qreg_size >>= fun s1 ->
      IdMap.find_opt cid creg_size >>= fun s2 ->
      if s1 = s2 then
        Some (List.init s1 (fun i -> Meas_dp ((qid, i), (cid, i))))
      else None
  | Meas ((qid, Some i), (cid, Some j)) -> Some [ Meas_dp ((qid, i), (cid, j)) ]
  | Meas _ -> None
  | Reset (qid, None) ->
      IdMap.find_opt qid qreg_size >>| fun s ->
      List.init s (fun i -> Reset_dp (qid, i))
  | Reset (qid, Some i) -> Some [ Reset_dp (qid, i) ]

let rec desugar_parallel_program (qasm_program : program)
    (qreg_size : int IdMap.t) (creg_size : int IdMap.t) : program_dp option =
  match qasm_program with
  | [] -> Some []
  | Qop qop :: tail ->
      desugar_parallel_qop qop qreg_size creg_size >>= fun qop_dp_list ->
      desugar_parallel_program tail qreg_size creg_size >>| fun tail_dp_list ->
      map (fun o -> Qop_dp o) qop_dp_list @ tail_dp_list
  | If (cid, i, qop) :: tail ->
      desugar_parallel_qop qop qreg_size creg_size >>= fun qop_dp_list ->
      desugar_parallel_program tail qreg_size creg_size >>| fun tail_dp_list ->
      IfList_dp (cid, i, qop_dp_list) :: tail_dp_list
  | Decl _ :: t
  | GateDecl _ :: t
  | Include _ :: t
  | OpaqueDecl _ :: t
  | Barrier _ :: t ->
      desugar_parallel_program t qreg_size creg_size

(****************************************)
(* 2. desugar gate subroutines (macros) *)
(****************************************)

let create_param_map (params : id list) (args : 'a list) : 'a IdMap.t =
  List.combine params args
  |> List.fold_left (fun acc (k, v) -> IdMap.add k v acc) IdMap.empty

let instantiate_arg (arg_map : argument_dp IdMap.t) (arg : argument) :
    argument_dp option =
  match arg with qid, None -> IdMap.find_opt qid arg_map | _ -> None

let rec instantiate_exp (exp_map : exp IdMap.t) (expr : exp) : exp option =
  match expr with
  | Id id_expr -> IdMap.find_opt id_expr exp_map
  | BinaryOp (b, e1, e2) ->
      instantiate_exp exp_map e1 >>= fun _e1 ->
      instantiate_exp exp_map e2 >>| fun _e2 -> BinaryOp (b, _e1, _e2)
  | UnaryOp (u, e) -> instantiate_exp exp_map e >>| fun _e -> UnaryOp (u, _e)
  | e -> Some e

let instantiate_gop (exp_map : exp IdMap.t) (arg_map : argument_dp IdMap.t)
    (operation : gop) : uop_dp list option =
  match operation with
  | GUop (CX (arg1, arg2)) ->
      instantiate_arg arg_map arg1 >>= fun _arg1 ->
      instantiate_arg arg_map arg2 >>| fun _arg2 -> [ CX_dp (_arg1, _arg2) ]
  | GUop (U (exp_list, arg)) ->
      option_l_map (instantiate_exp exp_map) exp_list >>= fun _exp_list ->
      instantiate_arg arg_map arg >>| fun _arg -> [ U_dp (_exp_list, _arg) ]
  | GUop (Gate (id, exp_list, arg_list)) ->
      option_l_map (instantiate_exp exp_map) exp_list >>= fun _exp_list ->
      option_l_map (instantiate_arg arg_map) arg_list >>| fun _arg_list ->
      [ Gate_dp (id, _exp_list, _arg_list) ]
  | GBarrier _ -> Some []

let instantiate_gate_decl (decl_head : gatedecl) (decl_body : gop list)
    (exp_list : exp list) (arg_list : argument_dp list) : uop_dp list option =
  let _, exp_params, arg_params = decl_head in
  let exp_map = create_param_map exp_params exp_list in
  let arg_map = create_param_map arg_params arg_list in
  decl_body |> option_l_concat_map (instantiate_gop exp_map arg_map)

let extract_gate_decl_rev (qasm : program) : (gatedecl * gop list) list =
  let rec helper_rev acc qasm =
    match qasm with
    | [] -> acc
    | GateDecl (decl_head, decl_body) :: tail ->
        helper_rev ((decl_head, decl_body) :: acc) tail
    | _ :: tail -> helper_rev acc tail
  in
  helper_rev [] qasm

let desugar_macro_uop (decl_head : gatedecl) (decl_body : gop list)
    (op : uop_dp) : uop_dp list option =
  let this_id, _, _ = decl_head in
  match op with
  | Gate_dp (gate_id, exp_list, arg_list) when gate_id = this_id ->
      instantiate_gate_decl decl_head decl_body exp_list arg_list
  | x -> Some [ x ]

let rec desugar_macro_qop_list (decl_head : gatedecl) (decl_body : gop list)
    (qop_list : qop_dp list) : qop_dp list option =
  match qop_list with
  | [] -> Some []
  | Uop_dp op :: tail ->
      desugar_macro_uop decl_head decl_body op >>| map (fun x -> Uop_dp x)
      >>= fun x ->
      desugar_macro_qop_list decl_head decl_body tail >>| fun _tail ->
      List.append x _tail
  | x :: tail ->
      desugar_macro_qop_list decl_head decl_body tail >>| fun _tail ->
      x :: _tail

let rec desugar_macro_program (qasm_dp : program_dp)
    (gate_decls : (gatedecl * gop list) list) : program_dp option =
  let rec inline decl_head decl_body qasm_dp =
    match qasm_dp with
    | [] -> Some []
    | Qop_dp (Uop_dp op) :: tail ->
        desugar_macro_uop decl_head decl_body op
        >>| map (fun x -> Qop_dp (Uop_dp x))
        >>= fun x ->
        inline decl_head decl_body tail >>| fun _tail -> List.append x _tail
    | IfList_dp (cid, i, qop_list) :: tail ->
        desugar_macro_qop_list decl_head decl_body qop_list >>= fun _qop_list ->
        inline decl_head decl_body tail >>| fun _tail ->
        IfList_dp (cid, i, _qop_list) :: _tail
    | x :: tail -> inline decl_head decl_body tail >>| fun _tail -> x :: _tail
  in
  match gate_decls with
  | [] -> Some qasm_dp
  | (decl_head, decl_body) :: tail ->
      inline decl_head decl_body qasm_dp >>= fun _qasm_dp ->
      desugar_macro_program _qasm_dp tail

(**********************************)
(* 3. assign (q)bits in registers *)
(**********************************)

type qc_ir =
  | NopIr
  | RotateIr of
      RbaseSymbolsImpl.coq_R
      * RbaseSymbolsImpl.coq_R
      * RbaseSymbolsImpl.coq_R
      * int
  | CnotIr of int * int
  | MeasureIr of int * int
  | ResetIr of int
  | SeqIr of qc_ir * qc_ir
  | IfIr of int * bool * qc_ir

module QASMArg = struct
  type t = id * int

  let compare (s1, i1) (s2, i2) =
    match compare s1 s2 with 0 -> compare i1 i2 | c -> c
end

module QASMArgMap = Map.Make (QASMArg)

module IntMap = Map.Make (struct
  type t = int

  let compare = compare
end)

(* assigned * regname * regindex *)
let assign_seq (reg_order : id list) (reg_size_map : int IdMap.t) :
    (int * (id * int)) Seq.t option =
  reg_order |> List.to_seq
  |> option_s_concat_map (fun reg_id ->
         IdMap.find_opt reg_id reg_size_map >>| fun _reg_size ->
         Seq.init _reg_size (fun i -> (reg_id, i)))
  >>| Seq.mapi (fun i arg -> (i, arg))

let assign_arg_int (assign_seq : (int * (id * int)) Seq.t) : int QASMArgMap.t =
  assign_seq |> Seq.map (fun (a, b) -> (b, a)) |> QASMArgMap.of_seq

let assign_int_arg (assign_seq : (int * (id * int)) Seq.t) : QASMArg.t IntMap.t
    =
  IntMap.of_seq assign_seq

let unfold_if (creg_size_map : int IdMap.t)
    (assingment_c_rev : int QASMArgMap.t) (creg_id : id) (cmp : int) :
    (int * bool) list option =
  let rec to_binary n s =
    match (n, s) with
    | 0, _ -> Some (List.init s (fun _ -> false))
    | _, 0 -> None
    | _, _ -> to_binary (n / 2) (s - 1) >>| fun _bits -> (n mod 2 = 1) :: _bits
  in
  IdMap.find_opt creg_id creg_size_map >>= fun _reg_size ->
  List.init _reg_size (fun i -> i)
  |> option_l_map (fun i -> QASMArgMap.find_opt (creg_id, i) assingment_c_rev)
  >>= fun _cbits ->
  to_binary cmp _reg_size >>| fun _cmp_bits -> List.combine _cbits _cmp_bits

let rec eval_exp (expr : exp) : float option =
  match expr with
  | Real f -> Some f
  | Nninteger i -> Some (Int.to_float i)
  | Pi -> Some Float.pi
  | Id _ -> None
  | BinaryOp (bop, e1, e2) -> eval_bop bop e1 e2
  | UnaryOp (uop, e) -> eval_uop uop e

and eval_bop (bop : binaryop) (e1 : exp) (e2 : exp) : float option =
  eval_exp e1 >>= fun _e1 ->
  eval_exp e2 >>| fun _e2 ->
  match bop with
  | Plus -> _e1 +. _e2
  | Minus -> _e1 -. _e2
  | Times -> _e1 *. _e2
  | Div -> _e1 /. _e2
  | Pow -> _e1 ** _e2

and eval_uop (uop : unaryop) (e : exp) : float option =
  eval_exp e >>| fun _e ->
  match uop with
  | Sin -> Float.sin _e
  | Cos -> Float.cos _e
  | Tan -> Float.tan _e
  | Exp -> Float.exp _e
  | Ln -> Float.log _e
  | Sqrt -> Float.sqrt _e
  | UMinus -> -._e

let eval_exp_list (exp_list : exp list) : (float * float * float) option =
  match exp_list with
  | [ theta_exp; phi_exp; lambda_exp ] ->
      eval_exp theta_exp >>= fun _theta_exp ->
      eval_exp phi_exp >>= fun _phi_exp ->
      eval_exp lambda_exp >>| fun _lambda_exp ->
      (_theta_exp, _phi_exp, _lambda_exp)
  | _ -> None

let float_to_R = RbaseSymbolsImpl.coq_Rabst

let desugar_qasm_qop (assignment_q_rev : int QASMArgMap.t)
    (assignment_c_rev : int QASMArgMap.t) (qasm_qop : qop_dp) : qc_ir option =
  match qasm_qop with
  | Uop_dp (CX_dp (arg1, arg2)) ->
      QASMArgMap.find_opt arg1 assignment_q_rev >>= fun _arg1 ->
      QASMArgMap.find_opt arg2 assignment_q_rev >>| fun _arg2 ->
      CnotIr (_arg1, _arg2)
  | Uop_dp (U_dp (exp_list, arg)) ->
      eval_exp_list exp_list >>= fun (theta, phi, lambda) ->
      QASMArgMap.find_opt arg assignment_q_rev >>| fun _arg ->
      RotateIr (float_to_R theta, float_to_R phi, float_to_R lambda, _arg)
  | Meas_dp (qarg, carg) ->
      QASMArgMap.find_opt qarg assignment_q_rev >>= fun _qarg ->
      QASMArgMap.find_opt carg assignment_c_rev >>| fun _carg ->
      MeasureIr (_qarg, _carg)
  | Reset_dp arg ->
      QASMArgMap.find_opt arg assignment_q_rev >>| fun _arg -> ResetIr _arg
  | Uop_dp (Gate_dp (_, _, _)) -> None

let rec desugar_qasm_if (cond_list : (int * bool) list) (qop_ir : qc_ir) : qc_ir
    =
  match cond_list with
  | [] -> qop_ir
  | (c, b) :: t -> IfIr (c, b, desugar_qasm_if t qop_ir)

let rec desugar_qasm_qop_list (assignment_q_rev : int QASMArgMap.t)
    (assignment_c_rev : int QASMArgMap.t) (qop_list : qop_dp list) :
    qc_ir option =
  match qop_list with
  | [] -> Some NopIr
  | h :: t ->
      desugar_qasm_qop assignment_q_rev assignment_c_rev h >>= fun _h ->
      desugar_qasm_qop_list assignment_q_rev assignment_c_rev t >>| fun _t ->
      SeqIr (_h, _t)

let rec desugar_qasm_program (creg_size_map : int IdMap.t)
    (assignment_q_rev : int QASMArgMap.t) (assignment_c_rev : int QASMArgMap.t)
    (qasm_dm : program_dp) : qc_ir option =
  match qasm_dm with
  | [] -> Some NopIr
  | Qop_dp op :: tail ->
      desugar_qasm_qop assignment_q_rev assignment_c_rev op >>= fun _op_ir ->
      desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev tail
      >>| fun _tail -> SeqIr (_op_ir, _tail)
  | IfList_dp (cid, comp, qop_list) :: tail ->
      unfold_if creg_size_map assignment_c_rev cid comp >>= fun cond_list ->
      desugar_qasm_qop_list assignment_q_rev assignment_c_rev qop_list
      >>= fun qop_ir ->
      desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev tail
      >>| fun _tail -> SeqIr (desugar_qasm_if cond_list qop_ir, _tail)

(********************************************)
(* 4. DEPRECATED: desugar reset instruction *)
(********************************************)

let rec desugar_qcir_program (qc_ir_program : qc_ir) (acc : int) :
    instruction * int =
  match qc_ir_program with
  | NopIr -> (NopInstr, acc)
  | RotateIr (t, p, l, q) -> (RotateInstr (t, p, l, q), acc)
  | CnotIr (a1, a2) -> (CnotInstr (a1, a2), acc)
  | MeasureIr (q, c) -> (MeasureInstr (q, c), acc)
  | ResetIr q -> (ResetInstr q, acc)
  | SeqIr (ir1, ir2) ->
      let qc1, acc1 = desugar_qcir_program ir1 acc in
      let qc2, acc2 = desugar_qcir_program ir2 acc1 in
      (SeqInstr (qc1, qc2), acc2)
  | IfIr (i, b, ir) ->
      let qc1, acc1 = desugar_qcir_program ir acc in
      (IfInstr (i, b, qc1), acc1)

let count_bits (size_map : int IdMap.t) : int =
  IdMap.fold (fun _ s a -> s + a) size_map 0

let desugar qasm =
  let qreg_order = extract_qreg_order qasm in
  let creg_order = extract_creg_order qasm in
  let qreg_size_map = extract_qreg_size qasm in
  let creg_size_map = extract_creg_size qasm in
  let gate_decls = extract_gate_decl_rev qasm in
  desugar_parallel_program qasm qreg_size_map creg_size_map >>= fun qasm_dp ->
  desugar_macro_program qasm_dp gate_decls >>= fun qasm_dm ->
  assign_seq qreg_order qreg_size_map >>= fun assignment_q_seq ->
  let assignment_q_rev = assign_arg_int assignment_q_seq in
  let assignment_q = assign_int_arg assignment_q_seq in
  assign_seq creg_order creg_size_map >>= fun assignment_c_seq ->
  let assignment_c_rev = assign_arg_int assignment_c_seq in
  let assignment_c = assign_int_arg assignment_c_seq in
  desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev qasm_dm
  >>| fun qasm_core_ir ->
  let num_qbits_tmp = count_bits qreg_size_map in
  let num_cbits = count_bits creg_size_map in
  let qasm_core, num_qbits = desugar_qcir_program qasm_core_ir num_qbits_tmp in
  let qc_program : inlinedProgram =
    {
      iP_num_cbits = num_cbits;
      iP_num_subinstrs = Int.max_int;
      iP_instrs = qasm_core;
    }
  in
  (num_qbits, qc_program, assignment_q, assignment_c)

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
