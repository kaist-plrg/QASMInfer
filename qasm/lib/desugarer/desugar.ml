open Quantum_core
open OpenQASM2.AST

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

let get_or_fail key msg map =
  match IdMap.find_opt key map with Some value -> value | None -> failwith msg

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
    (qreg_size : int IdMap.t) : argument_dp list list =
  let reg_size_list =
    arg_list
    |> List.filter_map (function
         | qid, None ->
             Some
               (get_or_fail qid "desugar_parallel_arg_list: invalid id"
                  qreg_size)
         | _ -> None)
  in
  let reg_size_opt = get_same_elem_opt reg_size_list in
  match reg_size_opt with
  | Some s -> List.init s (fun i -> index_arg_list arg_list i)
  | None -> failwith "desugar_parallel_arg_list: invalid register size"

let desugar_parallel_uop (operation : uop) (qreg_size : int IdMap.t) :
    uop_dp list =
  match operation with
  | CX ((qid1, None), (qid2, None)) -> (
      match (IdMap.find_opt qid1 qreg_size, IdMap.find_opt qid2 qreg_size) with
      | Some s1, Some s2 ->
          if s1 == s2 then List.init s1 (fun i -> CX_dp ((qid1, i), (qid2, i)))
          else failwith "desugar_parallel_uop: invalid register size"
      | _ -> failwith "invalid id")
  | CX ((qid1, Some i1), (qid2, Some i2)) -> [ CX_dp ((qid1, i1), (qid2, i2)) ]
  | CX _ -> failwith "deguar_parallel_uop: Invalid CX usage"
  | U (exp_list, (qid, None)) -> (
      match IdMap.find_opt qid qreg_size with
      | Some s -> List.init s (fun i -> U_dp (exp_list, (qid, i)))
      | None -> failwith "desugar_parallel_uop: invalid id")
  | U (exp_list, (qid, Some i)) -> [ U_dp (exp_list, (qid, i)) ]
  | Gate (gid, exp_list, arg_list) ->
      desugar_parallel_arg_list arg_list qreg_size
      |> map (fun arg_list_instantiated ->
             Gate_dp (gid, exp_list, arg_list_instantiated))

let desugar_parallel_qop (operation : qop) (qreg_size : int IdMap.t)
    (creg_size : int IdMap.t) : qop_dp list =
  match operation with
  | Uop uop -> map (fun u -> Uop_dp u) (desugar_parallel_uop uop qreg_size)
  | Meas ((qid, None), (cid, None)) -> (
      match (IdMap.find_opt qid qreg_size, IdMap.find_opt cid creg_size) with
      | Some s1, Some s2 ->
          if s1 == s2 then List.init s1 (fun i -> Meas_dp ((qid, i), (cid, i)))
          else failwith "invalid register size"
      | _ -> failwith "invalid id")
  | Meas ((qid, Some i), (cid, Some j)) -> [ Meas_dp ((qid, i), (cid, j)) ]
  | Meas _ -> failwith "invalid measure usage"
  | Reset (qid, None) -> (
      match IdMap.find_opt qid qreg_size with
      | Some s -> List.init s (fun i -> Reset_dp (qid, i))
      | None -> failwith "invalid id")
  | Reset (qid, Some i) -> [ Reset_dp (qid, i) ]

let rec desugar_parallel_program (qasm_program : program)
    (qreg_size : int IdMap.t) (creg_size : int IdMap.t) : program_dp =
  match qasm_program with
  | [] -> []
  | Qop qop :: tail ->
      map (fun o -> Qop_dp o) (desugar_parallel_qop qop qreg_size creg_size)
      @ desugar_parallel_program tail qreg_size creg_size
  | If (cid, i, qop) :: tail ->
      IfList_dp (cid, i, desugar_parallel_qop qop qreg_size creg_size)
      :: desugar_parallel_program tail qreg_size creg_size
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
    argument_dp =
  match arg with
  | qid, None ->
      get_or_fail qid ("unbound id " ^ qid ^ " in gate declaration") arg_map
  | _ -> failwith "invalid gate declaration"

let rec instantiate_exp (exp_map : exp IdMap.t) (expr : exp) : exp =
  match expr with
  | Id id_expr ->
      get_or_fail id_expr
        ("unbound id " ^ id_expr ^ " in gate declaration")
        exp_map
  | BinaryOp (b, e1, e2) ->
      BinaryOp (b, instantiate_exp exp_map e1, instantiate_exp exp_map e2)
  | UnaryOp (u, e) -> UnaryOp (u, instantiate_exp exp_map e)
  | e -> e

let instantiate_gop (exp_map : exp IdMap.t) (arg_map : argument_dp IdMap.t)
    (operation : gop) : uop_dp option =
  match operation with
  | GUop (CX (arg1, arg2)) ->
      Some (CX_dp (instantiate_arg arg_map arg1, instantiate_arg arg_map arg2))
  | GUop (U (exp_list, arg)) ->
      Some
        (U_dp
           (map (instantiate_exp exp_map) exp_list, instantiate_arg arg_map arg))
  | GUop (Gate (id, exp_list, arg_list)) ->
      Some
        (Gate_dp
           ( id,
             map (instantiate_exp exp_map) exp_list,
             map (instantiate_arg arg_map) arg_list ))
  | GBarrier _ -> None

let instantiate_gate_decl (decl_head : gatedecl) (decl_body : gop list)
    (exp_list : exp list) (arg_list : argument_dp list) : uop_dp list =
  let _, exp_params, arg_params = decl_head in
  let exp_map = create_param_map exp_params exp_list in
  let arg_map = create_param_map arg_params arg_list in
  decl_body |> List.filter_map (instantiate_gop exp_map arg_map)

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
    (op : uop_dp) : uop_dp list =
  let this_id, _, _ = decl_head in
  match op with
  | Gate_dp (gate_id, exp_list, arg_list) when gate_id = this_id ->
      instantiate_gate_decl decl_head decl_body exp_list arg_list
  | x -> [ x ]

let rec desugar_macro_qop_list (decl_head : gatedecl) (decl_body : gop list)
    (qop_list : qop_dp list) : qop_dp list =
  match qop_list with
  | [] -> []
  | Uop_dp op :: tail ->
      desugar_macro_uop decl_head decl_body op |> map (fun x -> Uop_dp x)
      |> fun x ->
      List.append x (desugar_macro_qop_list decl_head decl_body tail)
  | x :: tail -> x :: desugar_macro_qop_list decl_head decl_body tail

let rec desugar_macro_program (qasm_dp : program_dp)
    (gate_decls : (gatedecl * gop list) list) : program_dp =
  let rec inline decl_head decl_body qasm_dp =
    match qasm_dp with
    | [] -> []
    | Qop_dp (Uop_dp op) :: tail ->
        desugar_macro_uop decl_head decl_body op
        |> map (fun x -> Qop_dp (Uop_dp x))
        |> fun x -> List.append x (inline decl_head decl_body tail)
    | IfList_dp (cid, i, qop_list) :: tail ->
        IfList_dp (cid, i, desugar_macro_qop_list decl_head decl_body qop_list)
        :: inline decl_head decl_body tail
    | x :: tail -> x :: inline decl_head decl_body tail
  in
  match gate_decls with
  | [] -> qasm_dp
  | (decl_head, decl_body) :: tail ->
      desugar_macro_program (inline decl_head decl_body qasm_dp) tail

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

let assign_seq (reg_order : id list) (reg_size_map : int IdMap.t) :
    (int * (id * int)) Seq.t =
  reg_order |> List.to_seq
  |> Seq.flat_map (fun reg_id ->
         Seq.init (get_or_fail reg_id "assign_seq: invalid id" reg_size_map)
           (fun i -> (reg_id, i)))
  |> Seq.mapi (fun i arg -> (i, arg))

let assign_arg_int (assign_seq : (int * (id * int)) Seq.t) : int QASMArgMap.t =
  assign_seq |> Seq.map (fun (a, b) -> (b, a)) |> QASMArgMap.of_seq

let assign_int_arg (assign_seq : (int * (id * int)) Seq.t) : QASMArg.t IntMap.t
    =
  IntMap.of_seq assign_seq

let deref_or_fail key msg map =
  match QASMArgMap.find_opt key map with
  | Some value -> value
  | None -> failwith msg

let unfold_if (creg_size_map : int IdMap.t)
    (assingment_c_rev : int QASMArgMap.t) (creg_id : id) (cmp : int) :
    (int * bool) list =
  let rec to_binary n s =
    if n = 0 then List.init s (fun _ -> false)
    else (n mod 2 = 1) :: to_binary (n / 2) (s - 1)
  in
  let reg_size = get_or_fail creg_id "invalid creg id" creg_size_map in
  let cbits =
    List.init reg_size (fun i ->
        deref_or_fail (creg_id, i) "unfold_if: invalid argument"
          assingment_c_rev)
  in
  List.combine cbits (to_binary cmp reg_size)

let rec eval_exp (expr : exp) : float =
  match expr with
  | Real f -> f
  | Nninteger i -> Int.to_float i
  | Pi -> Float.pi
  | Id _ -> failwith "cannot eval id"
  | BinaryOp (bop, e1, e2) -> eval_bop bop e1 e2
  | UnaryOp (uop, e) -> eval_uop uop e

and eval_bop (bop : binaryop) (e1 : exp) (e2 : exp) : float =
  match bop with
  | Plus -> eval_exp e1 +. eval_exp e2
  | Minus -> eval_exp e1 -. eval_exp e2
  | Times -> eval_exp e1 *. eval_exp e2
  | Div -> eval_exp e1 /. eval_exp e2
  | Pow -> eval_exp e1 ** eval_exp e2

and eval_uop (uop : unaryop) (e : exp) : float =
  match uop with
  | Sin -> Float.sin (eval_exp e)
  | Cos -> Float.cos (eval_exp e)
  | Tan -> Float.tan (eval_exp e)
  | Exp -> Float.exp (eval_exp e)
  | Ln -> Float.log (eval_exp e)
  | Sqrt -> Float.sqrt (eval_exp e)
  | UMinus -> -.eval_exp e

let eval_exp_list (exp_list : exp list) : float * float * float =
  match exp_list with
  | [ theta_exp; phi_exp; lambda_exp ] ->
      (eval_exp theta_exp, eval_exp phi_exp, eval_exp lambda_exp)
  | _ -> failwith "invalid exp list length"

let float_to_R = RbaseSymbolsImpl.coq_Rabst

let desugar_qasm_qop (assignment_q_rev : int QASMArgMap.t)
    (assignment_c_rev : int QASMArgMap.t) (qasm_qop : qop_dp) : qc_ir =
  match qasm_qop with
  | Uop_dp (CX_dp (arg1, arg2)) ->
      CnotIr
        ( deref_or_fail arg1 "desugar_qasm_qop: CX: invalid argument"
            assignment_q_rev,
          deref_or_fail arg2 "desugar_qasm_qop: CX: invalid argument"
            assignment_q_rev )
  | Uop_dp (U_dp (exp_list, arg)) ->
      let theta, phi, lambda = eval_exp_list exp_list in
      RotateIr
        ( float_to_R theta,
          float_to_R phi,
          float_to_R lambda,
          deref_or_fail arg "desugar_qasm_qop: U: invalid argument"
            assignment_q_rev )
  | Meas_dp (qarg, carg) ->
      MeasureIr
        ( deref_or_fail qarg "desugar_qasm_qop: invalid argument"
            assignment_q_rev,
          deref_or_fail carg "desugar_qasm_qop: invalid argument"
            assignment_c_rev )
  | Reset_dp arg ->
      ResetIr
        (deref_or_fail arg "desugar_qasm_qop: invalid argument" assignment_q_rev)
  | Uop_dp (Gate_dp (gate_id, _, _)) ->
      failwith ("macro gate " ^ gate_id ^ " is not inlined")

let rec desugar_qasm_if (cond_list : (int * bool) list) (qop_ir : qc_ir) : qc_ir
    =
  match cond_list with
  | [] -> qop_ir
  | (c, b) :: t -> IfIr (c, b, desugar_qasm_if t qop_ir)

let rec desugar_qasm_qop_list (assignment_q_rev : int QASMArgMap.t)
    (assignment_c_rev : int QASMArgMap.t) (qop_list : qop_dp list) : qc_ir =
  match qop_list with
  | [] -> NopIr
  | h :: t ->
      SeqIr
        ( desugar_qasm_qop assignment_q_rev assignment_c_rev h,
          desugar_qasm_qop_list assignment_q_rev assignment_c_rev t )

let rec desugar_qasm_program (creg_size_map : int IdMap.t)
    (assignment_q_rev : int QASMArgMap.t) (assignment_c_rev : int QASMArgMap.t)
    (qasm_dm : program_dp) : qc_ir =
  match qasm_dm with
  | [] -> NopIr
  | Qop_dp op :: tail ->
      SeqIr
        ( desugar_qasm_qop assignment_q_rev assignment_c_rev op,
          desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev
            tail )
  | IfList_dp (cid, comp, qop_list) :: tail ->
      let cond_list = unfold_if creg_size_map assignment_c_rev cid comp in
      let qop_ir =
        desugar_qasm_qop_list assignment_q_rev assignment_c_rev qop_list
      in
      SeqIr
        ( desugar_qasm_if cond_list qop_ir,
          desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev
            tail )

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
  let qasm_dp = desugar_parallel_program qasm qreg_size_map creg_size_map in
  let qasm_dm = desugar_macro_program qasm_dp gate_decls in
  let assignment_q_seq = assign_seq qreg_order qreg_size_map in
  let assignment_q_rev = assign_arg_int assignment_q_seq in
  let assignment_q = assign_int_arg assignment_q_seq in
  let assignment_c_seq = assign_seq creg_order creg_size_map in
  let assignment_c_rev = assign_arg_int assignment_c_seq in
  let assignment_c = assign_int_arg assignment_c_seq in
  let qasm_core_ir =
    desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev qasm_dm
  in
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

let desugar_parallel qasm =
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
  desugar_qasm_program creg_size_map assignment_q_rev assignment_c_rev qasm_dm
