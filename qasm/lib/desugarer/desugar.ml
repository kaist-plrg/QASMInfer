open Quantum_core
open OpenQASM2.OpenQASM
open OpenQASM2.AST

(* 1. desugar parallel execution *)

type stmt_desugar_par =
  | Decl of decl
  | GateDecl of gatedecl * gop list
  | Qop of qop
  | IfList of id * int * qop list

type prgm_desugar_par = stmt_desugar_par list

module RegSizeMap = Map.Make (struct
  type t = id

  let compare = compare
end)

let rec extract_qreg_size (qasm_program : program) : int RegSizeMap.t =
  match qasm_program with
  | [] -> RegSizeMap.empty
  | Decl (QReg (reg_id, reg_size)) :: tail ->
      RegSizeMap.add reg_id reg_size (extract_qreg_size tail)
  | _ :: tail -> extract_qreg_size tail

let rec extract_creg_size (qasm_program : program) : int RegSizeMap.t =
  match qasm_program with
  | [] -> RegSizeMap.empty
  | Decl (CReg (reg_id, reg_size)) :: tail ->
      RegSizeMap.add reg_id reg_size (extract_creg_size tail)
  | _ :: tail -> extract_creg_size tail

let get_or_fail key msg map =
  match RegSizeMap.find_opt key map with
  | Some value -> value
  | None -> failwith msg

let rec get_same_elem_opt lst =
  match lst with
  | [] -> None
  | x :: [] -> Some x
  | x :: y :: tl -> if x = y then get_same_elem_opt (y :: tl) else None

let rec instantiate_arg_list (arg_list : argument list) (index : int) :
    argument list =
  match arg_list with
  | [] -> []
  | (qid, None) :: tail -> (qid, Some index) :: instantiate_arg_list tail index
  | h :: tail -> h :: instantiate_arg_list tail index

let desugar_parallel_arg_list (arg_list : argument list)
    (qreg_size : int RegSizeMap.t) : argument list list =
  let reg_size_list =
    arg_list
    |> List.filter_map (function
         | qid, None -> Some (get_or_fail qid "invalid id" qreg_size)
         | _ -> None)
  in
  let reg_size_opt = get_same_elem_opt reg_size_list in
  match reg_size_opt with
  | Some s -> List.init s (fun i -> instantiate_arg_list arg_list i)
  | None -> failwith "invalid register size"

let desugar_parallel_qop (operation : qop) (qreg_size : int RegSizeMap.t)
    (creg_size : int RegSizeMap.t) : qop list =
  match operation with
  | Uop (CX ((qid1, None), (qid2, None))) -> (
      match
        (RegSizeMap.find_opt qid1 qreg_size, RegSizeMap.find_opt qid2 qreg_size)
      with
      | Some s1, Some s2 ->
          if s1 == s2 then
            List.init s1 (fun i -> Uop (CX ((qid1, Some i), (qid2, Some i))))
          else failwith "invalid register size"
      | _ -> failwith "invalid id")
  | Uop (U (exp_list, (qid, None))) -> (
      match RegSizeMap.find_opt qid qreg_size with
      | Some s -> List.init s (fun i -> Uop (U (exp_list, (qid, Some i))))
      | None -> failwith "invalid id")
  | Uop (Gate (gid, exp_list, arg_list)) ->
      desugar_parallel_arg_list arg_list qreg_size
      |> map (fun arg_list_instantiated ->
             Uop (Gate (gid, exp_list, arg_list_instantiated)))
  | Meas ((qid, None), (cid, None)) -> (
      match
        (RegSizeMap.find_opt qid qreg_size, RegSizeMap.find_opt cid creg_size)
      with
      | Some s1, Some s2 ->
          if s1 == s2 then
            List.init s1 (fun i -> Meas ((qid, Some i), (cid, Some i)))
          else failwith "invalid register size"
      | _ -> failwith "invalid id")
  | Reset (qid, None) -> (
      match RegSizeMap.find_opt qid qreg_size with
      | Some s -> List.init s (fun i -> Reset (qid, Some i))
      | None -> failwith "invalid id")
  | x -> [ x ]

let rec desugar_parallel_program (qasm_program : program)
    (qreg_size : int RegSizeMap.t) (creg_size : int RegSizeMap.t) :
    prgm_desugar_par =
  match qasm_program with
  | [] -> []
  | Qop qop :: tail ->
      map (fun o -> Qop o) (desugar_parallel_qop qop qreg_size creg_size)
      @ desugar_parallel_program tail qreg_size creg_size
  | If (cid, i, qop) :: tail ->
      IfList (cid, i, desugar_parallel_qop qop qreg_size creg_size)
      :: desugar_parallel_program tail qreg_size creg_size
  | Decl d :: t -> Decl d :: desugar_parallel_program t qreg_size creg_size
  | GateDecl (d, g) :: t ->
      GateDecl (d, g) :: desugar_parallel_program t qreg_size creg_size
  | Include _ :: t | OpaqueDecl _ :: t | Barrier _ :: t ->
      desugar_parallel_program t qreg_size creg_size

type qc_ir =
  | NopInter
  | RotateInter of
      RbaseSymbolsImpl.coq_R
      * RbaseSymbolsImpl.coq_R
      * RbaseSymbolsImpl.coq_R
      * int
  | CnotInter of int * int
  | MeasureInter of int * int
  | ResetInter of int * qc_ir
  | SeqInter of qc_ir * qc_ir
  | IfInter of int * bool * qc_ir

module QASMqubit = struct
  type t = string * int

  let compare (s1, i1) (s2, i2) =
    match compare s1 s2 with 0 -> compare i1 i2 | c -> c
end

module QubitMap = Map.Make (QASMqubit)

let extract_qubit_map (qasm_program : program) : int QubitMap.t =
  failwith "not implemented"
