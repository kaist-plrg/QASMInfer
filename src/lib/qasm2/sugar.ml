open Ast
open Extracted

module IntMap = Desugar.IntMap
module StringSet = Set.Make (String)

type register = {
  name : string;
  size : int;
}

type assignment_kind = Quantum | Classical

let ( let* ) result f = Result.bind result f

let kind_name = function Quantum -> "quantum" | Classical -> "classical"

let is_identifier_start = function
  | 'a' .. 'z' | '_' -> true
  | _ -> false

let is_identifier_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

let reserved_identifiers =
  [ "barrier"; "cos"; "creg"; "exp"; "gate"; "if"; "include"; "ln";
    "measure"; "opaque"; "pi"; "qreg"; "reset"; "sin"; "sqrt";
    "tan" ]

let is_valid_identifier name =
  let length = String.length name in
  length > 0
  && is_identifier_start name.[0]
  && String.for_all is_identifier_char name
  && not (List.mem name reserved_identifiers)

let collect_assignments kind count assignments =
  let label = kind_name kind in
  if count < 0 then Error (Printf.sprintf "%s bit count cannot be negative" label)
  else
    let rec collect index acc =
      if index = count then Ok (List.rev acc)
      else
        match IntMap.find_opt index assignments with
        | None ->
            Error
              (Printf.sprintf "missing %s mapping for index %d" label index)
        | Some argument -> collect (index + 1) ((index, argument) :: acc)
    in
    let* entries = collect 0 [] in
    if IntMap.cardinal assignments <> count then
      Error
        (Printf.sprintf
           "%s assignment contains an index outside the declared bit count"
           label)
    else Ok entries

let validate_names kind entries =
  let label = kind_name kind in
  let rec loop = function
    | [] -> Ok ()
    | (_, (name, local_index)) :: rest ->
        if local_index < 0 then
          Error
            (Printf.sprintf "%s mapping for register %S has a negative index"
               label name)
        else if kind = Quantum && name = "$" then loop rest
        else if not (is_valid_identifier name) then
          Error
            (Printf.sprintf "%s register name %S is not valid OpenQASM 2"
               label name)
        else loop rest
  in
  loop entries

let names_of_entries entries =
  List.fold_left
    (fun names (_, (name, _)) ->
      if name = "$" then names else StringSet.add name names)
    StringSet.empty entries

let fresh_physical_name occupied =
  let rec choose suffix =
    let candidate =
      if suffix = 0 then "qasm3_physical"
      else Printf.sprintf "qasm3_physical_%d" suffix
    in
    if StringSet.mem candidate occupied then choose (suffix + 1) else candidate
  in
  choose 0

let rename_physical_register q_entries c_entries =
  if List.exists (fun (_, (name, _)) -> name = "$") q_entries then
    let occupied =
      StringSet.union (names_of_entries q_entries) (names_of_entries c_entries)
    in
    let physical_name = fresh_physical_name occupied in
    List.map
      (fun (global_index, (name, local_index)) ->
        let name = if name = "$" then physical_name else name in
        (global_index, (name, local_index)))
      q_entries
  else q_entries

let group_registers kind entries =
  let label = kind_name kind in
  let rec consume_run name expected_index = function
    | (_, (next_name, local_index)) :: rest when next_name = name ->
        if local_index <> expected_index then
          Error
            (Printf.sprintf
               "%s mapping for register %S expected local index %d but found %d"
               label name expected_index local_index)
        else consume_run name (expected_index + 1) rest
    | rest -> Ok (expected_index, rest)
  in
  let rec group seen acc = function
    | [] -> Ok (List.rev acc)
    | (_, (name, local_index)) :: _ as remaining ->
        if StringSet.mem name seen then
          Error
            (Printf.sprintf "%s register %S appears in multiple mapping ranges"
               label name)
        else if local_index <> 0 then
          Error
            (Printf.sprintf "%s mapping for register %S must start at index 0"
               label name)
        else
          let* size, rest = consume_run name 0 remaining in
          group (StringSet.add name seen) ({ name; size } :: acc) rest
  in
  group StringSet.empty [] entries

let ensure_disjoint_register_names qregs cregs =
  let qnames =
    List.fold_left (fun names reg -> StringSet.add reg.name names)
      StringSet.empty qregs
  in
  match List.find_opt (fun reg -> StringSet.mem reg.name qnames) cregs with
  | None -> Ok ()
  | Some reg ->
      Error
        (Printf.sprintf
           "register name %S is used for both quantum and classical registers"
           reg.name)

let array_of_entries count entries =
  let values = Array.make count ("", 0) in
  List.iter
    (fun (global_index, argument) -> values.(global_index) <- argument)
    entries;
  values

let find_register registers name =
  List.find_opt (fun register -> register.name = name) registers

let argument_of_index kind assignments index =
  let label = kind_name kind in
  if index < 0 || index >= Array.length assignments then
    Error (Printf.sprintf "missing %s mapping for index %d" label index)
  else Ok assignments.(index)

let expression_of_angle angle =
  match angle with
  | PiAngle q ->
      let numerator = q.qnum in
      let denominator = q.qden in
      let abs_numerator = Big_int_Z.abs_big_int numerator in
      let abs_numerator_int = Big_int_Z.int_of_big_int abs_numerator in
      let denominator_int = Big_int_Z.int_of_big_int denominator in
      let base =
        match
          Big_int_Z.int_of_big_int abs_numerator,
          Big_int_Z.int_of_big_int denominator
        with
        | 0, _ -> Nninteger 0
        | 1, 1 -> Pi
        | 1, _ -> BinaryOp (Div, Pi, Nninteger denominator_int)
        | _, 1 -> BinaryOp (Times, Nninteger abs_numerator_int, Pi)
        | _, _ ->
            BinaryOp
              ( Div,
                BinaryOp (Times, Nninteger abs_numerator_int, Pi),
                Nninteger denominator_int )
      in
      if Big_int_Z.sign_big_int numerator < 0 then Ok (UnaryOp (UMinus, base))
      else Ok base
  | RealAngle angle ->
      let value = RbaseSymbolsImpl.coq_Rrepr angle in
      if Float.is_finite value then Ok (Real value)
      else Error "cannot sugar a rotation with a non-finite angle"

let big_int_of_int = Big_int_Z.big_int_of_int

let normalize_q num den =
  let num = big_int_of_int num in
  let den = big_int_of_int den in
  if Big_int_Z.eq_big_int den Big_int_Z.zero_big_int then
    invalid_arg "zero denominator in exact angle";
  let num, den =
    if Big_int_Z.sign_big_int den < 0 then
      (Big_int_Z.minus_big_int num, Big_int_Z.minus_big_int den)
    else (num, den)
  in
  let divisor = Big_int_Z.gcd_big_int (Big_int_Z.abs_big_int num) den in
  {
    qnum = Big_int_Z.div_big_int num divisor;
    qden = Big_int_Z.div_big_int den divisor;
  }

let q_of_int num = normalize_q num 1

let q num den = normalize_q num den

let check_angle_eqb angles expected =
  match angles with
  | theta, phi, lambda ->
      let theta', phi', lambda' = expected in
      angle_eqb_mod_2 theta (PiAngle theta')
      && angle_eqb_mod_2 phi (PiAngle phi')
      && angle_eqb_mod_2 lambda (PiAngle lambda')

(* QASMCore holds an angle two ways, and the two are not interchangeable
   downstream: angle_eqb_mod_2 is false for every RealAngle, so a real-valued
   zero is not recognised as a standard gate, while the reader folds a "0.0"
   literal back to the exact angle 0 (Desugar.pi_multiple_of_exp).  Emitting the
   exact form for a real zero closes that asymmetry, which is what makes
   re-reading our own output give back the program we wrote.  Zero is the only
   real literal the reader folds, so no other value is touched. *)
let canonical_angle angle =
  match angle with
  | RealAngle value when RbaseSymbolsImpl.coq_Rrepr value = 0.0 ->
      PiAngle (q_of_int 0)
  | angle -> angle

let sugar_standard_gate angles =
  let check = check_angle_eqb angles in
  if check (q_of_int 0, q_of_int 0, q_of_int 0) then Some "id"
  else if check (q_of_int 1, q_of_int 0, q_of_int 1) then Some "x"
  else if check (q_of_int 1, q 1 2, q 1 2) then Some "y"
  else if check (q_of_int 0, q_of_int 0, q_of_int 1) then Some "z"
  else if check (q 1 2, q_of_int 0, q_of_int 1) then Some "h"
  else if check (q_of_int 0, q_of_int 0, q 1 2) then Some "s"
  else if check (q_of_int 0, q_of_int 0, q (-1) 2) then Some "sdg"
  else if check (q_of_int 0, q_of_int 0, q 1 4) then Some "t"
  else if check (q_of_int 0, q_of_int 0, q (-1) 4) then Some "tdg"
  else if check (q 1 2, q (-1) 2, q 1 2) then Some "sx"
  else if check (q 1 2, q 1 2, q (-1) 2) then Some "sxdg"
  else None

let qop_of_leaf q_assignment c_assignment = function
  | RotateInstr (theta, phi, lambda, qubit) -> (
      let theta = canonical_angle theta
      and phi = canonical_angle phi
      and lambda = canonical_angle lambda in
      match sugar_standard_gate (theta, phi, lambda) with
      | Some id -> 
        let* argument = argument_of_index Quantum q_assignment qubit in
        let arg = (fst argument, Some (snd argument)) in
        Ok (Uop (Gate (id, [], [arg])))
      | None ->
        let* theta = expression_of_angle theta in
        let* phi = expression_of_angle phi in
        let* lambda = expression_of_angle lambda in
        let* argument = argument_of_index Quantum q_assignment qubit in
        let arg = (fst argument, Some (snd argument)) in
        Ok (Uop (U ([ theta; phi; lambda ], arg)))
    )
  | CnotInstr (control, target) ->
      let* control = argument_of_index Quantum q_assignment control in
      let* target = argument_of_index Quantum q_assignment target in
      Ok
        (Uop
           (CX
              ( (fst control, Some (snd control)),
                (fst target, Some (snd target)) )))
  | SwapInstr (qubit1, qubit2) -> (* Now swap can be generated by unoptimization *)
      let* qubit1 = argument_of_index Quantum q_assignment qubit1 in
      let* qubit2 = argument_of_index Quantum q_assignment qubit2 in
      Ok
        (Uop
           (Gate
              ( "swap",
                [],
                [ (fst qubit1, Some (snd qubit1));
                  (fst qubit2, Some (snd qubit2)) ] )))
  | MeasureInstr (qubit, cbit) ->
      let* qubit = argument_of_index Quantum q_assignment qubit in
      let* cbit = argument_of_index Classical c_assignment cbit in
      Ok
        (Meas
           ( (fst qubit, Some (snd qubit)),
             (fst cbit, Some (snd cbit)) ))
  | ResetInstr qubit ->
      let* qubit = argument_of_index Quantum q_assignment qubit in
      Ok (Reset (fst qubit, Some (snd qubit)))
  | NopInstr | SeqInstr _ | IfInstr _ ->
      Error "unsupported non-leaf instruction in OpenQASM 2 sugar"

let rec all_some = function
  | [] -> Some []
  | None :: _ -> None
  | Some value :: rest ->
      Option.map (fun values -> value :: values) (all_some rest)

let full_register_argument registers arguments =
  match arguments with
  | (name, Some 0) :: _ -> (
      match find_register registers name with
      | None -> None
      | Some register ->
          if List.length arguments <> register.size then None
          else
            let valid =
              List.mapi
                (fun expected -> function
                  | actual_name, Some actual_index ->
                      actual_name = name && actual_index = expected
                  | _ -> false)
                arguments
              |> List.for_all Fun.id
            in
            if valid then Some (name, None) else None)
  | _ -> None

let collapse_rotations qregs qops =
  match
    List.map
      (function Uop (U (angles, argument)) -> Some (angles, argument) | _ -> None)
      qops
    |> all_some
  with
  | Some ((angles, _) :: _ as rotations)
    when List.for_all (fun (other_angles, _) -> other_angles = angles) rotations
    ->
      let arguments = List.map snd rotations in
      Option.map (fun argument -> Uop (U (angles, argument)))
        (full_register_argument qregs arguments)
  | _ -> None

let collapse_cnots qregs qops =
  match
    List.map
      (function Uop (CX (control, target)) -> Some (control, target) | _ -> None)
      qops
    |> all_some
  with
  | None | Some [] -> None
  | Some cnots -> (
      match
        ( full_register_argument qregs (List.map fst cnots),
          full_register_argument qregs (List.map snd cnots) )
      with
      | Some control, Some target -> Some (Uop (CX (control, target)))
      | _ -> None)

let collapse_measurements qregs cregs qops =
  match
    List.map
      (function Meas (qubit, cbit) -> Some (qubit, cbit) | _ -> None)
      qops
    |> all_some
  with
  | None | Some [] -> None
  | Some measurements -> (
      match
        ( full_register_argument qregs (List.map fst measurements),
          full_register_argument cregs (List.map snd measurements) )
      with
      | Some qubit, Some cbit -> Some (Meas (qubit, cbit))
      | _ -> None)

let collapse_resets qregs qops =
  match
    List.map (function Reset argument -> Some argument | _ -> None) qops
    |> all_some
  with
  | Some (_ :: _ as arguments) ->
      Option.map (fun argument -> Reset argument)
        (full_register_argument qregs arguments)
  | _ -> None

let collapse_parallel_qop qregs cregs qops =
  [ (fun () -> collapse_rotations qregs qops);
    (fun () -> collapse_cnots qregs qops);
    (fun () -> collapse_measurements qregs cregs qops);
    (fun () -> collapse_resets qregs qops) ]
  |> List.find_map (fun collapse -> collapse ())

let rec flatten_condition acc = function
  | IfInstr (cbit, expected, body) ->
      flatten_condition ((cbit, expected) :: acc) body
  | body -> (List.rev acc, body)

let rec flatten_body_rev acc = function
  | NopInstr -> Ok acc
  | SeqInstr instructions ->
      List.fold_left
        (fun result instruction ->
          let* acc = result in
          flatten_body_rev acc instruction)
        (Ok acc)
        instructions
  | IfInstr _ ->
      Error "unrepresentable conditional: nested condition in the guarded body"
  | instruction -> Ok (instruction :: acc)

let comparison_of_condition cregs c_assignment conditions =
  match conditions with
  | [] -> Error "unrepresentable conditional: empty condition"
  | (first_cbit, _) :: _ ->
      let* condition_name, first_local_index =
        argument_of_index Classical c_assignment first_cbit
      in
      let* register =
        match find_register cregs condition_name with
        | Some register -> Ok register
        | None ->
            Error
              (Printf.sprintf
                 "unrepresentable conditional: unknown classical register %S"
                 condition_name)
      in
      if first_local_index <> 0 || List.length conditions <> register.size then
        Error
          "unrepresentable conditional: condition does not cover a whole classical register"
      else
        let rec build expected_index comparison = function
          | [] -> Ok (condition_name, comparison)
          | (cbit, expected_value) :: rest ->
              let* name, local_index =
                argument_of_index Classical c_assignment cbit
              in
              if name <> condition_name || local_index <> expected_index then
                Error
                  "unrepresentable conditional: classical bits are not in source register order"
              else if expected_value && expected_index >= Sys.int_size - 1 then
                Error
                  "unrepresentable conditional: comparison value exceeds OCaml integer range"
              else
                let comparison =
                  if expected_value then comparison lor (1 lsl expected_index)
                  else comparison
                in
                build (expected_index + 1) comparison rest
        in
        build 0 0 conditions

let qop_writes_register register_name = function
  | Meas (_, (name, _)) -> name = register_name
  | Uop _ | Reset _ -> false

let statements_of_condition qregs cregs q_assignment c_assignment instruction =
  let conditions, body = flatten_condition [] instruction in
  let* condition_name, comparison =
    comparison_of_condition cregs c_assignment conditions
  in
  let* body_rev = flatten_body_rev [] body in
  let body_results =
    List.rev body_rev |> List.map (qop_of_leaf q_assignment c_assignment)
  in
  let* qops =
    List.fold_right
      (fun result acc ->
        let* value = result in
        let* values = acc in
        Ok (value :: values))
      body_results (Ok [])
  in
  match qops with
  | [] -> Ok []
  | [ qop ] -> Ok [ If (condition_name, comparison, qop) ]
  | _ -> (
      match collapse_parallel_qop qregs cregs qops with
      | Some qop -> Ok [ If (condition_name, comparison, qop) ]
      | None ->
          if List.exists (qop_writes_register condition_name) qops then
            Error
              "unrepresentable conditional: guarded operations mutate the condition register"
          else
            Ok
              (List.map
                 (fun qop -> If (condition_name, comparison, qop))
                 qops))

let statements_of_instruction qregs cregs q_assignment c_assignment instruction
    =
  let rec collect acc = function
    | NopInstr -> Ok acc
    | SeqInstr instructions ->
        let rec collect_all acc = function
          | [] ->
              Ok acc
          | instruction :: rest ->
              let* acc = collect acc instruction in
              collect_all acc rest
        in
        collect_all acc instructions
    | IfInstr _ as conditional ->
        let* statements =
          statements_of_condition qregs cregs q_assignment c_assignment
            conditional
        in
        Ok (List.rev_append statements acc)
    | instruction ->
        let* qop = qop_of_leaf q_assignment c_assignment instruction in
        Ok (Qop qop :: acc)
  in
  Result.map List.rev (collect [] instruction)

let qelib_gate_names =
  [ "id"; "x"; "y"; "z"; "h"; "s"; "sdg"; "t"; "tdg"; "sx"; "sxdg"; "swap" ]

let qop_uses_qelib = function
  | Uop (Gate (name, _, _)) -> List.mem name qelib_gate_names
  | Uop (U _ | CX _) | Meas _ | Reset _ -> false

let rec statement_uses_qelib = function
  | Qop qop | If (_, _, qop) -> qop_uses_qelib qop
  | IfBlock (_, body) -> List.exists statement_uses_qelib body
  | Include _ | Decl _ | GateDecl _ | OpaqueDecl _ | Barrier _ -> false

(* The register structure recovered from a pair of QASMCore bit assignments.
   Shared with Qasm3.Sugar, which needs the same reconstruction. *)
type layout = {
  qregs : register list;
  cregs : register list;
  qbits : (string * int) array;
  cbits : (string * int) array;
}

let layout_of_assignments nq nc q_assignment c_assignment =
  let* q_entries = collect_assignments Quantum nq q_assignment in
  let* c_entries = collect_assignments Classical nc c_assignment in
  let* () = validate_names Quantum q_entries in
  let* () = validate_names Classical c_entries in
  let q_entries = rename_physical_register q_entries c_entries in
  let* qregs = group_registers Quantum q_entries in
  let* cregs = group_registers Classical c_entries in
  let* () = ensure_disjoint_register_names qregs cregs in
  Ok
    {
      qregs;
      cregs;
      qbits = array_of_entries nq q_entries;
      cbits = array_of_entries nc c_entries;
    }

let sugar nq nc q_assignment c_assignment instruction =
  let* { qregs; cregs; qbits = q_assignment; cbits = c_assignment } =
    layout_of_assignments nq nc q_assignment c_assignment
  in
  let* statements =
    statements_of_instruction qregs cregs q_assignment c_assignment instruction
  in
  let declarations =
    List.map (fun reg -> Decl (QReg (reg.name, reg.size))) qregs
    @ List.map (fun reg -> Decl (CReg (reg.name, reg.size))) cregs
  in
  let includes =
    if List.exists statement_uses_qelib statements then [ Include "qelib1.inc" ]
    else []
  in
  Ok (includes @ declarations @ statements)
