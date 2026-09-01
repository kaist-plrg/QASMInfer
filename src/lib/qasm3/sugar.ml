open Ast
open Extracted

module A2 = Qasm2.Ast
module S2 = Qasm2.Sugar

let ( let* ) result f = Result.bind result f

(* Identifiers this front end's lexer claims as keywords.  A register whose name
   collides with one of them would render as OpenQASM 3 that cannot be read
   back, so it is rejected instead. *)
let reserved_identifiers =
  [ "barrier"; "bit"; "cos"; "creg"; "exp"; "false"; "gate"; "if"; "include";
    "ln"; "measure"; "opaque"; "pi"; "qreg"; "qubit"; "reset"; "sin"; "sqrt";
    "tan"; "true" ]

let validate_register_names kind registers =
  let label = match kind with `Quantum -> "quantum" | `Classical -> "classical" in
  let rec loop = function
    | [] -> Ok ()
    | register :: rest ->
        if List.mem register.S2.name reserved_identifiers then
          Error
            (Printf.sprintf "%s register name %S is reserved in OpenQASM 3" label
               register.S2.name)
        else loop rest
  in
  loop registers

let binaryop_of_qasm2 = function
  | A2.Plus -> Plus
  | A2.Minus -> Minus
  | A2.Times -> Times
  | A2.Div -> Div
  | A2.Pow -> Pow

let unaryop_of_qasm2 = function
  | A2.Sin -> Sin
  | A2.Cos -> Cos
  | A2.Tan -> Tan
  | A2.Exp -> Exp
  | A2.Ln -> Ln
  | A2.Sqrt -> Sqrt
  | A2.UMinus -> UMinus

let rec exp_of_qasm2 = function
  | A2.Real value -> Real value
  | A2.Nninteger value -> Nninteger value
  | A2.Pi -> Pi
  | A2.Id id -> Id id
  | A2.BinaryOp (operator, left, right) ->
      BinaryOp (binaryop_of_qasm2 operator, exp_of_qasm2 left, exp_of_qasm2 right)
  | A2.UnaryOp (operator, expression) ->
      UnaryOp (unaryop_of_qasm2 operator, exp_of_qasm2 expression)

(* Gates declared by stdgates.inc.  Qasm2.Sugar.sugar_standard_gate can also
   name "sxdg", which stdgates.inc does not define, so that one falls back to a
   literal U rotation. *)
let stdgates_gate_names =
  [ "id"; "x"; "y"; "z"; "h"; "s"; "sdg"; "t"; "tdg"; "sx"; "swap"; "cx" ]

let expression_of_angle angle =
  let* expression = S2.expression_of_angle angle in
  Ok (exp_of_qasm2 expression)

let indexed (name, index) = (name, Some index)

let qop_of_leaf layout instruction =
  let qubit index = S2.argument_of_index S2.Quantum layout.S2.qbits index in
  let cbit index = S2.argument_of_index S2.Classical layout.S2.cbits index in
  match instruction with
  | RotateInstr (theta, phi, lambda, target) -> (
      let* argument = qubit target in
      match S2.sugar_standard_gate (theta, phi, lambda) with
      | Some name when List.mem name stdgates_gate_names ->
          Ok (Uop (Gate (name, [], [ indexed argument ])))
      | Some _ | None ->
          let* theta = expression_of_angle theta in
          let* phi = expression_of_angle phi in
          let* lambda = expression_of_angle lambda in
          Ok (Uop (U ([ theta; phi; lambda ], indexed argument))))
  | CnotInstr (control, target) ->
      let* control = qubit control in
      let* target = qubit target in
      Ok (Uop (Gate ("cx", [], [ indexed control; indexed target ])))
  | SwapInstr (qubit1, qubit2) ->
      let* qubit1 = qubit qubit1 in
      let* qubit2 = qubit qubit2 in
      Ok (Uop (Gate ("swap", [], [ indexed qubit1; indexed qubit2 ])))
  | MeasureInstr (target, destination) ->
      let* target = qubit target in
      let* destination = cbit destination in
      Ok (Meas (indexed target, indexed destination))
  | ResetInstr target ->
      let* target = qubit target in
      Ok (Reset (indexed target))
  | NopInstr | SeqInstr _ | IfInstr _ ->
      Error "unsupported non-leaf instruction in OpenQASM 3 sugar"

let rec statements_of_instruction layout instruction =
  match instruction with
  | NopInstr -> Ok []
  | SeqInstr instructions ->
      List.fold_left
        (fun accumulated instruction ->
          let* accumulated = accumulated in
          let* statements = statements_of_instruction layout instruction in
          Ok (List.rev_append statements accumulated))
        (Ok []) instructions
      |> Result.map List.rev
  | IfInstr (guard, expected, body) ->
      (* QASMCore guards one classical bit, which OpenQASM 3 states directly.
         Nested guards become nested blocks; nothing here can fail to be
         expressible. *)
      let* name, index = S2.argument_of_index S2.Classical layout.S2.cbits guard in
      let* body = statements_of_instruction layout body in
      Ok [ If (CondBit (name, index, expected), body) ]
  | leaf ->
      let* qop = qop_of_leaf layout leaf in
      Ok [ Qop qop ]

let rec statement_uses_stdgates = function
  | Qop (Uop (Gate (name, _, _))) -> List.mem name stdgates_gate_names
  | If (_, body) -> List.exists statement_uses_stdgates body
  | Qop (Uop (U _ | CX _)) | Qop (Meas _) | Qop (Reset _) -> false
  | Include _ | Decl _ | GateDecl _ | OpaqueDecl _ | Barrier _ -> false

let sugar nq nc q_assignment c_assignment instruction =
  let* layout = S2.layout_of_assignments nq nc q_assignment c_assignment in
  let* () = validate_register_names `Quantum layout.S2.qregs in
  let* () = validate_register_names `Classical layout.S2.cregs in
  let* statements = statements_of_instruction layout instruction in
  let declarations =
    List.map (fun register -> Decl (QReg (register.S2.name, register.S2.size)))
      layout.S2.qregs
    @ List.map (fun register -> Decl (CReg (register.S2.name, register.S2.size)))
        layout.S2.cregs
  in
  let includes =
    if List.exists statement_uses_stdgates statements then
      [ Include "stdgates.inc" ]
    else []
  in
  Ok (includes @ declarations @ statements)
