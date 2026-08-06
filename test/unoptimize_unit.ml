module E = Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api
module IntMap = Q2.Desugar.IntMap

let failf fmt = Printf.ksprintf failwith fmt

let require condition message =
  if not condition then failwith message

let contains text fragment =
  let text_length = String.length text in
  let fragment_length = String.length fragment in
  let rec search offset =
    if offset + fragment_length > text_length then false
    else if String.sub text offset fragment_length = fragment then true
    else search (offset + 1)
  in
  fragment_length = 0 || search 0

let require_contains text fragment =
  if not (contains text fragment) then
    failf "expected %S to contain %S" text fragment

let ok_or_fail = function
  | Ok value -> value
  | Error message -> failf "unexpected sugar error: %s" message

let expect_error fragment = function
  | Ok _ -> failf "expected sugar error containing %S" fragment
  | Error message -> require_contains message fragment

let r value = E.RbaseSymbolsImpl.coq_Rabst value

let real_angle value = E.RealAngle (r value)

let pi_angle numerator denominator =
  E.PiAngle
    {
      E.qnum = Big_int_Z.big_int_of_int numerator;
      qden = Big_int_Z.big_int_of_int denominator;
    }

let test_unoptimize_nop_is_exact_identity () =
let instruction =
  E.SeqInstr
    [
      E.RotateInstr
        (real_angle 0.25, real_angle (-0.5), real_angle 1.75, 2);
      E.CnotInstr (2, 0);
      E.SwapInstr (0, 2);
      E.MeasureInstr (2, 1);
      E.IfInstr
        ( 1,
          true,
          E.SeqInstr
            [
              E.ResetInstr 2;
              E.NopInstr;
            ] );
    ]
  in
  let result = Unoptimize.unoptimize_nop instruction in
  require (result = instruction)
    "unoptimize_nop must preserve every instruction constructor exactly"

let desugar_qasm2 source =
  source |> Q2.parse_string |> Q2.inline_qelib |> Q2.desugar

let sorted_probabilities nq nc instruction =
  E.execute_and_calculate_prob nq nc instruction
  |> List.map (fun (state, probability) ->
         (Big_int_Z.int_of_big_int state, E.RbaseSymbolsImpl.coq_Rrepr probability))
  |> List.sort (fun (left, _) (right, _) -> compare left right)

let require_same_distribution ~context nq nc left right =
  let left = sorted_probabilities nq nc left in
  let right = sorted_probabilities nq nc right in
  if List.length left <> List.length right then
    failf "%s: probability supports differ" context;
  List.iter2
    (fun (left_state, left_probability) (right_state, right_probability) ->
      if left_state <> right_state then
        failf "%s: classical states differ" context;
      if Float.abs (left_probability -. right_probability) > 1e-12 then
        failf "%s: probability for state %d differs (%g <> %g)" context
          left_state left_probability right_probability)
    left right

let sugar_and_reparse nq nc instruction q_assignment c_assignment =
  let transformed = Unoptimize.unoptimize_nop instruction in
  let program =
    Q2.sugar nq nc q_assignment c_assignment transformed |> ok_or_fail
  in
  let rendered = Q2.string_of_program program in
  require_contains rendered "OPENQASM 2.0;";
  let nq', nc', instruction', q_assignment', c_assignment' =
    desugar_qasm2 rendered
  in
  require (nq = nq') "sugared QASM changed the qubit count";
  require (nc = nc') "sugared QASM changed the classical-bit count";
  require (instruction = instruction')
    "sugar/desugar must preserve the desugar-produced instruction tree";
  require_same_distribution ~context:"sugar/desugar round trip" nq nc instruction
    instruction';
  let rendered_again =
    Q2.sugar nq' nc' q_assignment' c_assignment' instruction'
    |> ok_or_fail |> Q2.string_of_program
  in
  require (rendered = rendered_again)
    "canonical QASM2 rendering must be stable after a second rewrite";
  (program, rendered)

let rec instruction_exists predicate instruction =
  predicate instruction
  ||
  match instruction with
  | E.SeqInstr instructions ->
      List.exists (instruction_exists predicate) instructions
  | E.IfInstr (_, _, body) ->
      instruction_exists predicate body
  | _ ->
      false

let test_qasm2_sugar_round_trip () =
  let source =
    {|
OPENQASM 2.0;
include "qelib1.inc";
qreg left[2];
qreg right[1];
creg flags[2];
creg result[1];
h left[0];
x left[1];
cx left[0],right[0];
rz(pi/3) left[1];
measure left -> flags;
if (flags==2) measure left -> flags;
measure right[0] -> result[0];
reset right[0];
|}
  in
  let nq, nc, instruction, q_assignment, c_assignment =
    desugar_qasm2 source
  in
  require (nq = 3) "multiple quantum registers must retain all three qubits";
  require (nc = 3) "multiple classical registers must retain all three bits";
  let require_constructor name predicate =
    require (instruction_exists predicate instruction)
      ("desugared fixture lacks " ^ name)
  in
  require_constructor "RotateInstr" (function E.RotateInstr _ -> true | _ -> false);
  require_constructor "CnotInstr" (function E.CnotInstr _ -> true | _ -> false);
  require_constructor "MeasureInstr" (function E.MeasureInstr _ -> true | _ -> false);
  require_constructor "ResetInstr" (function E.ResetInstr _ -> true | _ -> false);
  require_constructor "SeqInstr" (function E.SeqInstr _ -> true | _ -> false);
  require_constructor "IfInstr" (function E.IfInstr _ -> true | _ -> false);
  let _, rendered =
    sugar_and_reparse nq nc instruction q_assignment c_assignment
  in
  let _, _, _, q_assignment', c_assignment' = desugar_qasm2 rendered in
  require
    (IntMap.bindings q_assignment = IntMap.bindings q_assignment')
    "QASM2 round trip changed quantum-register assignments";
  require
    (IntMap.bindings c_assignment = IntMap.bindings c_assignment')
    "QASM2 round trip changed classical-register assignments"

let qreg_names program =
  List.filter_map
    (function
      | Q2.Ast.Decl (Q2.Ast.QReg (name, _)) -> Some name
      | _ -> None)
    program

let has_duplicates values =
  List.length (List.sort_uniq String.compare values) <> List.length values

let test_qasm3_physical_qubit_rename_avoids_collisions () =
  let qasm3_program =
    let open Qasm3.Ast in
    [ Decl (QReg ("qasm3_physical", 1));
      Decl (CReg ("result", 1));
      Qop
        (Uop
           (U
              ( [ Pi; Nninteger 0; Pi ],
                ("$", Some 0) )));
      Qop (Uop (CX (("$", Some 0), ("qasm3_physical", Some 0))));
      Qop (Meas (("$", Some 0), ("result", Some 0))) ]
  in
  let nq, nc, instruction, q_assignment, c_assignment =
    qasm3_program |> Q3.desugar |> Q2.desugar
  in
  let program, rendered =
    sugar_and_reparse nq nc instruction q_assignment c_assignment
  in
  let names = qreg_names program in
  require (List.mem "qasm3_physical" names)
    "the declared QASM3 register name must be preserved";
  require (List.mem "qasm3_physical_1" names)
    "the synthetic physical register must use the first fresh suffix";
  require (not (List.mem "$" names))
    "the QASM3 physical-register sentinel is not a legal QASM2 identifier";
  require (not (has_duplicates names))
    "physical-qubit renaming must not duplicate a declared register";
  require_contains rendered "qreg qasm3_physical_1[1];"

let test_qasm3_physical_qubit_rename_avoids_classical_collision () =
  let q_assignment = IntMap.add 0 ("$", 0) IntMap.empty in
  let c_assignment = IntMap.add 0 ("qasm3_physical", 0) IntMap.empty in
  let program =
    Q2.sugar 1 1 q_assignment c_assignment (E.MeasureInstr (0, 0))
    |> ok_or_fail
  in
  let rendered = Q2.string_of_program program in
  ignore (Q2.parse_string_result rendered |> ok_or_fail);
  require
    (List.mem "qasm3_physical_1" (qreg_names program))
    "the synthetic physical register must avoid classical register names";
  require_contains rendered "qreg qasm3_physical_1[1];";
  require_contains rendered "creg qasm3_physical[1];"

let test_qasm3_conditional_physical_qubit_round_trip () =
  let source =
    {|
OPENQASM 3.0;
bit[1] flag;
if (flag==1) reset $2;
|}
  in
  let nq, nc, instruction, q_assignment, c_assignment =
    source |> Q3.parse_string |> Q3.desugar |> Q2.desugar
  in
  require (nq = 3)
    "a physical qubit used only in a conditional must determine the qubit count";
  require
    (IntMap.bindings q_assignment
    = [ (0, ("$", 0)); (1, ("$", 1)); (2, ("$", 2)) ])
    "conditional physical qubits must receive a complete quantum mapping";
  require (nc = 1) "the conditional fixture must retain its classical bit";
  let _, rendered =
    sugar_and_reparse nq nc instruction q_assignment c_assignment
  in
  require_contains rendered "qreg qasm3_physical[3];";
  require_contains rendered "if(flag==1) reset qasm3_physical[2];"

let singleton_map index argument = IntMap.add index argument IntMap.empty

let test_sugar_reports_missing_quantum_mapping () =
  Q2.sugar 1 0 IntMap.empty IntMap.empty
    (E.RotateInstr (pi_angle 0 1, pi_angle 0 1, pi_angle 0 1, 0))
  |> expect_error "missing quantum mapping"

let test_sugar_reports_missing_classical_mapping () =
  Q2.sugar 1 1 (singleton_map 0 ("q", 0)) IntMap.empty
    (E.MeasureInstr (0, 0))
  |> expect_error "missing classical mapping"

let test_sugar_rejects_reserved_quantum_register_name () =
  Q2.sugar 1 0 (singleton_map 0 ("cos", 0)) IntMap.empty E.NopInstr
  |> expect_error "quantum register name \"cos\" is not valid OpenQASM 2"

let test_sugar_rejects_swap () =
  let q_assignment =
    IntMap.empty |> IntMap.add 0 ("q", 0) |> IntMap.add 1 ("q", 1)
  in
  Q2.sugar 2 0 q_assignment IntMap.empty (E.SwapInstr (0, 1))
  |> expect_error "unsupported SwapInstr"

let test_sugar_rejects_partial_register_condition () =
  let c_assignment =
    IntMap.empty |> IntMap.add 0 ("c", 0) |> IntMap.add 1 ("c", 1)
  in
  Q2.sugar 1 2 (singleton_map 0 ("q", 0)) c_assignment
    (E.IfInstr
       (0, true, E.RotateInstr (pi_angle 1 1, pi_angle 0 1, pi_angle 1 1, 0)))
  |> expect_error "unrepresentable conditional"

let test_sugar_splits_safe_conditional_sequence () =
  let q_assignment = singleton_map 0 ("q", 0) in
  let c_assignment =
    IntMap.empty |> IntMap.add 0 ("flag", 0) |> IntMap.add 1 ("result", 0)
  in
  let instruction =
    E.IfInstr
      ( 0,
        false,
        E.SeqInstr
          [ E.RotateInstr (pi_angle 1 2, pi_angle 0 1, pi_angle 1 1, 0);
            E.MeasureInstr (0, 1) ] )
  in
  let program =
    Q2.sugar 1 2 q_assignment c_assignment instruction |> ok_or_fail
  in
  let guarded_statement_count =
    List.fold_left
      (fun count -> function
        | Q2.Ast.If ("flag", 0, _) -> count + 1
        | _ -> count)
      0 program
  in
  require (guarded_statement_count = 2)
    "a safe guarded sequence must split into independently guarded qops";
  let rendered = Q2.string_of_program program in
  let nq, nc, rewritten, _, _ = desugar_qasm2 rendered in
  require_same_distribution ~context:"split conditional sequence" nq nc
    instruction rewritten

let test_sugar_rejects_conditional_sequence_that_mutates_guard () =
  let instruction =
    E.IfInstr
      ( 0,
        false,
        E.SeqInstr [E.MeasureInstr (0, 0); E.ResetInstr 0] )
  in
  Q2.sugar 1 1 (singleton_map 0 ("q", 0))
    (singleton_map 0 ("flag", 0)) instruction
  |> expect_error "guarded operations mutate the condition register"

let tests =
  [ ("unoptimize_nop exact identity", test_unoptimize_nop_is_exact_identity);
    ("QASM2 semantic round trip", test_qasm2_sugar_round_trip);
    ( "QASM3 physical rename collision",
      test_qasm3_physical_qubit_rename_avoids_collisions );
    ( "QASM3 physical/classical rename collision",
      test_qasm3_physical_qubit_rename_avoids_classical_collision );
    ( "QASM3 conditional physical qubit",
      test_qasm3_conditional_physical_qubit_round_trip );
    ("missing quantum map", test_sugar_reports_missing_quantum_mapping);
    ("missing classical map", test_sugar_reports_missing_classical_mapping);
    ( "reserved quantum register name",
      test_sugar_rejects_reserved_quantum_register_name );
    ("unsupported swap", test_sugar_rejects_swap);
    ("unrepresentable condition", test_sugar_rejects_partial_register_condition);
    ("safe conditional split", test_sugar_splits_safe_conditional_sequence);
    ( "unsafe conditional mutation",
      test_sugar_rejects_conditional_sequence_that_mutates_guard )
  ]

let () =
  List.iter
    (fun (name, test) ->
      try test () with exn -> failf "%s: %s" name (Printexc.to_string exn))
    tests
