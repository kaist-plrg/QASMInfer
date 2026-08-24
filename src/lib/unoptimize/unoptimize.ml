open Extracted

module Json = Yojson.Safe.Util

let unoptimize_nop instruction = instruction

let gate_of_string = function
  | "i" | "id" | "std_i" -> Some Std_I
  | "x" | "std_x" -> Some Std_X
  | "y" | "std_y" -> Some Std_Y
  | "z" | "std_z" -> Some Std_Z
  | "h" | "std_h" -> Some Std_H
  | "s" | "std_s" -> Some Std_S
  | "sdg" | "s_dg" | "std_sdg" -> Some Std_Sdg
  | "t" | "std_t" -> Some Std_T
  | "tdg" | "t_dg" | "std_tdg" -> Some Std_Tdg
  | "sx" | "std_sx" -> Some Std_SX
  | "sxdg" | "sx_dg" | "std_sxdg" -> Some Std_SXdg
  | _ -> None

let string_of_gate = function
  | Std_I -> "id"
  | Std_X -> "x"
  | Std_Y -> "y"
  | Std_Z -> "z"
  | Std_H -> "h"
  | Std_S -> "s"
  | Std_Sdg -> "sdg"
  | Std_T -> "t"
  | Std_Tdg -> "tdg"
  | Std_SX -> "sx"
  | Std_SXdg -> "sxdg"

let string_of_pattern_gate = function
  | SPG_Std (gate, qbit) -> Printf.sprintf "%s %d" (string_of_gate gate) qbit
  | SPG_Cnot (control, target) -> Printf.sprintf "cx %d %d" control target
  | SPG_Swap (qbit1, qbit2) -> Printf.sprintf "swap %d %d" qbit1 qbit2

let string_of_pattern_gate_list gates =
  gates |> List.map string_of_pattern_gate |> String.concat "; "

let result_bind result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

let rec result_map_list f = function
  | [] -> Ok []
  | value :: rest ->
      result_bind (f value) (fun mapped ->
          result_bind (result_map_list f rest) (fun mapped_rest ->
              Ok (mapped :: mapped_rest)))

let rec result_filter_map_list f = function
  | [] -> Ok []
  | value :: rest ->
      result_bind (f value) (fun mapped ->
          result_bind (result_filter_map_list f rest) (fun mapped_rest ->
              match mapped with
              | None -> Ok mapped_rest
              | Some value -> Ok (value :: mapped_rest)))

let json_object error json =
  try
    ignore (Json.to_assoc json);
    Ok ()
  with Json.Type_error _ -> Error error

let json_field json key =
  match Json.member key json with
  | `Null -> None
  | value -> Some value

let json_string error json =
  try Ok (Json.to_string json) with Json.Type_error _ -> Error error

let json_list error json =
  try Ok (Json.to_list json) with Json.Type_error _ -> Error error

let int_field rule_name gate_name json key =
  match json_field json key with
  | None ->
      Error
        (Printf.sprintf "rule %s gate '%s' is missing field '%s'" rule_name
           gate_name key)
  | Some value -> (
      try
        let value = Json.to_int value in
        if value >= 0 then Ok value
        else
          Error
            (Printf.sprintf
               "rule %s gate '%s' field '%s' must be a non-negative integer"
               rule_name gate_name key)
      with Json.Type_error _ ->
        Error
          (Printf.sprintf "rule %s gate '%s' field '%s' must be an integer"
             rule_name gate_name key))

let pattern_gate_of_json rule_name key json =
  result_bind
    (json_object
       (Printf.sprintf "rule %s field '%s' gate entry must be an object"
          rule_name key)
       json)
    (fun () ->
      match json_field json "gate" with
      | None ->
          Error
            (Printf.sprintf "rule %s field '%s' gate entry is missing field 'gate'"
               rule_name key)
      | Some gate_json ->
          let gate_name_error =
            Printf.sprintf "rule %s field '%s' gate entry must name a string"
              rule_name key
          in
          result_bind (json_string gate_name_error gate_json) (fun gate_name ->
            let normalized = String.lowercase_ascii gate_name in
            match normalized with
            | "cx" | "cnot" ->
                result_bind
                  (int_field rule_name gate_name json "control")
                  (fun control ->
                    result_bind
                      (int_field rule_name gate_name json "target")
                      (fun target -> Ok (SPG_Cnot (control, target))))
            | "swap" ->
                result_bind (int_field rule_name gate_name json "q1")
                  (fun qbit1 ->
                    result_bind (int_field rule_name gate_name json "q2")
                      (fun qbit2 -> Ok (SPG_Swap (qbit1, qbit2))))
            | _ -> (
                match gate_of_string normalized with
                | Some gate ->
                    result_bind (int_field rule_name gate_name json "q")
                      (fun qbit -> Ok (SPG_Std (gate, qbit)))
                | None ->
                    Error
                      (Printf.sprintf
                         "rule %s field '%s' contains unknown gate '%s'"
                         rule_name key gate_name))))

let pattern_gate_list_field rule_name json key =
  match json_field json key with
  | None -> Error (Printf.sprintf "rule %s is missing field '%s'" rule_name key)
  | Some value ->
      result_bind
        (json_list
           (Printf.sprintf "rule %s field '%s' must be an array" rule_name key)
           value)
        (result_map_list (pattern_gate_of_json rule_name key))

let rule_jsons_of_json json =
  match json with
  | `List _ -> Ok (Json.to_list json)
  | `Assoc _ -> (
      match json_field json "rules" with
      | None ->
          Error "rule file must be an array or an object with a 'rules' array"
      | Some value -> json_list "field 'rules' must be an array" value)
  | _ -> Error "rule file must be an array of rule objects"

let spec_of_rule_json nq index json =
  result_bind
    (json_object (Printf.sprintf "rule %d must be an object" (index + 1)) json)
    (fun () ->
      let fallback_name = Printf.sprintf "rule_%d" (index + 1) in
      let name =
        match json_field json "name" with
        | None -> Ok fallback_name
        | Some value ->
            json_string
              (Printf.sprintf "rule %s field 'name' must be a string"
                 fallback_name)
              value
      in
      result_bind name (fun name ->
          result_bind (pattern_gate_list_field name json "lhs") (fun lhs ->
              result_bind (pattern_gate_list_field name json "rhs") (fun rhs ->
                  if standard_rule_nqubits lhs rhs > nq then Ok None
                  else
                    match standard_rule_of_sequences nq name lhs rhs with
                    | Some spec -> Ok (Some spec)
                    | None ->
                      Error
                        (Printf.sprintf
                           "rule #%d %s (%s -> %s) is not valid up to global omega phase"
                           (index + 1) name (string_of_pattern_gate_list lhs)
                           (string_of_pattern_gate_list rhs))))))

let specs_of_rule_file nq path =
  try
    let json = Yojson.Safe.from_file path in
    result_bind (rule_jsons_of_json json) (fun rule_jsons ->
        match rule_jsons with
        | [] -> Error "rule file must contain at least one rule"
        | _ -> result_filter_map_list
                 (fun (index, json) -> spec_of_rule_json nq index json)
                 (List.mapi (fun index json -> (index, json)) rule_jsons))
  with
  | Sys_error message -> Error message
  | Yojson.Json_error message -> Error ("invalid JSON: " ^ message)

let pi_angle numerator denominator =
  PiAngle
    {
      qnum = Big_int_Z.big_int_of_int numerator;
      qden = Big_int_Z.big_int_of_int denominator;
    }

let random_qbit2 rng nq =
  let qbit1 = Random.State.int rng nq in
  let qbit2_offset = Random.State.int rng (nq - 1) in
  let qbit2 =
    if qbit2_offset < qbit1 then qbit2_offset else qbit2_offset + 1
  in
  (qbit1, qbit2)

let random_rotation rng qbit =
  match Random.State.int rng 6 with
  | 0 -> RotateInstr (pi_angle 0 1, pi_angle 0 1, pi_angle 0 1, qbit)
  | 1 -> RotateInstr (pi_angle 1 1, pi_angle 0 1, pi_angle 1 1, qbit)
  | 2 -> RotateInstr (pi_angle 1 1, pi_angle 0 1, pi_angle 0 1, qbit)
  | 3 -> RotateInstr (pi_angle 1 2, pi_angle 0 1, pi_angle 1 1, qbit)
  | 4 -> RotateInstr (pi_angle 0 1, pi_angle 0 1, pi_angle 1 2, qbit)
  | _ -> RotateInstr (pi_angle 0 1, pi_angle 0 1, pi_angle 1 4, qbit)

let random_atomic_instruction rng nq nc =
  let choices = ref [ (fun () -> NopInstr) ] in
  if nq > 0 then (
    choices :=
      (fun () -> random_rotation rng (Random.State.int rng nq))
      :: (fun () -> ResetInstr (Random.State.int rng nq))
      :: !choices;
    if nc > 0 then
      choices :=
        (fun () ->
          MeasureInstr (Random.State.int rng nq, Random.State.int rng nc))
        :: !choices);
  if nq > 1 then (
    choices :=
      (fun () ->
        let control, target = random_qbit2 rng nq in
        CnotInstr (control, target))
      :: !choices;
    choices :=
      (fun () ->
        let qbit1, qbit2 = random_qbit2 rng nq in
        SwapInstr (qbit1, qbit2))
      :: !choices);
  List.nth !choices (Random.State.int rng (List.length !choices)) ()

let rec random_instruction rng nq nc depth =
  if depth <= 0 then random_atomic_instruction rng nq nc
  else
    match Random.State.int rng (if nc > 0 then 3 else 2) with
    | 0 ->
        random_atomic_instruction rng nq nc
    | 1 ->
        SeqInstr
          [
            random_instruction rng nq nc (depth - 1);
            random_instruction rng nq nc (depth - 1);
          ]
    | _ ->
        IfInstr
          ( Random.State.int rng nc,
            Random.State.bool rng,
            random_instruction rng nq nc (depth - 1) )

let random_parameter rng nq nc param_kind =
  match param_kind with
  | ParamKind_None ->
      Some Param_None
  | ParamKind_qbit1 ->
      if nq <= 0 then None
      else Some (Param_qbit1 (Random.State.int rng nq))
  | ParamKind_qbit2 ->
      if nq < 2 then None
      else
        let qbit1, qbit2 = random_qbit2 rng nq in
        Some (Param_qbit2 (qbit1, qbit2))
  | ParamKind_cbit_instr ->
      if nc <= 0 then None
      else
        Some
          (Param_cbit_instr
             (Random.State.int rng nc, random_instruction rng nq nc 2))

type manual_parameters = {
  qbits : int list option;
  cbits : int list option;
  occurrence : int option;
}

type applicable_rule = {
  name : string;
  param : string;
  occurrences : int;
}

let string_of_param_kind = function
  | ParamKind_None -> "none"
  | ParamKind_qbit1 -> "qbit1"
  | ParamKind_qbit2 -> "qbit2"
  | ParamKind_cbit_instr -> "cbit_instr"

let representative_parameter nq nc = function
  | ParamKind_None -> Some Param_None
  | ParamKind_qbit1 ->
      if nq <= 0 then None else Some (Param_qbit1 0)
  | ParamKind_qbit2 ->
      if nq < 2 then None else Some (Param_qbit2 (0, 1))
  | ParamKind_cbit_instr ->
      if nc <= 0 then None else Some (Param_cbit_instr (0, NopInstr))

let manual_requested = function
  | None -> false
  | Some { qbits; cbits; occurrence } ->
      Option.is_some qbits || Option.is_some cbits || Option.is_some occurrence

let manual_numeric_requested = function
  | None -> false
  | Some { qbits; cbits; _ } -> Option.is_some qbits || Option.is_some cbits

let validate_manual_values manual =
  let check_values name = function
    | None -> ()
    | Some values ->
        List.iter
          (fun value ->
            if value < 0 then
              failwith (Printf.sprintf "%s must contain non-negative integers." name))
          values
  in
  Option.iter
    (fun { qbits; cbits; occurrence } ->
      check_values "--qbits" qbits;
      check_values "--cbits" cbits;
      match occurrence with
      | Some value when value < 0 -> failwith "--occurrence must be non-negative."
      | _ -> ())
    manual

let require_arity option_name expected = function
  | None -> ()
  | Some values ->
      let actual = List.length values in
      if actual <> expected then
        failwith
          (Printf.sprintf "%s expects %d value(s), but got %d." option_name
             expected actual)

let manual_parameter rng nq nc spec manual =
  let qbits, cbits =
    match manual with
    | None -> (None, None)
    | Some { qbits; cbits; _ } -> (qbits, cbits)
  in
  let make_random () = random_parameter rng nq nc spec.transform_param_kind in
  match spec.transform_param_kind with
  | ParamKind_None ->
      require_arity "--qbits" 0 qbits;
      require_arity "--cbits" 0 cbits;
      Some Param_None
  | ParamKind_qbit1 -> (
      require_arity "--cbits" 0 cbits;
      match qbits with
      | Some [ qbit ] -> Some (Param_qbit1 qbit)
      | Some _ ->
          require_arity "--qbits" 1 qbits;
          None
      | None -> make_random ())
  | ParamKind_qbit2 -> (
      require_arity "--cbits" 0 cbits;
      match qbits with
      | Some [ qbit1; qbit2 ] -> Some (Param_qbit2 (qbit1, qbit2))
      | Some _ ->
          require_arity "--qbits" 2 qbits;
          None
      | None -> make_random ())
  | ParamKind_cbit_instr -> (
      require_arity "--qbits" 0 qbits;
      match cbits with
      | Some [ cbit ] ->
          if cbit >= nc then
            failwith
              (Printf.sprintf "Manual cbit %d is out of range for %d cbit(s)."
                 cbit nc);
          Some (Param_cbit_instr (cbit, random_instruction rng nq nc 2))
      | Some _ ->
          require_arity "--cbits" 1 cbits;
          None
      | None -> make_random ())

let validate_manual_parameter spec param =
  match spec.transform_rule param with
  | Some _ -> ()
  | None ->
      failwith
        (Printf.sprintf "Manual parameters are invalid for rule '%s'."
           spec.transform_name)

let validate_manual_occurrence spec occurrence count =
  if occurrence < 0 then failwith "--occurrence must be non-negative.";
  if occurrence >= count then
    failwith
      (Printf.sprintf
         "Occurrence %d is out of range for rule '%s' with %d occurrence(s)."
         occurrence spec.transform_name count)

let try_transform rng ?manual specs nq nc instr =
  let candidates =
    Array.fold_left
      (fun acc spec ->
        match manual_parameter rng nq nc spec manual with
        | None -> acc
        | Some param ->
            if manual_numeric_requested manual then validate_manual_parameter spec param;
            let count = transformSpec_count spec param instr in
            if count <= 0 then acc else (spec, param, count) :: acc)
      []
      specs
  in
  match candidates with
  | [] -> None
  | _ ->
      let spec, param, count =
        List.nth candidates (Random.State.int rng (List.length candidates))
      in
      let occurrence =
        match manual with
        | Some { occurrence = Some occurrence; _ } ->
            validate_manual_occurrence spec occurrence count;
            occurrence
        | _ -> Random.State.int rng count
      in
      transformSpec_apply spec param instr occurrence

let combined_specs nq specs =
  let base_specs = transform_spec_list nq in
  match specs with
  | None -> base_specs
  | Some extra_specs -> base_specs @ extra_specs

let ensure_unique_spec_names specs =
  let rec loop seen = function
    | [] -> specs
    | spec :: rest ->
        if List.exists (String.equal spec.transform_name) seen then
          failwith
            (Printf.sprintf "Duplicate transformation rule name '%s'."
               spec.transform_name)
        else loop (spec.transform_name :: seen) rest
  in
  loop [] specs

let applicable_rules ?specs instr nq nc =
  if instruction_qbits_validb nq instr then
    let specs = combined_specs nq specs |> ensure_unique_spec_names in
    specs
    |> List.filter_map (fun spec ->
           match representative_parameter nq nc spec.transform_param_kind with
           | None -> None
           | Some param ->
               let occurrences = transformSpec_count spec param instr in
               if occurrences <= 0 then None
               else
                 Some
                   {
                     name = spec.transform_name;
                     param = string_of_param_kind spec.transform_param_kind;
                     occurrences;
                   })
  else failwith "Instruction qbit index is not valid."

let filter_specs_by_name rule_name specs =
  let matched =
    List.filter (fun spec -> String.equal spec.transform_name rule_name) specs
  in
  match matched with
  | [] ->
      failwith
        (Printf.sprintf "No transformation rule named '%s'." rule_name)
  | _ -> matched

let unoptimize_with_state ?specs ?rule_name ?manual rng instr step nq nc =
  validate_manual_values manual;
  if manual_requested manual then (
    match rule_name with
    | Some _ -> ()
    | None -> failwith "Manual parameters require --rule.");
  if manual_requested manual && step <> 1 then
    failwith "Manual parameters require a single rewrite step.";
  let specs =
    let specs = combined_specs nq specs |> ensure_unique_spec_names in
    let specs =
      match rule_name with
      | None -> specs
      | Some name -> filter_specs_by_name name specs
    in
    Array.of_list
      specs
  in

  let rec loop successful_steps current =
    if successful_steps >= step
    then current
    else
      match try_transform rng ?manual specs nq nc current
      with
      | None ->
          let message =
            match rule_name with
            | None ->
                "No transformation rule matched before the requested step count was reached."
            | Some name ->
                Printf.sprintf
                  "Transformation rule '%s' is not applicable to the current instruction."
                  name
          in
          failwith message
      | Some next ->
          loop (successful_steps + 1) next
  in
  loop 0 instr

let unoptimize ?specs ?rule_name ?manual instr step nq nc =
  let rng =
    Random.State.make_self_init ()
  in
  if instruction_qbits_validb nq instr
  then unoptimize_with_state ?specs ?rule_name ?manual rng instr step nq nc
  else failwith "Instruction qbit index is not valid."
