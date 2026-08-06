open Extracted

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

let string_of_gate = standard_gate_name

let string_of_gate_list gates =
  gates |> List.map string_of_gate |> String.concat " "

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

let gate_list_field rule_name fields key =
  match List.assoc_opt key fields with
  | Some (`List values) ->
      result_map_list
        (function
          | `String gate_name -> (
              let normalized = String.lowercase_ascii gate_name in
              match gate_of_string normalized with
              | Some gate -> Ok gate
              | None ->
                  Error
                    (Printf.sprintf
                       "rule %s field '%s' contains unknown standard gate '%s'"
                       rule_name key gate_name))
          | _ ->
              Error
                (Printf.sprintf
                   "rule %s field '%s' must contain only strings"
                   rule_name key))
        values
  | Some _ ->
      Error
        (Printf.sprintf "rule %s field '%s' must be an array" rule_name key)
  | None -> Error (Printf.sprintf "rule %s is missing field '%s'" rule_name key)

let rule_jsons_of_json = function
  | `List rules -> Ok rules
  | `Assoc fields -> (
      match List.assoc_opt "rules" fields with
      | Some (`List rules) -> Ok rules
      | Some _ -> Error "field 'rules' must be an array"
      | None -> Error "rule file must be an array or an object with a 'rules' array")
  | _ -> Error "rule file must be an array of rule objects"

let spec_of_rule_json index = function
  | `Assoc fields ->
      let fallback_name = Printf.sprintf "rule_%d" (index + 1) in
      let name =
        match List.assoc_opt "name" fields with
        | Some (`String value) -> Ok value
        | Some _ ->
            Error
              (Printf.sprintf "rule %s field 'name' must be a string"
                 fallback_name)
        | None -> Ok fallback_name
      in
      result_bind name (fun name ->
          result_bind (gate_list_field name fields "lhs") (fun lhs ->
              result_bind (gate_list_field name fields "rhs") (fun rhs ->
                  match standard_rule_of_sequences lhs rhs with
                  | Some rule -> Ok (transformSpec_simple_rule name rule)
                  | None ->
                      Error
                        (Printf.sprintf
                           "rule #%d %s (%s -> %s) is not valid up to global omega phase"
                           (index + 1) name (string_of_gate_list lhs)
                           (string_of_gate_list rhs)))))
  | _ -> Error (Printf.sprintf "rule %d must be an object" (index + 1))

let specs_of_rule_file path =
  try
    let json = Yojson.Safe.from_file path in
    result_bind (rule_jsons_of_json json) (fun rule_jsons ->
        match rule_jsons with
        | [] -> Error "rule file must contain at least one rule"
        | _ -> result_map_list (fun (index, json) -> spec_of_rule_json index json)
                 (List.mapi (fun index json -> (index, json)) rule_jsons))
  with
  | Sys_error message -> Error message
  | Yojson.Json_error message -> Error ("invalid JSON: " ^ message)

let random_parameter rng nq param_count =
  match param_count with
  | 0 ->
      Some Param_None
  | 1 ->
      if nq <= 0 then None
      else
        Some
          (Param_qbit1
             (Random.State.int rng nq))
  | 2 ->
      if nq <= 0 then None
      else
        Some
          (Param_qbit2
             (Random.State.int rng nq,
              Random.State.int rng nq))
  | _ ->
      None

let try_transform rng specs nq instr =
  let candidates =
    Array.fold_left
      (fun acc spec ->
    match random_parameter rng nq spec.param_count with
    | None -> acc
    | Some param ->
      let count = transformSpec_count spec param instr in
      if count <= 0
          then acc
      else
          (spec, param, count) :: acc)
      []
      specs
  in
  match candidates with
  | [] -> None
  | _ ->
      let spec, param, count =
        List.nth candidates (Random.State.int rng (List.length candidates))
      in
      let occurrence = Random.State.int rng count in
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

let filter_specs_by_name rule_name specs =
  let matched =
    List.filter (fun spec -> String.equal spec.transform_name rule_name) specs
  in
  match matched with
  | [] ->
      failwith
        (Printf.sprintf "No transformation rule named '%s'." rule_name)
  | _ -> matched

let unoptimize_with_state ?specs ?rule_name rng instr step nq =
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
      match try_transform rng specs nq current
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

let unoptimize ?specs ?rule_name instr step nq =
  let rng =
    Random.State.make_self_init ()
  in
  if instruction_qbits_validb nq instr
  then unoptimize_with_state ?specs ?rule_name rng instr step nq
  else failwith "Instruction qbit index is not valid."
