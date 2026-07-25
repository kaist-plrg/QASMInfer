open Extracted

let unoptimize_nop instruction = instruction

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
  let spec_count = Array.length specs in
  if spec_count = 0 then
    None
  else
    let spec =
      specs.(Random.State.int rng spec_count)
    in
    match
      random_parameter
        rng
        nq
        spec.param_count
    with
    | None ->
        None
    | Some param ->
        let count =
          transformSpec_count spec param instr
        in
        if count <= 0 then
          None
        else
          let occurrence = Random.State.int rng count
          in
          transformSpec_apply spec param instr occurrence

let unoptimize_with_state rng instr nq =
  let specs =
    Array.of_list
      (transform_spec_list nq)
  in

  let rec loop successful_steps current =
    if successful_steps >= 100 then
      current
    else
      match
        try_transform
          rng
          specs
          nq
          current
      with
      | None ->
          (* 실패는 step으로 세지 않는다. *)
          loop successful_steps current
      | Some next ->
          (* count 이내의 occurrence이면 syntactically
             different하다는 Rocq 증명을 신뢰한다. *)
          loop
            (successful_steps + 1)
            next
  in
  loop 0 instr

let unoptimize instr nq =
  let rng =
    Random.State.make_self_init ()
  in
  unoptimize_with_state rng instr nq
