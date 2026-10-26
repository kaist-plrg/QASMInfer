open Extracted

let require condition message = if not condition then failwith message
let id = RotateInstr (a0, a0, a0, 0)
let payload = MeasureInstr (0, 0)
let spec = contextualSpec_Insert_Dead_If_Bit 2

(* These explicitly numbered cases cover nested sequence sites that source
   parsers often flatten, both conditional outcomes, and enclosing prefixes. *)
let cases = [
  NopInstr, [0];
  SeqInstr [], [];
  SeqInstr [id; MeasureInstr (0, 0); id], [0; 1];
  SeqInstr [MeasureInstr (0, 1); ResetInstr 0; id], [0; 1; 2];
  SeqInstr [IfInstr (1, false, SeqInstr [id; MeasureInstr (0, 0); id]); id],
    [0; 1; 2];
  SeqInstr [IfInstr (0, true, MeasureInstr (0, 0)); id], [0; 1];
  SeqInstr [SeqInstr [id; MeasureInstr (0, 0)]; id], [0; 1; 2];
  SeqInstr [MeasureInstr (0, 0); IfInstr (1, false, id)], [0];
  SeqInstr [SeqInstr []; IfInstr (1, true, SeqInstr [id; id]); id],
    [0; 1; 2; 3; 4];
  IfInstr (1, false, SeqInstr [MeasureInstr (0, 1); id]), [0; 1; 2];
]

let () =
  List.iter (fun (instr, accepted) ->
    let param = Param_cbit_instr (0, payload) in
    let count = transformSpec_count spec.contextual_metadata param instr in
    require (count = dead_guard_site_count instr) "deep occurrence count changed";
    for index = 0 to count do
      let actual = spec.contextual_apply param instr index in
      require (Option.is_some actual = List.mem index accepted)
        (Printf.sprintf "wrong precondition at occurrence %d" index);
      Option.iter (fun result ->
        let pattern_result = transformSpec_apply spec.contextual_metadata param instr index in
        require (Option.map flatten_core pattern_result = Some (flatten_core result))
          "contextual insertion addresses a different deep site") actual
    done) cases;
  let named_gates = [CzInstr (0, 1); CyInstr (0, 1); ChInstr (0, 1);
    CsxInstr (0, 1); ToffoliInstr (0, 1, 2); CswapInstr (0, 1, 2);
    RccxInstr (0, 1, 2)] in
  let named_spec = contextualSpec_Insert_Dead_If_Bit 3 in
  List.iter (fun gate ->
    require (instruction_no_write 0 gate) "named gate marked as a classical write";
    let instr = SeqInstr [RotateInstr (aPI2, a0, aPI, 0);
      IfInstr (1, false, gate); MeasureInstr (0, 0); id] in
    let expected = execute_and_calculate_prob 3 2 instr in
    (* Sites 0/1/2/3 precede the measurement; site 4 follows it. *)
    for index = 0 to 4 do
      let actual = named_spec.contextual_apply (Param_cbit_instr (0, payload)) instr index in
      require (Option.is_some actual = (index < 4))
        "named-gate prefix changed dead-guard admissibility";
      Option.iter (fun result ->
        require (execute_and_calculate_prob 3 2 result = expected)
          "dead guard in a named-gate program changed the distribution") actual
    done) named_gates;
  let invalid = Param_cbit_instr (0, ResetInstr 2) in
  require (spec.contextual_apply invalid id 0 = None) "invalid payload accepted";
  require (spec.contextual_apply Param_None id 0 = None) "invalid parameter accepted";
  let bell = SeqInstr [RotateInstr (aPI2, a0, aPI, 0); CnotInstr (0, 1);
                       MeasureInstr (0, 0); MeasureInstr (1, 1)] in
  let probabilities instruction = execute_and_calculate_prob 2 2 instruction in
  let expected = probabilities bell in
  let payloads = ref [] in
  for seed = 0 to 31 do
    let manual = { Unoptimize.qbits = None; cbits = Some [1];
                   occurrence = Some 3; instr = None } in
    let result = Unoptimize.unoptimize ~rule_name:"Insert_Dead_If_Bit"
      ~manual ~random_1q:true ~seed ~on_dead_guard:(fun choice ->
        require (choice.payload_policy = "random-1q") "missing payload policy";
        (match choice.payload with RotateInstr (_, _, _, q) ->
          require (q >= 0 && q < 2) "invalid random qubit"
        | _ -> failwith "random payload is not a one-qubit gate");
        payloads := choice.payload :: !payloads) bell 1 2 2 in
    require (probabilities result = expected) "dead payload changed the distribution"
  done;
  require (List.length (List.sort_uniq compare !payloads) > 1) "payload did not vary";
  print_endline "dead guard: 10 deep-site cases, ordinal agreement, seven named-gate prefixes, payload checks, 32 seeded semantic checks passed"
