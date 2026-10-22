module E = Extracted
module Q2 = Qasm2.Api
module Q3 = Qasm3.Api

let require condition message = if not condition then failwith message
let ok = function Ok x -> x | Error e -> failwith e
let parse source = source |> Q2.parse_string |> Q2.inline_qelib |> Q2.desugar
let preamble = {|OPENQASM 2.0; include "qelib1.inc"; qreg q[4]; creg c[4];
|}
let instruction source = let _, _, i, _, _ = parse (preamble ^ source) in i

(* Independent literal expansions of qelib1 bodies, with cu1(pi/2) expanded
   in csx and ccx expanded in cswap.  They also exercise exact rule admission. *)
let gates = [
  ("cz", [ 0; 1 ], E.CzInstr (0, 1),
    {|h q[1]; cx q[0],q[1]; h q[1];|},
    {|{ "gate": "cz", "control": 0, "target": 1 }|});
  ("cy", [ 0; 1 ], E.CyInstr (0, 1),
    {|sdg q[1]; cx q[0],q[1]; s q[1];|},
    {|{ "gate": "cy", "control": 0, "target": 1 }|});
  ("ch", [ 0; 1 ], E.ChInstr (0, 1),
    {|h q[1]; sdg q[1]; cx q[0],q[1]; h q[1]; t q[1]; cx q[0],q[1]; t q[1]; h q[1]; s q[1]; x q[1]; s q[0];|},
    {|{ "gate": "ch", "control": 0, "target": 1 }|});
  ("csx", [ 0; 1 ], E.CsxInstr (0, 1),
    {|h q[1]; t q[0]; cx q[0],q[1]; tdg q[1]; cx q[0],q[1]; t q[1]; h q[1];|},
    {|{ "gate": "csx", "control": 0, "target": 1 }|});
  ("ccx", [ 0; 1; 2 ], E.ToffoliInstr (0, 1, 2),
    {|h q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[1]; t q[2]; h q[2]; cx q[0],q[1]; t q[0]; tdg q[1]; cx q[0],q[1];|},
    {|{ "gate": "ccx", "control1": 0, "control2": 1, "target": 2 }|});
  ("cswap", [ 0; 1; 2 ], E.CswapInstr (0, 1, 2),
    {|cx q[2],q[1]; h q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[1]; t q[2]; h q[2]; cx q[0],q[1]; t q[0]; tdg q[1]; cx q[0],q[1]; cx q[2],q[1];|},
    {|{ "gate": "cswap", "control": 0, "q1": 1, "q2": 2 }|});
  ("rccx", [ 0; 1; 2 ], E.RccxInstr (0, 1, 2),
    {|h q[2]; t q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[2]; cx q[1],q[2]; tdg q[2]; h q[2];|},
    {|{ "gate": "rccx", "control1": 0, "control2": 1, "target": 2 }|});
 ]

let call name wires = name ^ " " ^
  String.concat "," (List.map (Printf.sprintf "q[%d]") wires) ^ ";"

let leaves = function E.SeqInstr is -> is | i -> [i]

let round_trip () =
  let singles = "id q[0]; x q[0]; y q[0]; z q[0]; h q[0]; s q[0]; sdg q[0]; t q[0]; tdg q[0]; sx q[0]; sxdg q[0]; cx q[0],q[1]; swap q[0],q[1]; " in
  let source = singles ^ String.concat " " (List.map (fun (name, wires, _, _, _) -> call name wires) gates) in
  let nq,nc,i,qa,ca = parse (preamble ^ source) in
  require (List.length (leaves i) = 20) "vocabulary must be 20 atomic instructions";
  List.iter (fun (_,_,expected,_,_) -> require (List.mem expected (leaves i)) "parser expanded a composite") gates;
  let i = Unoptimize.unoptimize ~seed:1 i 0 nq nc in
  List.iter (fun dialect ->
    let emit i = if dialect = 2 then Q2.sugar nq nc qa ca i |> ok |> Q2.string_of_program
                 else Q3.sugar nq nc qa ca i |> ok |> Q3.string_of_program in
    let text = emit i in
    let _,_,again,_,_ = if dialect=2 then parse text else
      text |> Q3.parse_string |> Q3.desugar |> Q2.inline_qelib |> Q2.desugar in
    require (i = again) "named composite round trip changed AST";
    require (text = emit again) "composite emission is not a fixed point") [2;3]

let declarations_and_broadcast () =
  let _,_,native,_,_ = {|OPENQASM 3.0; include "qelib1.inc";
    qubit[3] q; ccx q[0],q[1],q[2]; rccx q[0],q[1],q[2];|}
    |> Q3.parse_string |> Q3.inline_qelib |> Q3.desugar |> Q2.desugar in
  require (leaves native = [E.ToffoliInstr(0,1,2); E.RccxInstr(0,1,2)])
    "QASM3 direct include API expanded native gates";

  let _,_,i,_,_ = parse {|OPENQASM 2.0; include "qelib1.inc";
    gate cz a,b { x a; } qreg q[2]; cz q[0],q[1];|} in
  require (not (List.exists (function E.CzInstr _ -> true | _ -> false) (leaves i)))
    "a user gate named cz was treated as a builtin";
  let _,_,i,_,_ = parse {|OPENQASM 2.0; include "qelib1.inc";
    gate wrapper a,b,c { ccx a,b,c; } qreg a[2]; qreg b[2]; qreg c[2]; wrapper a,b,c;|} in
  require (leaves i = [E.ToffoliInstr(0,2,4); E.ToffoliInstr(1,3,5)])
    "broadcast or user wrapper lost composite wire roles";
  List.iter (fun body ->
    try ignore (instruction body); failwith "wrong arity accepted"
    with Failure message -> require (message <> "wrong arity accepted") message)
    ["ccx q[0],q[1];"; "ccx(pi) q[0],q[1],q[2];"; "cz q[0],q[4];"];
  let source = {|OPENQASM 3.0; include "stdgates.inc";
    gate csx a,b { x a; } qubit[2] q; csx q[0],q[1];|} in
  let _,_,i,_,_ = source |> Q3.parse_string |> Q3.desugar |> Q2.inline_qelib |> Q2.desugar in
  require (not (List.exists (function E.CsxInstr _ -> true | _ -> false) (leaves i)))
    "noncanonical OQ3 local declaration was recognized as csx"

let distribution i =
  E.execute_and_calculate_prob 4 4 i
  |> List.map (fun (state,p) -> Big_int_Z.int_of_big_int state, E.RbaseSymbolsImpl.coq_Rrepr p)
let same_distribution left right =
  let left = distribution left and right = distribution right in
  let keys = List.sort_uniq compare (List.map fst left @ List.map fst right) in
  let get xs k = Option.value ~default:0. (List.assoc_opt k xs) in
  List.iter (fun k -> require (Float.abs (get left k -. get right k) < 1e-12)
    "native gate differs from its qelib1 body") keys

let semantics () =
  List.iter (fun (name,wires,_,body,_) ->
    (* All basis states plus phase-sensitive, entangled contexts on four wires. *)
    for basis=0 to 15 do
      let prefix = List.init 4 (fun q -> if basis land (1 lsl q) <> 0 then call "x" [q] else "") |> String.concat " " in
      let prefix = prefix ^ " h q[0]; h q[1]; h q[2]; cx q[2],q[3]; t q[1]; " in
      let suffix = " h q[0]; h q[1]; h q[2]; measure q -> c;" in
      same_distribution (instruction (prefix ^ call name wires ^ suffix))
        (instruction (prefix ^ body ^ suffix))
    done) gates

let spec name lhs rhs =
  match E.standard_rule_of_sequences 4 name lhs rhs with
  | Some s -> s
  | None -> failwith ("valid composite rule rejected: " ^ name)

let exact_bodies () =
  let standard_of_instruction = function
    | E.CnotInstr (a,b) -> E.SPG_Cnot(a,b)
    | E.RotateInstr (a,b,c,q) ->
        let gate = match Qasm2.Sugar.sugar_standard_gate (a,b,c) with
          | Some "h" -> E.Std_H | Some "x" -> E.Std_X
          | Some "s" -> E.Std_S | Some "sdg" -> E.Std_Sdg
          | Some "t" -> E.Std_T | Some "tdg" -> E.Std_Tdg
          | _ -> failwith "unexpected primitive body gate"
        in
        E.SPG_Std(gate,q)
    | _ -> failwith "body not primitive"
  in
  let patterns = [E.SPG_Cz(0,1); E.SPG_Cy(0,1); E.SPG_Ch(0,1); E.SPG_Csx(0,1);
    E.SPG_Toffoli(0,1,2); E.SPG_Cswap(0,1,2); E.SPG_Rccx(0,1,2)] in
  List.iter2 (fun (name,_,_,body,_) pattern ->
    ignore (spec name [pattern] (List.map standard_of_instruction (leaves (instruction body))))) gates patterns;
  require (E.standard_rule_of_sequences 3 "relative" [E.SPG_Rccx(0,1,2)] [E.SPG_Toffoli(0,1,2)] = None)
    "relative phase was erased from rccx";
  require (E.standard_rule_of_sequences 2 "csx_squared" [E.SPG_Csx(0,1);E.SPG_Csx(0,1)]
    [E.SPG_Std(E.Std_I,0);E.SPG_Std(E.Std_I,1)] = None) "csx was treated as self-inverse"

let with_rules text f =
  let path = Filename.temp_file "qelib-rules" ".json" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    let out = open_out path in output_string out text; close_out out;
    f (Unoptimize.specs_of_rule_file 4 path))

let admission_and_addressing () =
  List.iter (fun (name,_,_,_,json) ->
    with_rules ("[{\"name\":\"identity\",\"lhs\":["^json^"],\"rhs\":["^json^"]}]")
      (fun result -> require (List.length (ok result) = 1) ("rule decoder rejected "^name))) gates;
  List.iter (fun json -> with_rules ("[{\"lhs\":["^json^"],\"rhs\":["^json^"]}]")
      (function Error _ -> () | Ok _ -> failwith "duplicate wires accepted"))
    [{|{"gate":"cz","control":0,"target":0}|};
     {|{"gate":"ccx","control1":0,"control2":1,"target":0}|};
     {|{"gate":"cswap","control":1,"q1":1,"q2":2}|};
     {|{"gate":"rccx","control1":9,"control2":9,"target":10}|}];
  let rules = [{|{"name":"cancel","lhs":[{"gate":"ccx","control1":0,"control2":1,"target":2},{"gate":"ccx","control1":0,"control2":1,"target":2}],"rhs":[]}|}] in
  with_rules ("["^String.concat "," rules^"]") (fun result ->
    let specs = ok result in
    let i = instruction "ccx q[0],q[1],q[2]; ccx q[0],q[1],q[2]; if(c==0) ccx q[2],q[0],q[1]; if(c==0) ccx q[2],q[0],q[1]; ccx q[2],q[0],q[1]; ccx q[2],q[0],q[1];" in
    let manual = {Unoptimize.qbits=Some [2;0;1];cbits=None;occurrence=Some 0;instr=None} in
    let out = Unoptimize.unoptimize ~specs ~rule_name:"cancel" ~manual ~seed:0 i 1 4 4 in
    require (List.length (leaves out) = List.length (leaves i)-2) "manual qbits did not select a three-wire match";
    require (List.hd (leaves out) = E.ToffoliInstr(0,1,2)) "manual qbits selected the wrong role ordering")

let swaps_and_guards () =
  let original = E.SeqInstr (List.map (fun (_,_,i,_,_) -> i) gates) in
  let manual = {Unoptimize.qbits=Some [0;3];cbits=None;occurrence=Some 0;instr=None} in
  let swapped = Unoptimize.unoptimize ~rule_name:"Insert_Swap" ~manual ~seed:0 original 1 4 4 in
  let remap q = if q=0 then 3 else if q=3 then 0 else q in
  let expected = E.SwapInstr(0,3) :: List.map (fun (name,wires,_,_,_) ->
    Qasm2.Native.instruction name (List.map remap wires)) gates in
  require (leaves swapped = expected) "Insert_Swap failed to remap native wires";
  List.iter (fun (_,_,i,_,_) ->
    let guarded = E.IfInstr(0,true,i) in
    let out = Unoptimize.unoptimize ~rule_name:"Double_If_True" ~seed:0 guarded 1 4 4 in
    require (out = E.IfInstr(0,true,E.IfInstr(0,true,i))) "conditional pattern lost native instruction") gates

let () = List.iter (fun (name,test) ->
  try test () with exn -> failwith (name ^ ": " ^ Printexc.to_string exn))
  ["round trip",round_trip; "declarations",declarations_and_broadcast;
   "semantics",semantics; "exact bodies",exact_bodies;
   "admission",admission_and_addressing; "builtins",swaps_and_guards]
