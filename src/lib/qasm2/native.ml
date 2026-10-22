open Ast
open Extracted

(* Native markers are introduced by inline_qelib, never by the parser for a
   user declaration.  In particular a user-defined gate named cz is a macro. *)
let names = [ "cz"; "cy"; "ch"; "csx"; "ccx"; "cswap"; "rccx" ]

let instruction name qbits =
  match name, qbits with
  | "cz", [ a; b ] -> CzInstr (a, b)
  | "cy", [ a; b ] -> CyInstr (a, b)
  | "ch", [ a; b ] -> ChInstr (a, b)
  | "csx", [ a; b ] -> CsxInstr (a, b)
  | "ccx", [ a; b; c ] -> ToffoliInstr (a, b, c)
  | "cswap", [ a; b; c ] -> CswapInstr (a, b, c)
  | "rccx", [ a; b; c ] -> RccxInstr (a, b, c)
  | _ -> invalid_arg ("invalid native qelib1 gate: " ^ name)

let named_instruction = function
  | CzInstr (a, b) -> Some ("cz", [ a; b ])
  | CyInstr (a, b) -> Some ("cy", [ a; b ])
  | ChInstr (a, b) -> Some ("ch", [ a; b ])
  | CsxInstr (a, b) -> Some ("csx", [ a; b ])
  | ToffoliInstr (a, b, c) -> Some ("ccx", [ a; b; c ])
  | CswapInstr (a, b, c) -> Some ("cswap", [ a; b; c ])
  | RccxInstr (a, b, c) -> Some ("rccx", [ a; b; c ])
  | _ -> None

let mark_declaration = function
  | GateDecl ((name, [], args) as head, _) when List.mem name names ->
      GateDecl (head, [ GUop (Native (name, List.map (fun arg -> arg, None) args)) ])
  | statement -> statement

(* stdgates.inc lacks these two names.  Their local declarations use only its
   parameter-free gates.  Recognize precisely these declarations on OQ3 input
   to preserve the native instructions across an emit/parse round trip. *)
let local_declarations = [
  GateDecl (("csx", [], [ "a"; "b" ]), [
    GUop (Gate ("h", [], [ ( "b", None ) ]));
    GUop (Gate ("t", [], [ ( "a", None ) ]));
    GUop (Gate ("cx", [], [ ( "a", None ); ( "b", None ) ]));
    GUop (Gate ("tdg", [], [ ( "b", None ) ]));
    GUop (Gate ("cx", [], [ ( "a", None ); ( "b", None ) ]));
    GUop (Gate ("t", [], [ ( "b", None ) ]));
    GUop (Gate ("h", [], [ ( "b", None ) ]));
  ]);
  GateDecl (("rccx", [], [ "a"; "b"; "c" ]), [
    GUop (Gate ("h", [], [ ( "c", None ) ]));
    GUop (Gate ("t", [], [ ( "c", None ) ]));
    GUop (Gate ("cx", [], [ ( "b", None ); ( "c", None ) ]));
    GUop (Gate ("tdg", [], [ ( "c", None ) ]));
    GUop (Gate ("cx", [], [ ( "a", None ); ( "c", None ) ]));
    GUop (Gate ("t", [], [ ( "c", None ) ]));
    GUop (Gate ("cx", [], [ ( "b", None ); ( "c", None ) ]));
    GUop (Gate ("tdg", [], [ ( "c", None ) ]));
    GUop (Gate ("h", [], [ ( "c", None ) ]));
  ]);
 ]

let recognize_local_declaration statement =
  if List.mem statement local_declarations then mark_declaration statement
  else statement
