module Ast = Ast
module Desugar : module type of Desugar

val get_ast : string -> Ast.program
val parse_string : string -> Ast.program
val parse_string_result : ?filename:string -> string -> (Ast.program, string) result
val inline_qelib : Ast.program -> Ast.program
val desugar : Ast.statement list -> Desugar.Ast2.statement list

(** Render a QASMCore instruction as OpenQASM 3.  Unlike the OpenQASM 2 sugar
    this cannot fail on program shape: every QASMCore conditional nests, and
    OpenQASM 3 conditionals nest too.  It still fails on bit assignments that do
    not describe a register layout, and on register names OpenQASM 3 reserves. *)
val sugar :
  int ->
  int ->
  Qasm2.Desugar.QASMArg.t Qasm2.Desugar.IntMap.t ->
  Qasm2.Desugar.QASMArg.t Qasm2.Desugar.IntMap.t ->
  Extracted.instruction ->
  (Ast.program, string) result

val string_of_program : Ast.program -> string
