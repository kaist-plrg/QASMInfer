val version : string
val describe : unit -> string

module Ast = Ast
module Desugar = Desugar

val parse_string : string -> Ast.program
val get_ast : string -> Ast.program
val inline_qelib : Ast.program -> Ast.program
val desugar : Ast.program -> int * int * Extracted.instruction * Desugar.QASMArg.t Desugar.IntMap.t * Desugar.QASMArg.t Desugar.IntMap.t
val string_of_instruction : Extracted.instruction -> string
