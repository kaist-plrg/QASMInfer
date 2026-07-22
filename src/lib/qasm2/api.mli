val version : string
val describe : unit -> string

module Ast = Ast
module Desugar = Desugar

val parse_string : string -> Ast.program
val parse_string_result : ?filename:string -> string -> (Ast.program, string) result
val get_ast : string -> Ast.program
val inline_qelib : Ast.program -> Ast.program
val desugar : Ast.program -> int * int * Extracted.instruction * Desugar.QASMArg.t Desugar.IntMap.t * Desugar.QASMArg.t Desugar.IntMap.t
val sugar : int -> int -> Desugar.QASMArg.t Desugar.IntMap.t -> Desugar.QASMArg.t Desugar.IntMap.t -> Extracted.instruction -> (Ast.program, string) result
val string_of_program : Ast.program -> string
val string_of_instruction : Extracted.instruction -> string
