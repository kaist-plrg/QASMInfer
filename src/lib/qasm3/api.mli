module Ast = Ast
module Desugar : module type of Desugar

val get_ast : string -> Ast.program
val inline_qelib : Ast.program -> Ast.program
val desugar : Ast.statement list -> Desugar.Ast2.statement list
