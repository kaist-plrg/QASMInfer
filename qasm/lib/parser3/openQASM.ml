open Printf
open Lexing

(* Error handling adapted from Real World OCaml *)
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.mainprogram Lexer.token lexbuf with
  | Lexer.SyntaxError msg ->
      fprintf stderr "%a: %s\n" print_position lexbuf msg;
      []
  | Parser.Error ->
      fprintf stderr "%a: syntax error\n" print_position lexbuf;
      exit (-1)

(* core parsing routine *)
let get_ast f =
  let ch = open_in_bin f in
  Fun.protect
    ~finally:(fun () -> close_in ch)
    (fun () ->
      let lexbuf = Lexing.from_channel ch in
      parse_with_error lexbuf)
