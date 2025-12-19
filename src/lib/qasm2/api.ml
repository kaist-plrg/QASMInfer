open Printf
open Lexing
open Ast

module Parser = Parser
module Lexer = Lexer
module Desugar = Desugar

[@@@warning "-32"]

let version = "qasm2"
let describe () = "OpenQASM 2 parser (stub wiring; fill in semantics as needed)."

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

let parse_string s =
  let lexbuf = Lexing.from_string s in
  parse_with_error lexbuf

let desugar = Desugar.desugar

let string_of_instruction = Stringifier.string_of_instruction

module Ast = Ast

let qelib_decl =
  [
    GateDecl
      ( ("u3", [ "theta"; "phi"; "lambda" ], [ "q" ]),
        [ GUop (U ([ Id "theta"; Id "phi"; Id "lambda" ], ("q", None))) ] );
    GateDecl
      ( ("u2", [ "phi"; "lambda" ], [ "q" ]),
        [
          GUop
            (U
               ( [ BinaryOp (Div, Pi, Nninteger 2); Id "phi"; Id "lambda" ],
                 ("q", None) ));
        ] );
    GateDecl
      ( ("u1", [ "lambda" ], [ "q" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Id "lambda" ], ("q", None))) ] );
    GateDecl (("cx", [], [ "c"; "t" ]), [ GUop (CX (("c", None), ("t", None))) ]);
    GateDecl
      ( ("id", [], [ "a" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Nninteger 0 ], ("a", None))) ] );
    GateDecl
      ( ("u0", [ "gamma" ], [ "q" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Nninteger 0 ], ("q", None))) ] );
    GateDecl
      ( ("u", [ "theta"; "phi"; "lambda" ], [ "q" ]),
        [ GUop (U ([ Id "theta"; Id "phi"; Id "lambda" ], ("q", None))) ] );
    GateDecl
      ( ("p", [ "lambda" ], [ "q" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Id "lambda" ], ("q", None))) ] );
    GateDecl
      ( ("x", [], [ "a" ]),
        [ GUop (Gate ("u3", [ Pi; Nninteger 0; Pi ], [ ("a", None) ])) ] );
    GateDecl
      ( ("y", [], [ "a" ]),
        [
          GUop
            (Gate
               ( "u3",
                 [
                   Pi;
                   BinaryOp (Div, Pi, Nninteger 2);
                   BinaryOp (Div, Pi, Nninteger 2);
                 ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      (("z", [], [ "a" ]), [ GUop (Gate ("u1", [ Pi ], [ ("a", None) ])) ]);
    GateDecl
      ( ("h", [], [ "a" ]),
        [ GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("a", None) ])) ] );
    GateDecl
      ( ("s", [], [ "a" ]),
        [
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 2) ], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("sdg", [], [ "a" ]),
        [
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2) ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("t", [], [ "a" ]),
        [
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("tdg", [], [ "a" ]),
        [
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("rx", [ "theta" ], [ "a" ]),
        [
          GUop
            (Gate
               ( "u3",
                 [
                   Id "theta";
                   BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2);
                   BinaryOp (Div, Pi, Nninteger 2);
                 ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("ry", [ "theta" ], [ "a" ]),
        [
          GUop
            (Gate
               ("u3", [ Id "theta"; Nninteger 0; Nninteger 0 ], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("rz", [ "phi" ], [ "a" ]),
        [ GUop (Gate ("u1", [ Id "phi" ], [ ("a", None) ])) ] );
    GateDecl
      ( ("sx", [], [ "a" ]),
        [
          GUop (Gate ("sdg", [], [ ("a", None) ]));
          GUop (Gate ("h", [], [ ("a", None) ]));
          GUop (Gate ("sdg", [], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("sxdg", [], [ "a" ]),
        [
          GUop (Gate ("s", [], [ ("a", None) ]));
          GUop (Gate ("h", [], [ ("a", None) ]));
          GUop (Gate ("s", [], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("cz", [], [ "a"; "b" ]),
        [
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
        ] );
    GateDecl
      ( ("cy", [], [ "a"; "b" ]),
        [
          GUop (Gate ("sdg", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("s", [], [ ("b", None) ]));
        ] );
    GateDecl
      ( ("swap", [], [ "a"; "b" ]),
        [
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("a", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("ch", [], [ "a"; "b" ]),
        [
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("sdg", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("t", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("t", [], [ ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("s", [], [ ("b", None) ]));
          GUop (Gate ("x", [], [ ("b", None) ]));
          GUop (Gate ("s", [], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("ccx", [], [ "a"; "b"; "c" ]),
        [
          GUop (Gate ("h", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop (Gate ("tdg", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("t", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop (Gate ("tdg", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("t", [], [ ("b", None) ]));
          GUop (Gate ("t", [], [ ("c", None) ]));
          GUop (Gate ("h", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("t", [], [ ("a", None) ]));
          GUop (Gate ("tdg", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("cswap", [], [ "a"; "b"; "c" ]),
        [
          GUop (Gate ("cx", [], [ ("c", None); ("b", None) ]));
          GUop (Gate ("ccx", [], [ ("a", None); ("b", None); ("c", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("crx", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 2) ], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2);
                   Nninteger 0;
                   Nninteger 0;
                 ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, Id "lambda", Nninteger 2);
                   BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2);
                   Nninteger 0;
                 ],
                 [ ("b", None) ] ));
        ] );
    GateDecl
      ( ("cry", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "ry",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "ry",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("crz", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "rz",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "rz",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("cu1", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("a", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
        ] );
    GateDecl
      ( ("cp", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("a", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
        ] );
    GateDecl
      ( ("cu3", [ "theta"; "phi"; "lambda" ], [ "c"; "t" ]),
        [
          GUop
            (Gate
               ( "u1",
                 [
                   BinaryOp
                     (Div, BinaryOp (Plus, Id "lambda", Id "phi"), Nninteger 2);
                 ],
                 [ ("c", None) ] ));
          GUop
            (Gate
               ( "u1",
                 [
                   BinaryOp
                     (Div, BinaryOp (Minus, Id "lambda", Id "phi"), Nninteger 2);
                 ],
                 [ ("t", None) ] ));
          GUop (Gate ("cx", [], [ ("c", None); ("t", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, UnaryOp (UMinus, Id "theta"), Nninteger 2);
                   Nninteger 0;
                   BinaryOp
                     ( Div,
                       UnaryOp (UMinus, BinaryOp (Plus, Id "phi", Id "lambda")),
                       Nninteger 2 );
                 ],
                 [ ("t", None) ] ));
          GUop (Gate ("cx", [], [ ("c", None); ("t", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, Id "theta", Nninteger 2);
                   Id "phi";
                   Nninteger 0;
                 ],
                 [ ("t", None) ] ));
        ] );
    GateDecl
      ( ("csx", [], [ "a"; "b" ]),
        [
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, Pi, Nninteger 2) ],
                 [ ("a", None); ("b", None) ] ));
          GUop (Gate ("h", [], [ ("b", None) ]));
        ] );
    GateDecl
      ( ("cu", [ "theta"; "phi"; "lambda"; "gamma" ], [ "c"; "t" ]),
        [
          GUop (Gate ("p", [ Id "gamma" ], [ ("c", None) ]));
          GUop
            (Gate
               ( "p",
                 [
                   BinaryOp
                     (Div, BinaryOp (Plus, Id "lambda", Id "phi"), Nninteger 2);
                 ],
                 [ ("c", None) ] ));
          GUop
            (Gate
               ( "p",
                 [
                   BinaryOp
                     (Div, BinaryOp (Minus, Id "lambda", Id "phi"), Nninteger 2);
                 ],
                 [ ("t", None) ] ));
          GUop (Gate ("cx", [], [ ("c", None); ("t", None) ]));
          GUop
            (Gate
               ( "u",
                 [
                   BinaryOp (Div, UnaryOp (UMinus, Id "theta"), Nninteger 2);
                   Nninteger 0;
                   BinaryOp
                     ( Div,
                       UnaryOp (UMinus, BinaryOp (Plus, Id "phi", Id "lambda")),
                       Nninteger 2 );
                 ],
                 [ ("t", None) ] ));
          GUop (Gate ("cx", [], [ ("c", None); ("t", None) ]));
          GUop
            (Gate
               ( "u",
                 [
                   BinaryOp (Div, Id "theta", Nninteger 2);
                   Id "phi";
                   Nninteger 0;
                 ],
                 [ ("t", None) ] ));
        ] );
    GateDecl
      ( ("rxx", [ "theta" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "u3",
                 [ BinaryOp (Div, Pi, Nninteger 2); Id "theta"; Nninteger 0 ],
                 [ ("a", None) ] ));
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("u1", [ UnaryOp (UMinus, Id "theta") ], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop
            (Gate
               ( "u2",
                 [ UnaryOp (UMinus, Pi); BinaryOp (Minus, Pi, Id "theta") ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("rzz", [ "theta" ], [ "a"; "b" ]),
        [
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("u1", [ Id "theta" ], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("rccx", [], [ "a"; "b"; "c" ]),
        [
          GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("c", None) ]));
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("c", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("c", None) ] ));
          GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("c", None) ]));
        ] );
    GateDecl
      ( ("rc3x", [], [ "a"; "b"; "c"; "d" ]),
        [
          GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("d", None) ]));
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("d", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("d", None) ] ));
          GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("d", None) ]));
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("d", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("d", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("d", None) ]));
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("d", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("d", None) ] ));
          GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("d", None) ]));
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("d", None) ]));
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("d", None) ] ));
          GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("d", None) ]));
        ] );
    GateDecl
      ( ("c3x", [], [ "a"; "b"; "c"; "d" ]),
        [
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("a", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("b", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("c", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("c", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("c", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("d", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("d", None) ] ));
          GUop (Gate ("cx", [], [ ("b", None); ("d", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("d", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("d", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("d", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("d", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("d", None) ] ));
          GUop (Gate ("cx", [], [ ("b", None); ("d", None) ]));
          GUop
            (Gate ("p", [ BinaryOp (Div, Pi, Nninteger 8) ], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("d", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("d", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("d", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
        ] );
    GateDecl
      ( ("c3sqrtx", [], [ "a"; "b"; "c"; "d" ]),
        [
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, Pi, Nninteger 8) ],
                 [ ("a", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("b", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, Pi, Nninteger 8) ],
                 [ ("b", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("c", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, Pi, Nninteger 8) ],
                 [ ("c", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 8) ],
                 [ ("c", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("h", [], [ ("d", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, Pi, Nninteger 8) ],
                 [ ("c", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("d", None) ]));
        ] );
    GateDecl
      ( ("c4x", [], [ "a"; "b"; "c"; "d"; "e" ]),
        [
          GUop (Gate ("h", [], [ ("e", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, Pi, Nninteger 2) ],
                 [ ("d", None); ("e", None) ] ));
          GUop (Gate ("h", [], [ ("e", None) ]));
          GUop
            (Gate
               ( "c3x",
                 [],
                 [ ("a", None); ("b", None); ("c", None); ("d", None) ] ));
          GUop (Gate ("h", [], [ ("e", None) ]));
          GUop
            (Gate
               ( "cu1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2) ],
                 [ ("d", None); ("e", None) ] ));
          GUop (Gate ("h", [], [ ("e", None) ]));
          GUop
            (Gate
               ( "c3x",
                 [],
                 [ ("a", None); ("b", None); ("c", None); ("d", None) ] ));
          GUop
            (Gate
               ( "c3sqrtx",
                 [],
                 [ ("a", None); ("b", None); ("c", None); ("e", None) ] ));
        ] );
  ]

let stdgates_decl =
  [
    GateDecl
      ( ("u3", [ "theta"; "phi"; "lambda" ], [ "q" ]),
        [ GUop (U ([ Id "theta"; Id "phi"; Id "lambda" ], ("q", None))) ] );
    GateDecl
      ( ("u2", [ "phi"; "lambda" ], [ "q" ]),
        [
          GUop
            (U
               ( [ BinaryOp (Div, Pi, Nninteger 2); Id "phi"; Id "lambda" ],
                 ("q", None) ));
        ] );
    GateDecl
      ( ("u1", [ "lambda" ], [ "q" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Id "lambda" ], ("q", None))) ] );
    GateDecl (("cx", [], [ "c"; "t" ]), [ GUop (CX (("c", None), ("t", None))) ]);
    GateDecl
      ( ("id", [], [ "a" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Nninteger 0 ], ("a", None))) ] );
    GateDecl
      ( ("p", [ "lambda" ], [ "q" ]),
        [ GUop (U ([ Nninteger 0; Nninteger 0; Id "lambda" ], ("q", None))) ] );
    GateDecl
      ( ("x", [], [ "a" ]),
        [ GUop (Gate ("u3", [ Pi; Nninteger 0; Pi ], [ ("a", None) ])) ] );
    GateDecl
      ( ("y", [], [ "a" ]),
        [
          GUop
            (Gate
               ( "u3",
                 [
                   Pi;
                   BinaryOp (Div, Pi, Nninteger 2);
                   BinaryOp (Div, Pi, Nninteger 2);
                 ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      (("z", [], [ "a" ]), [ GUop (Gate ("u1", [ Pi ], [ ("a", None) ])) ]);
    GateDecl
      ( ("h", [], [ "a" ]),
        [ GUop (Gate ("u2", [ Nninteger 0; Pi ], [ ("a", None) ])) ] );
    GateDecl
      ( ("s", [], [ "a" ]),
        [
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 2) ], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("sdg", [], [ "a" ]),
        [
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2) ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("t", [], [ "a" ]),
        [
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 4) ], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("tdg", [], [ "a" ]),
        [
          GUop
            (Gate
               ( "u1",
                 [ BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 4) ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("rx", [ "theta" ], [ "a" ]),
        [
          GUop
            (Gate
               ( "u3",
                 [
                   Id "theta";
                   BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2);
                   BinaryOp (Div, Pi, Nninteger 2);
                 ],
                 [ ("a", None) ] ));
        ] );
    GateDecl
      ( ("ry", [ "theta" ], [ "a" ]),
        [
          GUop
            (Gate
               ("u3", [ Id "theta"; Nninteger 0; Nninteger 0 ], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("rz", [ "phi" ], [ "a" ]),
        [ GUop (Gate ("u1", [ Id "phi" ], [ ("a", None) ])) ] );
    GateDecl
      ( ("sx", [], [ "a" ]),
        [
          GUop (Gate ("sdg", [], [ ("a", None) ]));
          GUop (Gate ("h", [], [ ("a", None) ]));
          GUop (Gate ("sdg", [], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("cz", [], [ "a"; "b" ]),
        [
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
        ] );
    GateDecl
      ( ("cy", [], [ "a"; "b" ]),
        [
          GUop (Gate ("sdg", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("s", [], [ ("b", None) ]));
        ] );
    GateDecl
      ( ("swap", [], [ "a"; "b" ]),
        [
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("a", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("ch", [], [ "a"; "b" ]),
        [
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("sdg", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("t", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("t", [], [ ("b", None) ]));
          GUop (Gate ("h", [], [ ("b", None) ]));
          GUop (Gate ("s", [], [ ("b", None) ]));
          GUop (Gate ("x", [], [ ("b", None) ]));
          GUop (Gate ("s", [], [ ("a", None) ]));
        ] );
    GateDecl
      ( ("ccx", [], [ "a"; "b"; "c" ]),
        [
          GUop (Gate ("h", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop (Gate ("tdg", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("t", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("b", None); ("c", None) ]));
          GUop (Gate ("tdg", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("c", None) ]));
          GUop (Gate ("t", [], [ ("b", None) ]));
          GUop (Gate ("t", [], [ ("c", None) ]));
          GUop (Gate ("h", [], [ ("c", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop (Gate ("t", [], [ ("a", None) ]));
          GUop (Gate ("tdg", [], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("cswap", [], [ "a"; "b"; "c" ]),
        [
          GUop (Gate ("cx", [], [ ("c", None); ("b", None) ]));
          GUop (Gate ("ccx", [], [ ("a", None); ("b", None); ("c", None) ]));
          GUop (Gate ("cx", [], [ ("c", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("crx", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate ("u1", [ BinaryOp (Div, Pi, Nninteger 2) ], [ ("b", None) ]));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2);
                   Nninteger 0;
                   Nninteger 0;
                 ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, Id "lambda", Nninteger 2);
                   BinaryOp (Div, UnaryOp (UMinus, Pi), Nninteger 2);
                   Nninteger 0;
                 ],
                 [ ("b", None) ] ));
        ] );
    GateDecl
      ( ("cry", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "ry",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "ry",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("crz", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "rz",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "rz",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
        ] );
    GateDecl
      ( ("cp", [ "lambda" ], [ "a"; "b" ]),
        [
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("a", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, UnaryOp (UMinus, Id "lambda"), Nninteger 2) ],
                 [ ("b", None) ] ));
          GUop (Gate ("cx", [], [ ("a", None); ("b", None) ]));
          GUop
            (Gate
               ( "p",
                 [ BinaryOp (Div, Id "lambda", Nninteger 2) ],
                 [ ("b", None) ] ));
        ] );
    GateDecl
      ( ("cu", [ "theta"; "phi"; "lambda"; "gamma" ], [ "c"; "t" ]),
        [
          GUop (Gate ("p", [ Id "gamma" ], [ ("c", None) ]));
          GUop
            (Gate
               ( "p",
                 [
                   BinaryOp
                     (Div, BinaryOp (Plus, Id "lambda", Id "phi"), Nninteger 2);
                 ],
                 [ ("c", None) ] ));
          GUop
            (Gate
               ( "p",
                 [
                   BinaryOp
                     (Div, BinaryOp (Minus, Id "lambda", Id "phi"), Nninteger 2);
                 ],
                 [ ("t", None) ] ));
          GUop (Gate ("cx", [], [ ("c", None); ("t", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, UnaryOp (UMinus, Id "theta"), Nninteger 2);
                   Nninteger 0;
                   BinaryOp
                     ( Div,
                       UnaryOp (UMinus, BinaryOp (Plus, Id "phi", Id "lambda")),
                       Nninteger 2 );
                 ],
                 [ ("t", None) ] ));
          GUop (Gate ("cx", [], [ ("c", None); ("t", None) ]));
          GUop
            (Gate
               ( "u3",
                 [
                   BinaryOp (Div, Id "theta", Nninteger 2);
                   Id "phi";
                   Nninteger 0;
                 ],
                 [ ("t", None) ] ));
        ] );
  ]

let rec inline_qelib ast =
  match ast with
  | [] -> []
  | Ast.Include "qelib1.inc" :: t -> qelib_decl @ inline_qelib t
  | Ast.Include "stdgates.inc" :: t -> stdgates_decl @ inline_qelib t
  | h :: t -> h :: inline_qelib t
