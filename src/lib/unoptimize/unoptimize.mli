(** [Domain_error (error_class, detail)] reports a failure that is the user's to
    fix rather than a bug.  [error_class] is part of the CLI contract: it is
    printed as the middle field of "qasminfer: <class>: <detail>". *)
exception Domain_error of string * string

val unoptimize_nop : 'a -> 'a
val specs_of_rule_file : int -> string -> (Extracted.transformSpec list, string) result

type applicable_rule = {
  name : string;
  param : string;
  occurrences : int;
}

type manual_parameters = {
  qbits : int list option;
  cbits : int list option;
  occurrence : int option;
  (** Payload inserted by a rule with a [cbit_instr] parameter.  [None] keeps
      the historical behaviour of drawing one at random. *)
  instr : Extracted.instruction option;
}

val applicable_rules :
  ?specs:Extracted.transformSpec list ->
  Extracted.instruction ->
  int ->
  int ->
  applicable_rule list

val unoptimize :
  ?specs:Extracted.transformSpec list ->
  ?rule_name:string ->
  ?manual:manual_parameters ->
  Extracted.instruction ->
  int ->
  int ->
  int ->
  Extracted.instruction
