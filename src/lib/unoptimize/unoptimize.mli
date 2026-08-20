val unoptimize_nop : 'a -> 'a
val specs_of_rule_file : string -> (Extracted.transformSpec list, string) result

type applicable_rule = {
  name : string;
  param : string;
  occurrences : int;
}

type manual_parameters = {
  qbits : int list option;
  cbits : int list option;
  occurrence : int option;
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
