val unoptimize_nop : 'a -> 'a
val specs_of_rule_file : string -> (Extracted.transformSpec list, string) result
val unoptimize :
  ?specs:Extracted.transformSpec list ->
  ?rule_name:string ->
  Extracted.instruction ->
  int ->
  int ->
  int ->
  Extracted.instruction
