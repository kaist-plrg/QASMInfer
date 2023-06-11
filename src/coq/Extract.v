Require Import Density.
Require Import Extraction.
Require ExtrOcamlNatInt.
Require ExtrOcamlZInt.

(* Mapping Coq's Z type to OCaml's Z.t
Extract Inductive Z => "Z.t" [ "" ].

Mapping Coq's Q type to OCaml's Q.t
Extract Inductive Q => "Q.t" [ "" ]. *)


(* Extract Inductive Cauchy.ConstructiveCauchyReals.CReal =>
  "float"
  [ "(fun f _ _ _ -> f)" ]
  "(fun f -> f)".

Extract Constant CReal_to_Q =>
  "(fun r n -> r /. (float_of_int (1 lsl n)))".

Extract Constant ClassicalDedekindReals.DReal => "float". *)

Extract Constant Pos.succ => "Stdlib.succ".

Extract Constant RbaseSymbolsImpl.R => "float".
Extract Constant RbaseSymbolsImpl.Rabst => "__".
Extract Constant RbaseSymbolsImpl.Rrepr => "__".
Extract Constant RbaseSymbolsImpl.R0 => "0.0".
Extract Constant RbaseSymbolsImpl.R1 => "1.0".
Extract Constant RbaseSymbolsImpl.Rplus => "Stdlib.(+.)".
Extract Constant RbaseSymbolsImpl.Rmult => "Stdlib.( *. )".
Extract Constant RbaseSymbolsImpl.Ropp => "Stdlib.(~-.)".
Extract Constant RinvImpl.Rinv => "fun x -> 1.0 /. x".

(* Extract Constant ClassicalDedekindReals.DReal => "float". *)

Extract Constant Rle_dec => "fun x y -> x <= y".
Extract Constant total_order_T =>
"(fun x y ->
  if (x < y) then (Some true)
  else if (y < x) then None else (Some false))".

Extract Constant RTC => "fun x -> (x, 0.0)".
Extract Constant NTC => "fun n -> (float_of_int n, 0.0)".

Extract Constant sin => "Stdlib.sin".
Extract Constant cos => "Stdlib.cos".
Extract Constant atan2 => "Stdlib.atan2".
Extract Constant exp => "Stdlib.exp".

Extraction "src/ocaml/core.ml" Qop_rot Qop_cnot Den_0_init Den_measure Den_unitary Den_proj_uop.