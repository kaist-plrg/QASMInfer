Require Import Density.
Require Import Extraction.
Require ExtrOcamlNatInt.
Require ExtrOcamlZInt.

Extract Constant Nat.add => "(+)".
Extract Constant Nat.sub => "(fun n m -> Stdlib.max 0 (n-m))".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.div => "(/)".
Extract Constant Nat.modulo => "(mod)".
Extraction Inline Nat.add.
Extraction Inline Nat.sub.
Extraction Inline Nat.mul.
Extraction Inline Nat.div.
Extraction Inline Nat.modulo.

Extract Constant Pos.succ => "Stdlib.succ".

Extract Constant Reals.ClassicalDedekindReals.DReal => "float".
Extract Inductive Reals.Cauchy.ConstructiveCauchyReals.CReal => "float"
  [ "(fun seq scale => seq scale)" ]
  "(fun f creal -> f (creal.seq) (creal.scale))".

Extract Constant RbaseSymbolsImpl.Rabst => "fun x -> x".
Extract Constant RbaseSymbolsImpl.Rrepr => "fun x -> x".

Extract Constant IZR => "float_of_int".

(* Extract Constant RbaseSymbolsImpl.Rabst => "failwith ""Should not use Rabst""".
Extraction Inline RbaseSymbolsImpl.Rabst.
Extract Constant RbaseSymbolsImpl.Rrepr => "failwith ""Should not use Rrepr""".
Extraction Inline RbaseSymbolsImpl.Rrepr. *)

Extract Constant RbaseSymbolsImpl.R => "float".
Extract Constant RbaseSymbolsImpl.R0 => "0.0".
Extract Constant RbaseSymbolsImpl.R1 => "1.0".
Extract Constant RbaseSymbolsImpl.Rplus => "Stdlib.(+.)".
Extract Constant RbaseSymbolsImpl.Rmult => "Stdlib.( *. )".
Extract Constant RbaseSymbolsImpl.Ropp => "Stdlib.(~-.)".
Extract Constant RinvImpl.Rinv => "fun x -> 1.0 /. x".


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

Extraction "../qasm/lib/quantum_core.ml" Qop_rot Qop_cnot Den_0_init Den_measure Den_unitary Den_proj_uop.