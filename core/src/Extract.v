Require Import Program.
Require Import Extraction.
Require ExtrOcamlNatInt.
Require ExtrOcamlZInt.

Extract Inlined Constant Init.Nat.add => "(+)".
Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.sub => "(fun n m -> Stdlib.max 0 (n-m))".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.div => "(/)".
Extract Inlined Constant Nat.modulo => "(mod)".
Extract Inlined Constant pow_2 => "(fun n -> Int.shift_left 1 n)".

Extract Constant Pos.succ => "Stdlib.succ".

Extract Inlined Constant Reals.ClassicalDedekindReals.DReal => "float".
Extract Inductive Reals.Cauchy.ConstructiveCauchyReals.CReal => "float"
  [ "(fun seq scale => seq scale)" ]
  "(fun f creal -> f (creal.seq) (creal.scale))".

Extract Inlined Constant IZR => "float_of_int".

Extract Constant RbaseSymbolsImpl.R => "float".
Extract Constant RbaseSymbolsImpl.R0 => "0.0".
Extract Constant RbaseSymbolsImpl.R1 => "1.0".
Extract Constant RbaseSymbolsImpl.Rplus => "Stdlib.(+.)".
Extract Constant RbaseSymbolsImpl.Rmult => "Stdlib.( *. )".
Extract Constant RbaseSymbolsImpl.Ropp => "Stdlib.(~-.)".
Extract Constant Rminus => "Stdlib.(-.)".
Extract Constant RinvImpl.Rinv => "fun x -> 1.0 /. x".
Extract Constant Rdiv => "Stdlib.(/.)".
Extract Constant RbaseSymbolsImpl.Rabst => "fun x -> x".
Extract Constant RbaseSymbolsImpl.Rrepr => "fun x -> x".
Extract Constant total_order_T =>
"(fun x y ->
  if (x < y) then (Some true)
  else if (y < x) then None else (Some false))".
Extract Constant Rlt_dec => "(fun x y -> x < y)".
Extract Constant Rgt_dec => "(fun x y -> x > y)".

Extract Constant RTC => "fun x -> {re=x; im=0.0}".
Extract Constant RTIm => "fun y -> {re=0.0; im=y}".
Extract Constant NTC => "fun n -> {re=float_of_int n; im=0.0}".

Extract Inlined Constant sin => "Stdlib.sin".
Extract Inlined Constant cos => "Stdlib.cos".
Extract Inlined Constant atan2 => "Stdlib.atan2".
Extract Inlined Constant exp => "Stdlib.exp".

Extract Inlined Constant C => "Complex.t".
Extract Inlined Constant Cmake => "(fun re im -> {re=re; im=im})".
Extract Inlined Constant Cplus => "Complex.add".
Extract Inlined Constant Cminus => "Complex.sub".
Extract Inlined Constant Cmult => "Complex.mul".
Extract Inlined Constant Cconj => "Complex.conj".
Extract Inlined Constant Creal => "(fun x -> x.re)".
Extract Inlined Constant Cexp => "Complex.exp".
Extract Inlined Constant Cinv => "Complex.inv".

Extraction "../qasm/lib/core/quantum_core.ml" Execute_and_calculate_prob.