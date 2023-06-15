Require Import Density.
Require Import Extraction.
Require ExtrOcamlNatInt.
Require ExtrOcamlZInt.

(* Set Extraction Flag 2031. *)

Extract Inlined Constant C => "float * float".

Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.sub => "(fun n m -> Stdlib.max 0 (n-m))".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.div => "(/)".
Extract Inlined Constant Nat.modulo => "(mod)".

Extract Constant Pos.succ => "Stdlib.succ".

Extract Constant Reals.ClassicalDedekindReals.DReal => "float".
Extract Inductive Reals.Cauchy.ConstructiveCauchyReals.CReal => "float"
  [ "(fun seq scale => seq scale)" ]
  "(fun f creal -> f (creal.seq) (creal.scale))".

Extract Inlined Constant RbaseSymbolsImpl.Rabst => "fun x -> x".
Extract Inlined Constant RbaseSymbolsImpl.Rrepr => "fun x -> x".

Extract Constant IZR => "float_of_int".

Extract Constant RbaseSymbolsSig.R => "".

(* Extract Constant RbaseSymbolsImpl.Rabst => "failwith ""Should not use Rabst""".
Extraction Inline RbaseSymbolsImpl.Rabst.
Extract Constant RbaseSymbolsImpl.Rrepr => "failwith ""Should not use Rrepr""".
Extraction Inline RbaseSymbolsImpl.Rrepr. *)

(* Extract Constant RbaseSymbolsSig => "float". *)
Extract Inlined Constant RbaseSymbolsImpl.R => "float".
Extract Inlined Constant RbaseSymbolsImpl.R0 => "0.0".
Extract Inlined Constant RbaseSymbolsImpl.R1 => "1.0".
Extract Inlined Constant RbaseSymbolsImpl.Rplus => "Stdlib.(+.)".
Extract Inlined Constant RbaseSymbolsImpl.Rmult => "Stdlib.( *. )".
Extract Inlined Constant RbaseSymbolsImpl.Ropp => "Stdlib.(~-.)".
Extract Inlined Constant Rminus => "Stdlib.(-.)".
Extract Inlined Constant RinvImpl.Rinv => "fun x -> 1.0 /. x".
Extract Inlined Constant Rdiv => "Stdlib.(/.)".

Extract Constant RTC => "fun x -> (x, 0.0)".
Extract Constant NTC => "fun n -> (float_of_int n, 0.0)".

Extract Inlined Constant sin => "Stdlib.sin".
Extract Inlined Constant cos => "Stdlib.cos".
Extract Inlined Constant atan2 => "Stdlib.atan2".
Extract Inlined Constant exp => "Stdlib.exp".

Extraction "../qasm/lib/quantum_core.ml" Qop_rot Qop_cnot Den_0_init Den_measure Den_unitary Den_proj_uop.