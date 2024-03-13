Require Import Bool.
Require Import Arith.

Definition total_map (V: Type) := nat -> V.

Definition tm_empty {V: Type} (v: V): total_map V := fun (_: nat) => v.

Definition tm_update {V: Type} (m: total_map V) (k: nat) (v: V): total_map V :=
  fun (x: nat) => if (x =? k) then v else m x.

Definition tmb_equal (m1 m2: total_map bool) (size: nat): bool.
Proof.
  induction size as [|size'].
  - exact (eqb (m1 0) (m2 0)).
  - exact (andb (eqb (m1 size') (m2 size')) IHsize').
Defined.
