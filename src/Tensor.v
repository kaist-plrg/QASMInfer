Require Export Matrix.
Import ListNotations.

Declare Scope T_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.


(* tensor product =============================================================================== *)

Definition Tproduct (m1 m2: Matrix):
  {m: Matrix | rows m = (rows m1 * rows m2)%nat /\ cols m = (cols m1 * cols m2)%nat}.
Proof.
  refine( exist _
    {|rows := rows m1 * rows m2;
      cols := cols m1 * cols m2;
      inner := fun i j => Cmult (
        inner m1 (i / rows m2) (j / cols m2)
      ) (
        inner m2 (i mod rows m2) (j mod cols m2)
      )
    |} _ ).
  Unshelve.
  - split. reflexivity. reflexivity.
  - assert (rows m1 > 0) by apply rows_pos.
    assert (rows m2 > 0) by apply rows_pos.
    lia.
  - assert (cols m1 > 0) by apply cols_pos.
    assert (cols m2 > 0) by apply cols_pos.
    lia.
Defined.

Property Tproduct_correct: forall
  (m1 m2 mt: Matrix) (i j: nat) (Ht: _) (Hi: _) (Hj: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ mt Ht = Tproduct m1 m2 ->
  mt[[i Hi|j Hj]] = m1[[(i / rows m2) H1i|(j / cols m2) H1j]] * m2[[(i mod rows m2) H2i|(j mod cols m2) H2j]].
Proof.
  unfold Mget.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)

(* Definition trace, partial trace *)
(* Definition tensor_product *)