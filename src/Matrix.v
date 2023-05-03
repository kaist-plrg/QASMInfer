Require Export Complex.

Declare Scope matrix_scope.
Open Scope matrix_scope.

Open Scope nat_scope.
Open Scope C_scope.
Bind Scope nat_scope with nat.
Bind Scope C_scope with C.

Record Matrix := {
  rows: nat;
  cols: nat;
  data: list C;
  data_length: length data = (rows * cols)%nat
}.

Definition Mget (m : Matrix) (row col : nat) : option C :=
  if (row <? rows m) && (col <? cols m) then
    nth_error (data m) (row * cols m + col)
  else
    None.

Notation "m '[[' row ',' col ']]'" :=
  (Mget m row col) (at level 9, row at level 9, col at level 9, no associativity).


Lemma matrix_shape_size: forall m1 m2: Matrix,
  rows m1 = rows m2 -> cols m1 = cols m2 -> length (data m1) = length (data m2).
Proof.
  intros m1 m2 Hrows Hcols.
  repeat rewrite data_length.
  rewrite Hrows.
  rewrite Hcols.
  reflexivity.
Qed.

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2):
  {m: Matrix | rows m = rows m1 /\ cols m = cols m1}.
Proof.
  destruct (bop_lists bop (data m1) (data m2) (matrix_shape_size m1 m2 Hrows Hcols)) as [newData newH].
  refine (
    exist _ {| rows := rows m1;
             cols := cols m1;
             data := newData;
             data_length := _  |}
             _
  ).
  Unshelve.
  - split. reflexivity. reflexivity.
  - rewrite newH. apply data_length.
Defined.

Theorem Mbop_correct: forall
  (bop: C -> C -> C)
  (m1 m2: Matrix)
  (Hrows: rows m1 = rows m2)
  (Hcols: cols m1 = cols m2),
  (proj1_sig (Mbop bop m1 m2 Hrows Hcols)



(* Definition Mopp (m: Matrix): option Matrix
Definition Mminus (m1 m2: Matrix): option Matrix.
Definition Mmult (m1 m2: Matrix): option Matrix. *)
