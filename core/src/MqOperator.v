Require Export Projection.

Bind Scope Complex_scope with Complex.
Open Scope Matrix_scope.

Section SWAP.

Definition mat_swap2: Matrix 2 :=
  rec_mat (rec_mat (bas_mat 1) (bas_mat 0)
                   (bas_mat 0) (bas_mat 0))  (rec_mat (bas_mat 0) (bas_mat 0)
                                                      (bas_mat 1) (bas_mat 0))
          (rec_mat (bas_mat 0) (bas_mat 1)
                   (bas_mat 0) (bas_mat 0))  (rec_mat (bas_mat 0) (bas_mat 0)
                                                      (bas_mat 0) (bas_mat 1)).

Fixpoint mat_swap_1n_suppl (n: nat) : Matrix (2 + n).
Proof.
  destruct n as [|n'].
  - exact mat_swap2.
  - exact ((mat_swap2 ⊗ mat_eye) * ((@mat_eye 1) ⊗ mat_swap_1n_suppl n') * (mat_swap2 ⊗ mat_eye)).
Defined.

Definition mat_swap_1n (n: nat) : Matrix n.
Proof.
  destruct n as [|[|n']].
  1-2: exact mat_eye.
  exact (mat_swap_1n_suppl n').
Defined.

Definition mat_swap {n} (q1 q2: nat) : Matrix n.
Proof.
  destruct (lt_dec q1 n) as [H1|H1], (lt_dec q2 n) as [H2|H2].
  - destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
    + replace n with (q1 + (q2 - q1 + 1) + (n - q2 - 1))%nat by lia.
      exact ((@mat_eye q1) ⊗ mat_swap_1n (q2 - q1 + 1) ⊗ @mat_eye (n - q2 - 1)).
    + exact mat_eye.
    + replace n with (q2 + (q1 - q2 + 1) + (n - q1 - 1))%nat by lia.
      exact ((@mat_eye q2) ⊗ mat_swap_1n (q1 - q2 + 1) ⊗ @mat_eye (n - q1 - 1)).
  - exact mat_eye.
  - exact mat_eye.
  - exact mat_eye.
Defined.

Definition mat_swap_op {n} (q1 q2: nat) (U: Matrix n) : Matrix n :=
  mat_swap q1 q2 * U * mat_swap q1 q2.

End SWAP.


Section SWAP_PROPERTIES.

Lemma mat_swap2_unitary : mat_unitary mat_swap2.
Proof.
  unfold mat_swap2, mat_unitary, mat_eye; simpl; split.
  all: repeat f_equal; com_simpl.
Qed.

Lemma mat_swap_1n_unitary : forall n, mat_unitary (mat_swap_1n n).
Proof.
  induction n as [|[|[|n']]].
  1-3: unfold mat_unitary; simpl; split; repeat f_equal.
  all: try lca.
  unfold mat_unitary in *.
  split.
  all: unfold mat_swap_1n in *.
  all: unfold mat_swap_1n_suppl.
  all: repeat apply mat_mul_unitary.
  all: try apply (@tprod_unitary 2 (S n')).
  all: try apply (@tprod_unitary 1 (2 + n')).
  all: try apply mat_eye_unitary.
  all: try apply mat_swap2_unitary.
  all: auto.
Qed.

Lemma mat_swap_unitary : forall n q1 q2, mat_unitary (@mat_swap n q1 q2).
Proof.
  intros.
  unfold mat_swap; destruct (lt_dec q1 n) as [H1|H1], (lt_dec q2 n) as [H2|H2].
  - destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
    all: simpl_eq.
    all: repeat apply tprod_unitary.
    all: try apply mat_eye_unitary.
    all: apply mat_swap_1n_unitary.
  - apply mat_eye_unitary.
  - apply mat_eye_unitary.
  - apply mat_eye_unitary.
Qed.

Lemma mat_swap_op_unitary : forall n q1 q2 (U: Matrix n), mat_unitary U -> mat_unitary (mat_swap_op q1 q2 U).
Proof.
  intros.
  unfold mat_swap_op.
  repeat apply mat_mul_unitary.
  all: try apply mat_swap_unitary; auto.
Qed.

End SWAP_PROPERTIES.

Section CNOT.

Definition mat_not2: Matrix 1 := rec_mat (bas_mat 0) (bas_mat 1) (bas_mat 1) (bas_mat 0).

Definition mat_cnot {n} (qc qt: nat) : Matrix n := mat_ctrl_single n qc qt mat_not2.

End CNOT.

Section CNOT_PROPERTIES.

Lemma mat_not2_unitary : mat_unitary mat_not2.
Proof.
  unfold mat_not2, mat_unitary; simpl; split; repeat f_equal; com_simpl.
Qed.

Lemma mat_cnot_unitary : forall n qc qt, mat_unitary (@mat_cnot n qc qt).
Proof.
  intros.
  apply mat_ctrl_single_unitary.
  apply mat_not2_unitary.
Qed.

End CNOT_PROPERTIES.