Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.Single.
Require Import QASMInfer.operator.Projection.

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

Fixpoint mat_ctrl_single (n c t: nat) (U: Matrix 1) : Matrix n :=
  match n, c, t with
  | 0, _, _ | S _, 0, 0 => mat_eye
  | S n', 0, S t' => mat_proj0_base ⊗ mat_eye + mat_proj1_base ⊗ mat_single n' t' U
  | S n', S c', 0 => mat_eye ⊗ mat_proj0 n' c' + U ⊗ mat_proj1 n' c'
  | S n', S c', S t' => (@mat_eye 1) ⊗ mat_ctrl_single n' c' t' U
  end.

Definition mat_not2: Matrix 1 := rec_mat (bas_mat 0) (bas_mat 1) (bas_mat 1) (bas_mat 0).

Definition mat_cnot {n} (qc qt: nat) : Matrix n := mat_ctrl_single n qc qt mat_not2.

End CNOT.

Section CNOT_PROPERTIES.

Lemma mat_ctrl_single_unitary : forall n c t (U: Matrix 1), mat_unitary U -> mat_unitary (mat_ctrl_single n c t U).
Proof.
  intros n c t U HU.
  revert c t.
  induction n.
  - intros; mat_simpl.
    unfold mat_unitary; split.
    all: repeat (f_equal; simpl; try lca).
  - intros; destruct c, t.
    + unfold mat_unitary; split.
      all: mat_simpl.
      all: repeat (f_equal; simpl).
      all: try apply mat_eye_Hermitian.
      all: try apply mat_0_Hermitian.
    + mat_simpl.
      unfold mat_unitary; split.
      all: mat_simpl.
      all: repeat (f_equal; simpl).
      all: try apply mat_eye_Hermitian.
      all: try rewrite mat_0_Hermitian; auto.
      all: mat_simpl.
      all: apply mat_single_unitary; assumption.
    + destruct HU as [HU0 HU1].
      destruct (mat_proj0_projection n c) as [HP0 HH0].
      destruct (mat_proj1_projection n c) as [HP1 HH1].
      unfold mat_ctrl_single.
      unfold mat_unitary; split.
      all: rewrite mat_add_conjtrans.
      all: repeat (try rewrite mat_mul_dist_l; try rewrite mat_mul_dist_r).
      all: repeat rewrite (@tprod_conjtrans 1 _).
      all: rewrite mat_eye_Hermitian.
      all: repeat rewrite (tprod_mul 1 _).
      all: try rewrite mat_mul_eye_r; try rewrite mat_mul_eye_l.
      all: try rewrite HU0; try rewrite HU1.
      all: try rewrite HH0; try rewrite HH1.
      all: try rewrite HP0; try rewrite HP1.
      all: try rewrite mat_proj_01_perp; try rewrite mat_proj_10_perp.
      all: rewrite mat_mul_eye_r.
      all: repeat rewrite tprod_0_r.
      all: rewrite mat_add_0_r; rewrite mat_add_0_l.
      all: rewrite <- (tprod_add_dist_l 1 _).
      all: rewrite mat_proj_sum.
      all: apply (tprod_eye_eye 1).
  + mat_simpl.
    apply unitary_diagonal.
    all: auto.
Qed.


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
