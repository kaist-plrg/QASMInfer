Require Export Positive.

Open Scope Matrix_scope.

Definition mat_projection {n} (A: Matrix n) : Prop := A * A = A /\ mat_Hermitian A /\ mat_trace A >= 0.

Section BASE.

Definition mat_proj0 : Matrix 1 := rec_mat (bas_mat 1) (bas_mat 0)
                                           (bas_mat 0) (bas_mat 0).

Definition mat_proj1 : Matrix 1 := rec_mat (bas_mat 0) (bas_mat 0)
                                           (bas_mat 0) (bas_mat 1).

Definition mat_proj0_pt (U: Matrix 1) : Matrix 2 := mat_proj0 ⊗ U.

Definition mat_proj1_pt (U: Matrix 1) : Matrix 2 := mat_proj1 ⊗ U.

Definition mat_ctrl_0_ct (U: Matrix 1) : Matrix 2 := mat_proj0_pt U + mat_proj1_pt mat_eye.

Definition mat_ctrl_1_ct (U: Matrix 1) : Matrix 2 := mat_proj0_pt mat_eye + mat_proj1_pt U.

End BASE.

Section PROPERTIES.

Lemma mat_proj_sum : mat_proj0 + mat_proj1 = mat_eye.
Proof.
  unfold mat_proj0, mat_proj1.
  com_simpl.
Qed.

Lemma mat_proj0_mul : mat_proj0 * mat_proj0 = mat_proj0.
Proof.
  unfold mat_proj0.
  com_simpl.
Qed.

Lemma mat_proj1_mul : mat_proj1 * mat_proj1 = mat_proj1.
Proof.
  unfold mat_proj1.
  com_simpl.
Qed.

Lemma mat_proj0_Hermitian : mat_Hermitian mat_proj0.
Proof.
  unfold mat_proj0, mat_Hermitian.
  com_simpl.
Qed.

Lemma mat_proj1_Hermitian : mat_Hermitian mat_proj1.
Proof.
  unfold mat_proj1, mat_Hermitian.
  com_simpl.
Qed.

Lemma mat_proj0_positive : mat_positive mat_proj0.
Proof.
  apply mat_pure_positive_impl.
  exists (rec_vec (bas_vec 1) (bas_vec 0)).
  com_simpl.
Qed.

Lemma mat_proj1_positive : mat_positive mat_proj1.
Proof.
  apply mat_pure_positive_impl.
  exists (rec_vec (bas_vec 0) (bas_vec 1)).
  com_simpl.
Qed.

Lemma mat_proj0_trace : mat_trace mat_proj0 >= 0.
Proof.
  unfold mat_proj0.
  com_simpl.
  split; simpl.
  all: lra.
Qed.

Lemma mat_proj1_trace : mat_trace mat_proj1 >= 0.
Proof.
  unfold mat_proj1.
  com_simpl.
  split; simpl.
  all: lra.
Qed.

Lemma mat_proj0_projection : mat_projection mat_proj0.
Proof.
  unfold mat_projection.
  split.
  - apply mat_proj0_mul.
  - split.
    + apply mat_proj0_Hermitian.
    + apply mat_proj0_trace.
Qed.

Lemma mat_proj1_projection : mat_projection mat_proj1.
Proof.
  unfold mat_projection.
  split.
  - apply mat_proj1_mul.
  - split.
    + apply mat_proj1_Hermitian.
    + apply mat_proj1_trace.
Qed.

Lemma mat_proj_01_perp : mat_proj0 * mat_proj1 = mat_0.
Proof.
  com_simpl.
Qed.

Lemma mat_proj_10_perp : mat_proj1 * mat_proj0 = mat_0.
Proof.
  com_simpl.
Qed.

Lemma mat_ctrl_1_ct_unitary : forall (U: Matrix 1), mat_unitary U -> mat_unitary (mat_ctrl_1_ct U).
Proof.
  intros U [HU1 HU2].
  unfold mat_ctrl_1_ct, mat_proj0_pt, mat_proj1_pt, mat_unitary.
  repeat (
    mat_conj || mat_expand || mat_sort || mat_simpl ||
    rewrite (tprod_conjtrans 1) ||
    rewrite mat_eye_Hermitian ||
    rewrite HU1 || rewrite HU2 ||
    rewrite (tprod_conjtrans 1) ||
    rewrite (tprod_mul 1) ||
    rewrite (tprod_0_l 1) ||
    rewrite mat_proj0_Hermitian || rewrite mat_proj1_Hermitian ||
    rewrite mat_proj0_mul || rewrite mat_proj1_mul ||
    rewrite mat_proj_01_perp || rewrite mat_proj_10_perp
  ).
  rewrite <- (tprod_add_dist_r 1).
  rewrite mat_proj_sum.
  rewrite tprod_eye_eye.
  split; reflexivity.
Qed.

Lemma mat_ctrl_0_ct_unitary : forall (U: Matrix 1), mat_unitary U -> mat_unitary (mat_ctrl_0_ct U).
Proof.
  intros U [HU1 HU2].
  unfold mat_ctrl_0_ct, mat_proj0_pt, mat_proj1_pt, mat_unitary.
  repeat (
    mat_conj || mat_expand || mat_sort || mat_simpl ||
    rewrite (tprod_conjtrans 1) ||
    rewrite mat_eye_Hermitian ||
    rewrite HU1 || rewrite HU2 ||
    rewrite (tprod_conjtrans 1) ||
    rewrite (tprod_mul 1) ||
    rewrite (tprod_0_l 1) ||
    rewrite mat_proj0_Hermitian || rewrite mat_proj1_Hermitian ||
    rewrite mat_proj0_mul || rewrite mat_proj1_mul ||
    rewrite mat_proj_01_perp || rewrite mat_proj_10_perp
  ).
  rewrite <- (tprod_add_dist_r 1).
  rewrite mat_proj_sum.
  rewrite tprod_eye_eye.
  split; reflexivity.
Qed.

End PROPERTIES.
