Require Export Projection.
Require Export Coq.Program.Equality.

Bind Scope Complex_scope with Complex.
Open Scope Matrix_scope.

Section SINGLE.

Open Scope R_scope.

(* rotation around y axis *)
Definition mat_rot_y (θ : R) : Matrix 1 :=
  rec_mat (bas_mat (cos (θ/2))) (bas_mat (- sin (θ/2)))
          (bas_mat (sin (θ/2))) (bas_mat (cos (θ/2))).

(* rotation around z axis *)
Definition mat_rot_z (θ : R) : Matrix 1 :=
  rec_mat (bas_mat (com_iexp (- θ/2))) (bas_mat 0)
          (bas_mat 0)                 (bas_mat (com_iexp (θ/2))).

Close Scope R_scope.

(* Previous built-in single qubit gate *)
Definition mat_rot (θ φ l : R) : Matrix 1 := (mat_rot_z φ * mat_rot_y θ * mat_rot_z l).

End SINGLE.

Section PROPERTIES.

Lemma mat_rot_y_unitary : forall θ, mat_unitary (mat_rot_y θ).
Proof.
  intros.
  unfold mat_rot_y, mat_unitary, mat_eye; split.
  all: simpl; repeat f_equal; com_simpl.
Qed.

Lemma mat_rot_z_unitary : forall θ, mat_unitary (mat_rot_z θ).
Proof.
  intros.
  unfold mat_rot_z, mat_unitary, mat_eye; split.
  all: simpl; repeat f_equal; com_simpl.
  all: apply com_iexp_0_impl; ring.
Qed.

Lemma mat_rot_unitary : forall θ φ l, mat_unitary (mat_rot θ φ l).
Proof.
  intros.
  unfold mat_rot.
  repeat apply mat_mul_unitary.
  apply mat_rot_z_unitary.
  apply mat_rot_y_unitary.
  apply mat_rot_z_unitary.
Qed.

End PROPERTIES.

Section GENERAL.

Definition mat_single (n t: nat) (U : Matrix 1) : Matrix n.
Proof.
  destruct (lt_dec t n).
    replace n with (t + 1 + (n - t - 1))%nat by lia.
    apply ((@mat_eye t) ⊗ U ⊗ (@mat_eye (n - t - 1))).
  - apply mat_eye.
Defined.

Lemma mat_single_unitary : forall n t (U : Matrix 1), mat_unitary U -> mat_unitary (@mat_single n t U).
Proof.
  intros.
  unfold mat_single.
  destruct (lt_dec t n).
  - simpl_eq.
    repeat apply tprod_unitary.
    apply mat_eye_unitary.
    auto.
    apply mat_eye_unitary.
  - apply mat_eye_unitary.
Qed.

Lemma mat_single_Hermitian : forall n t (U : Matrix 1), mat_Hermitian U -> mat_Hermitian (@mat_single n t U).
Proof.
  intros.
  unfold mat_single.
  destruct (lt_dec t n).
  - simpl_eq.
    repeat apply tprod_Hermitian.
    apply mat_eye_Hermitian.
    auto.
    apply mat_eye_Hermitian.
  - apply mat_eye_Hermitian.
Qed.

Lemma mat_single_projection : forall n t (U : Matrix 1), mat_projection U -> mat_projection (mat_single n t U).
Proof.
  intros.
  split; [|split].
  - unfold mat_single.
    destruct (lt_dec t n).
    + simpl_eq.
      destruct H as [H _].
      repeat rewrite tprod_mul.
      rewrite H.
      mat_simpl.
    + mat_simpl.
  - destruct H as [_ [H _]].
    apply mat_single_Hermitian.
    apply H.
  - destruct H as [_ [_ H]].
    unfold mat_single.
    destruct (lt_dec t n).
    + simpl_eq.
      repeat rewrite tprod_trace.
      repeat apply com_ge0_mul.
      2: apply H.
      all: apply mat_trace_positive, mat_eye_positive.
    + apply mat_trace_positive, mat_eye_positive.
Qed.

End GENERAL.