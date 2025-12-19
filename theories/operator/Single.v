Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
From Stdlib Require Export Program.Equality.

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

Fixpoint mat_single (n t: nat) (U : Matrix 1) : Matrix n :=
  match n, t with
  | 0, _ => mat_eye
  | S n', 0 => U ⊗ mat_eye
  | S n', S t' => @mat_eye 1 ⊗ mat_single n' t' U
  end.

Lemma mat_single_unitary : forall n t (U : Matrix 1), mat_unitary U -> mat_unitary (@mat_single n t U).
Proof.
  unfold mat_single.
  induction n.
  - intros.
    apply mat_eye_unitary.
  - intros.
    destruct t.
    + apply (@tprod_unitary 1 n).
      assumption.
      apply mat_eye_unitary.
    + apply (@tprod_unitary 1 n).
      apply mat_eye_unitary.
      apply IHn.
      assumption.
Qed.

Lemma mat_single_Hermitian : forall n t (U : Matrix 1), mat_Hermitian U -> mat_Hermitian (@mat_single n t U).
Proof.
  unfold mat_single.
  induction n.
  - intros.
    apply mat_eye_Hermitian.
  - intros.
    destruct t.
    + apply (@tprod_Hermitian 1 n).
      assumption.
      apply mat_eye_Hermitian.
    + apply (@tprod_Hermitian 1 n).
      apply mat_eye_Hermitian.
      apply IHn.
      assumption.
Qed.

End GENERAL.
