(* TODO: Add widely-used gates e.g., gates in stdlib.inc *)
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.program.Program.
From Stdlib Require Export Program.Equality.

Bind Scope Complex_scope with Complex.
Open Scope Matrix_scope.

Section Gates.
(* Defining Standard Gates *)
(* https://github.com/Qiskit/qiskit/blob/main/qiskit/qasm/libs/qelib1.inc *)

(* QE Standard Gates *)
Definition Gate_P (lambda: R) (qbit: nat): Instruction :=
  RotateInstr 0 0 lambda qbit.

Definition Gate_I (qbit: nat): Instruction :=
  Gate_P 0 qbit.

(* Pauli Gates *)
Definition Gate_X (qbit: nat): Instruction :=
  RotateInstr PI 0 PI qbit.

Definition Gate_Y (qbit: nat): Instruction :=
  RotateInstr PI PI2 PI2 qbit.

Definition Gate_Z (qbit: nat): Instruction :=
  Gate_P PI qbit.

(* Clifford Gates *)
Definition Gate_H (qbit: nat): Instruction :=
  RotateInstr PI2 0 PI qbit.

Definition Gate_S (qbit: nat): Instruction :=
  Gate_P PI2 qbit.

Definition Gate_SDG (qbit: nat): Instruction :=
  Gate_P (-PI2) qbit.

End Gates.

Section Gate_properties.

Variable nq: nat.

Definition gphase (theta: R): Complex :=
  com_iexp theta.

Lemma Gate_matrix_den_uop_gphase:
  forall (qbit: nat), nq > qbit ->
  forall (A: Matrix 1) (theta: R) (U: Matrix nq),
  den_uop (mat_single nq qbit (gphase theta .* A)) U = den_uop (mat_single nq qbit A) U.
Proof.
  intros qbit H A theta U.
  unfold den_uop.
  rewrite (mat_single_scale _ _ _ _ H).
  rewrite mat_scale_conjtrans.
  rewrite <- mat_scale_mul_comm.
  repeat rewrite mat_scale_mul_assoc.
  rewrite <- mat_scale_scale_comm.
  rewrite com_iexp_conj_anticomm.
  rewrite com_iexp_inv_l.
  rewrite mat_scale_1.
  reflexivity.
Qed.

Definition Gate_X_matrix: Matrix 1 :=
  rec_mat (bas_mat 0) (bas_mat 1)
          (bas_mat 1) (bas_mat 0).

Lemma Gate_X_matrix_unitary: mat_unitary Gate_X_matrix.
Proof.
  unfold mat_unitary, Gate_X_matrix. simpl.
  split; f_equal; f_equal; lca.
Qed.

Lemma Gate_X_matrix_Hermitian: mat_Hermitian Gate_X_matrix.
Proof.
  unfold mat_Hermitian, Gate_X_matrix. simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_X_matrix_gphase:
  mat_rot PI 0 PI = gphase (- PI2) .* Gate_X_matrix.
Proof.
  unfold mat_rot. simpl.
  replace (- 0 / 2)%R with 0%R by field.
  replace (0 / 2)%R with 0%R by field.
  rewrite com_iexp_0, cos_PI2, sin_PI2.
  com_simpl.
  f_equal; f_equal; try com_simpl.
  - unfold gphase. replace PI2 with (PI / 2)%R by (unfold PI; field; lra).
    unfold com_iexp. rewrite cos_neg, sin_neg, cos_PI2, sin_PI2. lca.
  - unfold gphase. replace PI2 with (PI / 2)%R by (unfold PI; field; lra).
    f_equal. lra.
Qed.

Definition Gate_Y_matrix: Matrix 1 :=
  rec_mat (bas_mat 0) (bas_mat (-Ione))
          (bas_mat Ione) (bas_mat 0).

Lemma Gate_Y_matrix_unitary: mat_unitary Gate_Y_matrix.
Proof.
  unfold mat_unitary, Gate_Y_matrix. simpl.
  split; f_equal; f_equal; lca.
Qed.

Lemma Gate_Y_matrix_Hermitian: mat_Hermitian Gate_Y_matrix.
Proof.
  unfold mat_Hermitian, Gate_Y_matrix. simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_Y_matrix_gphase:
  mat_rot PI PI2 PI2 = gphase (- PI2) .* Gate_Y_matrix.
Proof.
  unfold mat_rot. simpl.
  rewrite cos_PI2, sin_PI2. com_simpl.
  f_equal; f_equal.
  - rewrite com_mul_comm, com_neg_mul_comm.
    replace (- PI2 / 2)%R with (- (PI2 / 2))%R by field.
    rewrite com_iexp_inv_r. unfold gphase, com_iexp.
    replace PI2 with (PI / 2)%R by (unfold PI; field; lra).
    rewrite cos_neg, sin_neg, cos_PI2, sin_PI2. lca.
  - replace (PI2 / 2 + - PI2 / 2)%R with 0%R by field.
    rewrite com_iexp_0. unfold gphase, com_iexp.
    replace PI2 with (PI / 2)%R by (unfold PI; field; lra).
    rewrite cos_neg, sin_neg, cos_PI2, sin_PI2. lca.
Qed.

Definition Gate_Z_matrix: Matrix 1 :=
  rec_mat (bas_mat 1) (bas_mat 0)
          (bas_mat 0) (bas_mat (-1)%R).

Lemma Gate_Z_matrix_unitary: mat_unitary Gate_Z_matrix.
Proof.
  unfold mat_unitary, Gate_Z_matrix. simpl.
  split; f_equal; f_equal; lca.
Qed.

Lemma Gate_Z_matrix_Hermitian: mat_Hermitian Gate_Z_matrix.
Proof.
  unfold mat_Hermitian, Gate_Z_matrix. simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_Z_matrix_gphase:
  mat_rot 0 0 PI = gphase (- PI2) .* Gate_Z_matrix.
Proof.
  unfold mat_rot, Gate_Z_matrix. simpl.
  replace (- 0 / 2)%R with 0%R by field.
  replace (0 / 2)%R with 0%R by field.
  rewrite cos_0, sin_0.
  com_simpl.
  f_equal; f_equal; try lca.
  - replace (- PI / 2)%R with (- (PI / 2))%R by field.
    replace PI2 with (PI / 2)%R by (unfold PI; field; lra).
    reflexivity.
  - replace PI2 with (PI / 2)%R by (unfold PI; field; lra).
    unfold gphase, com_iexp.
    rewrite cos_neg, sin_neg, cos_PI2, sin_PI2. lca.
Qed.

Lemma Gate_P_matrix_mul:
  forall (l1 l2: R),
  (mat_rot 0 0 l1) * (mat_rot 0 0 l2) = mat_rot 0 0 (l1 + l2)%R.
Proof.
  intros l1 l2.
  unfold mat_rot.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  repeat rewrite mat_mul_eye_l.
  unfold mat_rot_z.
  simpl.
  f_equal; f_equal; com_simpl; f_equal; lra.
Qed.

Lemma Gate_P_matrix_0_eye:
  mat_rot 0 0 0 = mat_eye.
Proof.
  unfold mat_rot.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  repeat rewrite mat_mul_eye_l.
  reflexivity.
Qed.

Lemma Gate_P_matrix_periodic:
  forall (l: R),
  mat_rot 0 0 l = gphase PI .* mat_rot 0 0 (l + 2 * PI).
Proof.
  intros l.
  unfold mat_rot.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  repeat rewrite mat_mul_eye_l.
  unfold mat_rot_z.
  simpl. com_simpl.
  f_equal; f_equal.
  - f_equal. lra.
  - replace (PI + (l + 2 * PI) / 2)%R with (l / 2 + 2 * PI)%R by field.
    unfold com_iexp.
    replace (l/2 + 2*PI)%R with (l/2 + 2 * INR 1 * PI)%R by (simpl; ring).
    rewrite cos_period, sin_period.
    reflexivity.
Qed.

Lemma Gate_P_matrix_periodic_neg:
  forall (l: R),
  mat_rot 0 0 l = gphase PI .* mat_rot 0 0 (l - 2 * PI).
Proof.
  intros l.
  rewrite Gate_P_matrix_periodic with (l := (l - 2 * PI)%R).
  replace (l - 2 * PI + 2 * PI)%R with l by field.
  rewrite <- mat_scale_scale_comm.
  unfold gphase, com_iexp.
  rewrite cos_PI, sin_PI.
  assert (H: (((-1)%R + RTIm 0)%com * ((-1)%R + RTIm 0)%com)%com = 1%com). lca.
  rewrite H.
  rewrite mat_scale_1.
  reflexivity.
Qed.

End Gate_properties.
