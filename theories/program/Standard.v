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

Definition Gate_I (a: nat): Instruction :=
  NopInstr.

(* QE Standard Gates *)
Definition Gate_P (lambda: R) (qbit: nat): Instruction :=
  RotateInstr 0 0 lambda qbit.

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

Definition Gate_X_matrix (qbit: nat): Matrix nq :=
  mat_single nq qbit (mat_rot PI 0 PI).

Lemma Gate_X_rot_matrix:
  mat_rot PI 0 PI = -(RTIm 1) .* rec_mat (bas_mat 0) (bas_mat 1) (bas_mat 1) (bas_mat 0).
Proof.
  unfold mat_rot. simpl.
  replace (- 0 / 2)%R with 0%R by field.
  replace (0 / 2)%R with 0%R by field.
  rewrite com_iexp_0, cos_PI2, sin_PI2.
  com_simpl.
  f_equal; f_equal; try com_simpl.
  - unfold com_iexp. rewrite cos_PI2, sin_PI2. com_simpl.
  - unfold com_iexp.
    replace (- PI / 2)%R with (- (PI / 2))%R by field.
    rewrite cos_neg, sin_neg, cos_PI2, sin_PI2. com_simpl.
Qed.

Lemma Gate_X_rot_matrix_square:
  (mat_rot PI 0 PI) * (mat_rot PI 0 PI) = (-1)%R .* mat_eye.
Proof.
  rewrite Gate_X_rot_matrix.
  simpl. com_simpl.
  f_equal; f_equal; com_simpl.
Qed.

Definition Gate_Y_matrix (qbit: nat): Matrix nq :=
  mat_single nq qbit (mat_rot PI PI2 PI2).

Lemma Gate_Y_rot_matrix:
  mat_rot PI PI2 PI2 = rec_mat (bas_mat 0) (bas_mat (-1)%R) (bas_mat 1) (bas_mat 0).
Proof.
  unfold mat_rot. simpl.
  rewrite cos_PI2, sin_PI2.
  com_simpl.
  f_equal; f_equal; try com_simpl.
  - replace (- PI2 / 2)%R with (- (PI2 / 2))%R by field.
    rewrite com_mul_comm, com_neg_mul_comm, com_iexp_inv_r.
    lca.
  - replace (- PI2 / 2)%R with (- (PI2 / 2))%R by field.
    replace (PI2 / 2 + - (PI2 / 2))%R with 0%R by field.
    apply com_iexp_0.
Qed.

Lemma Gate_Y_rot_matrix_square:
  (mat_rot PI PI2 PI2) * (mat_rot PI PI2 PI2) = (-1)%R .* mat_eye.
Proof.
  rewrite Gate_Y_rot_matrix.
  simpl. com_simpl.
Qed.

Definition Gate_Z_matrix (qbit: nat): Matrix nq :=
  mat_single nq qbit (mat_rot 0 0 PI).

Lemma Gate_Z_rot_matrix:
  mat_rot 0 0 PI = rec_mat (bas_mat (-Ione)) (bas_mat 0) (bas_mat 0) (bas_mat Ione).
Proof.
  unfold mat_rot. simpl.
  replace (- 0 / 2)%R with 0%R by field.
  replace (0 / 2)%R with 0%R by field.
  rewrite com_iexp_0, cos_0, sin_0.
  com_simpl.
  f_equal; f_equal; try com_simpl.
  - replace (- PI / 2)%R with (- (PI / 2))%R by field.
    unfold com_iexp.
    rewrite cos_neg, sin_neg, cos_PI2, sin_PI2.
    lca.
  - unfold com_iexp.
    rewrite cos_PI2, sin_PI2.
    lca.
Qed.

Lemma Gate_Z_rot_matrix_square:
  (mat_rot 0 0 PI) * (mat_rot 0 0 PI) = (-1)%R .* mat_eye.
Proof.
  rewrite Gate_Z_rot_matrix.
  simpl. com_simpl.
  f_equal; f_equal. lca.
Qed.

Lemma Pauli_Gate_matrix_neg_eye_extend:
  forall (qbit: nat), nq > qbit ->
  forall (A: Matrix 1), A * A = (-1)%R .* mat_eye ->
  (mat_single nq qbit A) * (mat_single nq qbit A) = (-1)%R .* mat_eye.
Proof.
  intros qbit H.
  intros A HA.
  rewrite mat_single_factorized.
  rewrite HA.
  rewrite (mat_single_scale nq qbit mat_eye _ H).
  rewrite mat_single_eye.
  reflexivity.
Qed.

Lemma Pauli_Gate_matrix_den_uop:
  forall (qbit: nat), nq > qbit ->
  forall (A: Matrix 1), A * A = (-1)%R .* mat_eye ->
  forall (U: Matrix nq),
  den_uop (mat_single nq qbit A) (den_uop (mat_single nq qbit A) U) = U.
Proof.
  intros qbit H A HA U.
  assert (HS: (mat_single nq qbit A) * (mat_single nq qbit A) = (-1)%R .* mat_eye).
  apply (Pauli_Gate_matrix_neg_eye_extend qbit H A HA).
  unfold den_uop.
  remember (mat_single nq qbit A) as B.
  rewrite (mat_mul_assoc B _ _), (mat_mul_assoc B _ _), <- (mat_mul_assoc _ (B†) (B†)).
  rewrite <- mat_mul_conjtrans.
  rewrite HS.
  rewrite mat_scale_conjtrans, mat_scale_mul_assoc, mat_mul_eye_l.
  rewrite mat_scale_mul_comm, <- mat_scale_cmul_assoc, mat_eye_conjtrans.
  rewrite <- mat_scale_mul_comm, mat_mul_eye_r.
  com_simpl.
  assert (Hcom: ((-1)%R * (-1)%R = Cone)%com). lca.
  rewrite Hcom, mat_scale_1. reflexivity.
Qed.

End Gate_properties.
