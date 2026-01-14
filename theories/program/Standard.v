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

Definition Gate_Sdg (qbit: nat): Instruction :=
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
  mat_sort.
  com_simpl.
  mat_simpl.
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
  unfold mat_rot, gphase.
  rewrite mat_rot_z_0_eye.
  mat_simpl.
  rewrite cos_PI2, sin_PI2.
  f_equal; f_equal; com_simpl.
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
  unfold mat_rot, gphase.
  mat_simpl.
  rewrite cos_PI2, sin_PI2.
  f_equal; f_equal; com_simpl.
  - rewrite com_mul_comm, com_neg_mul_comm.
    replace (- PI2 / 2)%R with (- (PI2 / 2))%R by field.
    com_simpl.
  - replace (PI2 / 2 + - PI2 / 2)%R with 0%R by field.
    com_simpl.
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
  unfold mat_rot, Gate_Z_matrix, gphase.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  mat_simpl.
  f_equal; f_equal; com_simpl.
Qed.

Definition Gate_H_matrix: Matrix 1 :=
  (/ sqrt 2)%R .*
  rec_mat (bas_mat 1) (bas_mat 1)
          (bas_mat 1) (bas_mat (-1)%R).

Lemma Gate_H_matrix_Hermitian: mat_Hermitian Gate_H_matrix.
Proof.
  unfold mat_Hermitian, Gate_H_matrix. simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_H_matrix_unitary: mat_unitary Gate_H_matrix.
Proof.
  unfold mat_unitary.
  rewrite Gate_H_matrix_Hermitian.
  unfold Gate_H_matrix. simpl.
  split; f_equal; f_equal; com_simpl.
  all: apply com_proj_eq.
  all: simpl.
  all: try lra.
  all: ring_simplify; simpl.
  all: rewrite Rmult_1_r, <- Rinv_mult, sqrt_sqrt.
  all: lra.
Qed.

Lemma Gate_H_matrix_gphase:
  mat_rot PI2 0 PI = gphase (- PI2) .* Gate_H_matrix.
Proof.
  unfold mat_rot, gphase.
  rewrite mat_rot_z_0_eye.
  mat_simpl. com_simpl.
  replace (PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  rewrite sin_PI4, cos_PI4.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_P_matrix_mul:
  forall (l1 l2: R),
  (mat_rot 0 0 l1) * (mat_rot 0 0 l2) = mat_rot 0 0 (l1 + l2)%R.
Proof.
  intros l1 l2.
  unfold mat_rot.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  mat_simpl.
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
  mat_sort.
  unfold gphase.
  rewrite com_iexp_PI.
  replace ((-1)%R * (-1)%R)%com with Cone by lca.
  rewrite mat_scale_1.
  reflexivity.
Qed.

Lemma Gate_matrix_X_Y__eq__Z:
  Gate_X_matrix * Gate_Y_matrix = gphase PI2 .* Gate_Z_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_matrix_Y_X__eq__Z:
  Gate_Y_matrix * Gate_X_matrix = gphase (-PI2) .* Gate_Z_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_matrix_Y_Z__eq__X:
  Gate_Y_matrix * Gate_Z_matrix = gphase PI2 .* Gate_X_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_matrix_Z_Y__eq__X:
  Gate_Z_matrix * Gate_Y_matrix = gphase (-PI2) .* Gate_X_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_matrix_Z_X__eq__Y:
  Gate_Z_matrix * Gate_X_matrix = gphase PI2 .* Gate_Y_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_matrix_X_Z__eq__Y:
  Gate_X_matrix * Gate_Z_matrix = gphase (-PI2) .* Gate_Y_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; lca.
Qed.

End Gate_properties.
