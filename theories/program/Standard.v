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

Lemma Gate_X_matrix_unitary:
  forall (qbit: nat), mat_unitary (Gate_X_matrix qbit).
Proof.
  intros qbit.
  unfold Gate_X_matrix.
  apply mat_single_unitary.
  apply mat_rot_unitary.
Qed.

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

Lemma Gate_X_matrix_square:
  forall (qbit: nat), nq > qbit ->
  (Gate_X_matrix qbit) * (Gate_X_matrix qbit) = (-1)%R .* mat_eye.
Proof.
  intros qbit H.
  unfold Gate_X_matrix.
  rewrite mat_single_factorized.
  rewrite Gate_X_rot_matrix_square.
  rewrite (mat_single_scale nq qbit mat_eye _ H).
  rewrite mat_single_eye.
  reflexivity.
Qed.

End Gate_properties.
