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

Lemma Gate_X_matrix_Hermitian:
  forall (qbit: nat), mat_Hermitian (Gate_X_matrix qbit).
Proof.
  intros qbit.
  unfold Gate_X_matrix.
  apply mat_single_Hermitian.
  unfold mat_rot.
  simpl. com_simpl.
  replace (- 0 / 2)%R with 0%R by field.
  replace (0 / 2)%R with 0%R by field.
  rewrite com_iexp_0, cos_PI2, sin_PI2.
  com_simpl.
  (* mat_rot PI 0 PI is NOT Hermitian. *)
  (* [ 0 -i ] *)
  (* [ -i 0 ] *)
Admitted.

End Gate_properties.
