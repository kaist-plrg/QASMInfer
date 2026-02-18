(* TODO: Add widely-used gates e.g., gates in stdlib.inc *)
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.program.Program.
From Stdlib Require Export Program.Equality.

From Stdlib.FSets Require Import FMapPositive FMapFacts.

Bind Scope Complex_scope with Complex.
Open Scope Matrix_scope.

Section GATES.
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

End GATES.

Notation "'I' q" := (Gate_I q) (in custom qasm at level 0, q constr at level 0).
Notation "'X' q" := (Gate_X q) (in custom qasm at level 0, q constr at level 0).
Notation "'Y' q" := (Gate_Y q) (in custom qasm at level 0, q constr at level 0).
Notation "'Z' q" := (Gate_Z q) (in custom qasm at level 0, q constr at level 0).

Notation "'H' q" := (Gate_H q) (in custom qasm at level 0, q constr at level 0).
Notation "'S' q" := (Gate_S q) (in custom qasm at level 0, q constr at level 0).
Notation "'Sdg' q" := (Gate_Sdg q) (in custom qasm at level 0, q constr at level 0).

Notation "'P' ( λ ) q" :=
  (Gate_P λ q)
  (in custom qasm at level 0, λ constr at level 0, q constr at level 0).

Section GATE_PROPERTIES.

Variable nq: nat.

Definition gphase (theta: R): Complex :=
  com_iexp theta.

Lemma den_uop_gphase:
  forall (theta: R) (A U: Matrix nq),
  den_uop (gphase theta .* A) U = den_uop A U.
Proof.
  intros theta A U.
  unfold den_uop.
  rewrite mat_scale_conjtrans.
  mat_sort.
  com_simpl.
  mat_simpl.
Qed.

Lemma mat_Hermitian_unitary__involutory:
  forall {n: nat} (A: Matrix n),
  mat_Hermitian A -> mat_unitary A -> A * A = mat_eye.
Proof.
  intros n A HH Hu.
  rewrite <- HH at 2.
  apply (proj2 Hu).
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
  unfold mat_rot_z.
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
  mat_simpl. unfold mat_rot_z.
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

Lemma Gate_matrix_H_X__eq__Z_H:
  Gate_H_matrix * Gate_X_matrix = Gate_Z_matrix * Gate_H_matrix.
Proof.
  com_simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_matrix_H_Y__eq__Y_H:
  Gate_H_matrix * Gate_Y_matrix = gphase PI .* Gate_Y_matrix * Gate_H_matrix.
Proof.
  unfold gphase; com_simpl.
  f_equal; f_equal; com_simpl.
Qed.

Lemma Gate_matrix_H_Z__eq__X_H:
  Gate_H_matrix * Gate_Z_matrix = Gate_X_matrix * Gate_H_matrix.
Proof.
  com_simpl.
  f_equal; f_equal; lca.
Qed.

Corollary Gate_matrix_H_X_H__eq__Z:
  Gate_H_matrix * Gate_X_matrix * Gate_H_matrix = Gate_Z_matrix.
Proof.
  rewrite Gate_matrix_H_X__eq__Z_H.
  rewrite <- mat_mul_assoc.
  rewrite (mat_Hermitian_unitary__involutory Gate_H_matrix).
  - mat_simpl.
  - apply Gate_H_matrix_Hermitian.
  - apply Gate_H_matrix_unitary.
Qed.

Corollary Gate_matrix_H_Y_H__eq__Y:
  Gate_H_matrix * Gate_Y_matrix * Gate_H_matrix = gphase PI .* Gate_Y_matrix.
Proof.
  rewrite Gate_matrix_H_Y__eq__Y_H.
  rewrite <- mat_mul_assoc.
  rewrite (mat_Hermitian_unitary__involutory Gate_H_matrix).
  - mat_simpl.
  - apply Gate_H_matrix_Hermitian.
  - apply Gate_H_matrix_unitary.
Qed.

Corollary Gate_matrix_H_Z_H__eq__X:
  Gate_H_matrix * Gate_Z_matrix * Gate_H_matrix = Gate_X_matrix.
Proof.
  rewrite <- mat_mul_assoc.
  rewrite <- Gate_matrix_H_X__eq__Z_H.
  mat_sort.
  rewrite (mat_Hermitian_unitary__involutory Gate_H_matrix).
  - mat_simpl.
  - apply Gate_H_matrix_Hermitian.
  - apply Gate_H_matrix_unitary.
Qed.

End GATE_PROPERTIES.

Section GATE_MATRIX_CORRESPONDENCE.

Variable nq: nat.

Definition Matrix_of (instr: Instruction) (mat: Matrix nq): Prop :=
  forall (ps: ProgramState nq),
  PositiveMap.Equal
  (Execute_suppl nq instr ps)
  (PositiveMap.map (fun b => {|
    B_qstate := den_uop mat (B_qstate nq b);
    B_prob := B_prob nq b
  |}) ps).

Inductive Matrix_of_list : list Instruction -> list (Matrix nq) -> Prop :=
| nil_mat :
    Matrix_of_list nil nil
| cons_mat :
  forall (instr : Instruction) (mat : Matrix nq)
    (ilist : list Instruction) (mlist : list (Matrix nq)),
  Matrix_of instr mat ->
  Matrix_of_list ilist mlist ->
  Matrix_of_list (instr :: ilist) (mat :: mlist).

Lemma Matrix_of_list_id:
  forall {lst: list Instruction} {mlst: list (Matrix nq)},
  forall (ps: ProgramState nq),
  Matrix_of_list lst mlst ->
  PositiveMap.Equal
  (Execute_suppl nq qasm{ seq[ lst ] } ps)
  (PositiveMap.map (fun b => {|
    B_qstate := den_uop (List.fold_right (fun a b => b * a) mat_eye mlst) (B_qstate nq b);
    B_prob := B_prob nq b
  |}) ps).
Proof.
  intros lst mlst ps H cstate.
  revert ps.
  induction H; intros ps.
  - simpl. rewrite PFacts.map_o.
    destruct (PositiveMap.find cstate ps); simpl.
    + f_equal. destruct b. f_equal. simpl.
      unfold den_uop.
      rewrite mat_eye_conjtrans.
      mat_simpl.
    + reflexivity.
  - replace (Execute_suppl nq qasm{ seq[ (instr :: ilist)]} ps) with
    (Execute_suppl nq qasm{ seq[ ilist ]} (Execute_suppl nq instr ps)) by reflexivity.
    rewrite IHMatrix_of_list.
    rewrite PFacts.map_o, PFacts.map_o.
    rewrite H, PFacts.map_o.
    destruct (PositiveMap.find cstate ps); simpl.
    + f_equal. destruct b. f_equal.
      rewrite den_uop_den_uop. reflexivity.
    + reflexivity.
Qed.

Lemma Matrix_of_I {qbit: nat}:
  qbit < nq ->
  Matrix_of (qasm{ I qbit }) (mat_eye).
Proof.
  intros Hvalid ps cstate.
  simpl.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal; f_equal; f_equal.
  rewrite Gate_P_matrix_0_eye.
  apply mat_single_eye.
Qed.  

Lemma Matrix_of_X {qbit: nat}:
  qbit < nq ->
  Matrix_of qasm{ X qbit } (mat_single nq qbit Gate_X_matrix).
Proof.
  intros Hvalid ps. simpl.
  intros cstate.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal. rewrite Gate_X_matrix_gphase.
  rewrite (mat_single_scale _ _ Hvalid).
  rewrite den_uop_gphase.
  reflexivity.
Qed.

Lemma Matrix_of_Y {qbit: nat}:
  qbit < nq ->
  Matrix_of qasm{ Y qbit } (mat_single nq qbit Gate_Y_matrix).
Proof.
  intros Hvalid ps. simpl.
  intros cstate.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal. rewrite Gate_Y_matrix_gphase.
  rewrite (mat_single_scale _ _ Hvalid).
  rewrite den_uop_gphase.
  reflexivity.
Qed.

Lemma Matrix_of_Z {qbit: nat}:
  qbit < nq ->
  Matrix_of qasm{ Z qbit } (mat_single nq qbit Gate_Z_matrix).
Proof.
  intros Hvalid ps. simpl.
  intros cstate.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal. rewrite Gate_Z_matrix_gphase.
  rewrite (mat_single_scale _ _ Hvalid).
  rewrite den_uop_gphase.
  reflexivity.
Qed.

Lemma Matrix_of_H {qbit: nat}:
  qbit < nq ->
  Matrix_of qasm{ H qbit } (mat_single nq qbit Gate_H_matrix).
Proof.
  intros Hvalid ps. simpl.
  intros cstate.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal. rewrite Gate_H_matrix_gphase.
  rewrite (mat_single_scale _ _ Hvalid).
  rewrite den_uop_gphase.
  reflexivity.
Qed.

Lemma Matrix_of_P {qbit: nat} (lambda: R):
  qbit < nq ->
  Matrix_of qasm{ P(lambda) qbit } (mat_single nq qbit (mat_rot 0 0 lambda)).
Proof.
  intros Hvalid ps. simpl.
  intros cstate. reflexivity.
Qed.

Lemma Matrix_of_cnot {qbit1 qbit2: nat}:
  qbit1 < nq -> qbit2 < nq ->
  Matrix_of qasm{ cx qbit1 qbit2 } (mat_cnot qbit1 qbit2).
Proof.
  intros Hvalid1 Hvalid2 ps. simpl.
  intros cstate. reflexivity.
Qed.

Lemma Matrix_of_swap {qbit1 qbit2: nat}:
  qbit1 < nq -> qbit2 < nq ->
  Matrix_of qasm{ swap qbit1 qbit2 } (mat_swap qbit1 qbit2).
Proof.
  intros Hvalid1 Hvalid2 ps. simpl.
  intros cstate. reflexivity.
Qed.

Lemma Matrix_of_U {qbit: nat} (theta phi lambda: R):
  Matrix_of qasm{ U (theta, phi, lambda) qbit } (mat_single nq qbit (mat_rot theta phi lambda)).
Proof.
  intros ps. simpl.
  intros cstate. reflexivity.
Qed.

End GATE_MATRIX_CORRESPONDENCE.

Ltac mat_of_single H :=
  repeat (
    apply nil_mat ||
    apply cons_mat ||
    apply (Matrix_of_X _ H) ||
    apply (Matrix_of_Y _ H) ||
    apply (Matrix_of_Z _ H) ||
    apply (Matrix_of_I _ H) ||
    apply (Matrix_of_H _ H) ||
    apply Matrix_of_U
  ).

Ltac mat_of_double H1 H2 :=
  repeat (
    apply nil_mat ||
    apply cons_mat ||
    apply (Matrix_of_X _ H1) ||
    apply (Matrix_of_Y _ H1) ||
    apply (Matrix_of_Z _ H1) ||
    apply (Matrix_of_I _ H1) ||
    apply (Matrix_of_H _ H1) ||
    apply (Matrix_of_X _ H2) ||
    apply (Matrix_of_Y _ H2) ||
    apply (Matrix_of_Z _ H2) ||
    apply (Matrix_of_I _ H2) ||
    apply (Matrix_of_H _ H2) ||
    apply Matrix_of_U ||
    apply (Matrix_of_cnot _ H1 H2) ||
    apply (Matrix_of_cnot _ H2 H1) ||
    apply (Matrix_of_swap _ H1 H2) ||
    apply (Matrix_of_swap _ H2 H1)
  ).