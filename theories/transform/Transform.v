Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section Transform.

Variable nq: nat.

(* Qbit index validity : prevents index out of bounds *)
Definition Qbit_index_valid (qbit: nat): Prop :=
  nq > qbit.

Lemma Transform_I: forall (qbit: nat),
  Instruction_equiv nq
  (Gate_I qbit)
  NopInstr.
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite Gate_P_matrix_0_eye.
    rewrite mat_single_eye.
    unfold den_uop.
    rewrite mat_eye_conjtrans.
    mat_simpl.
  - reflexivity.
Qed.

Lemma Transform_den_uop_involutive:
  forall (A Q: Matrix nq),
  mat_unitary A -> mat_Hermitian A ->
  den_uop A (den_uop A Q) = Q.
Proof.
  intros A Q Hu HH.
  rewrite den_uop_den_uop.
  rewrite <- HH at 2.
  rewrite (proj2 Hu).
  unfold den_uop.
  rewrite mat_eye_conjtrans.
  mat_simpl.
Qed.

Lemma Transform_X_X: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_X qbit) (Gate_X qbit))
  NopInstr.
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite Gate_X_matrix_gphase, (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
    apply Transform_den_uop_involutive.
    + apply mat_single_unitary. apply Gate_X_matrix_unitary.
    + apply mat_single_Hermitian. apply Gate_X_matrix_Hermitian.
  - reflexivity.
Qed.

Lemma Transform_Y_Y: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Y qbit) (Gate_Y qbit))
  NopInstr.
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite Gate_Y_matrix_gphase, (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
    apply Transform_den_uop_involutive.
    + apply mat_single_unitary. apply Gate_Y_matrix_unitary.
    + apply mat_single_Hermitian. apply Gate_Y_matrix_Hermitian.
  - reflexivity.
Qed.

Lemma Transform_Z_Z: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Z qbit) (Gate_Z qbit))
  NopInstr.
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite Gate_Z_matrix_gphase, (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
    apply Transform_den_uop_involutive.
    + apply mat_single_unitary. apply Gate_Z_matrix_unitary.
    + apply mat_single_Hermitian. apply Gate_Z_matrix_Hermitian.
  - reflexivity.
Qed.

Lemma Transform_H_H: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_H qbit) (Gate_H qbit))
  NopInstr.
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite Gate_H_matrix_gphase, (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
    apply Transform_den_uop_involutive.
    + apply mat_single_unitary. apply Gate_H_matrix_unitary.
    + apply mat_single_Hermitian. apply Gate_H_matrix_Hermitian.
  - reflexivity.
Qed.

Lemma Transform_P_P: forall (qbit: nat) (l1 l2: R),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_P l1 qbit) (Gate_P l2 qbit))
  (Gate_P (l1 + l2)%R qbit).
Proof.
  intros qbit l1 l2 H.
  unfold Instruction_equiv, ProgramState_equiv.
  intros ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    simpl; f_equal.
    rewrite den_uop_den_uop. f_equal.
    rewrite mat_single_factorized. f_equal.
    rewrite Gate_P_matrix_mul.
    f_equal; lra.
  - reflexivity.
Qed.

Lemma Transform_P_periodic: forall (qbit: nat) (l: R),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (Gate_P l qbit)
  (Gate_P (l + 2*PI) qbit).
Proof.
  intros qbit l H.
  unfold Instruction_equiv, ProgramState_equiv.
  intros ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    f_equal.
    rewrite Gate_P_matrix_periodic.
    rewrite (Gate_matrix_den_uop_gphase _ _ H).
    reflexivity.
  - reflexivity. 
Qed.

Corollary Transform_S_S: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_S qbit) (Gate_S qbit))
  (Gate_Z qbit).
Proof.
  intros qbit H.
  unfold Gate_S, Gate_Z.
  replace PI with (PI2 + PI2)%R by (unfold PI; field).
  apply (Transform_P_P qbit _ _ H).
Qed.

Corollary Transform_S_Sdg: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_S qbit) (Gate_Sdg qbit))
  NopInstr.
Proof.
  intros qbit H.
  apply Instruction_equiv_equivalence with (y:= (Gate_I qbit)).
  - unfold Gate_S, Gate_Sdg, Gate_I.
    replace 0%R with (PI2 + (- PI2))%R by field.
    apply (Transform_P_P qbit _ _ H).
  - apply Transform_I.
Qed.

Corollary Transform_Sdg_S: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Sdg qbit) (Gate_S qbit))
  NopInstr.
Proof.
  intros qbit H.
  apply Instruction_equiv_equivalence with (y:= (Gate_I qbit)).
  - unfold Gate_S, Gate_Sdg, Gate_I.
    replace 0%R with ((- PI2) + PI2)%R by field.
    apply (Transform_P_P qbit _ _ H).
  - apply Transform_I.
Qed.

Corollary Transform_Sdg_Sdg: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Sdg qbit) (Gate_Sdg qbit))
  (Gate_Z qbit).
Proof.
  intros qbit H.
  unfold Gate_S, Gate_Sdg, Gate_Z.
  apply Instruction_equiv_equivalence with (y := Gate_P ((-PI2) + (-PI2)) qbit).
  - apply (Transform_P_P qbit _ _ H).
  - replace PI with ((-PI) + 2*PI)%R by field.
    replace ((- PI2) + (-PI2))%R with (-PI)%R by (unfold PI; field).
    apply (Transform_P_periodic qbit _ H).
Qed.

Lemma Transform_X_Y: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_X qbit) (Gate_Y qbit))
  (Gate_Z qbit).
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite den_uop_den_uop, mat_single_factorized.
    rewrite Gate_X_matrix_gphase, Gate_Y_matrix_gphase, Gate_Z_matrix_gphase.
    rewrite <- mat_scale_mul_comm, mat_scale_mul_assoc, mat_scale_mul_assoc.
    rewrite Gate_matrix_Y_X__eq__Z.
    repeat rewrite (Gate_matrix_den_uop_gphase _ _ H).
    reflexivity.
  - reflexivity.
Qed.

Lemma Transform_Y_X: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Y qbit) (Gate_X qbit))
  (Gate_Z qbit).
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    destruct b; simpl; f_equal.
    rewrite den_uop_den_uop, mat_single_factorized.
    rewrite Gate_X_matrix_gphase, Gate_Y_matrix_gphase, Gate_Z_matrix_gphase.
    rewrite <- mat_scale_mul_comm, mat_scale_mul_assoc, mat_scale_mul_assoc.
    rewrite Gate_matrix_X_Y__eq__Z.
    repeat rewrite (Gate_matrix_den_uop_gphase _ _ H).
    reflexivity.
  - reflexivity.
Qed.

End Transform.
