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
  intros cstate.
  simpl.
  reflexivity.
Qed.

Lemma Transform_den_uop_involutive:
  forall (A Q: Matrix nq),
  mat_unitary A -> mat_Hermitian A ->
  den_uop A (den_uop A Q) = Q.
Proof.
  intros A Q Hu HH.
  unfold den_uop.
  rewrite mat_mul_assoc, mat_mul_assoc.
  rewrite <- HH at 2. rewrite HH at 2.
  rewrite (proj2 Hu), mat_mul_eye_l.
  rewrite <- mat_mul_assoc.
  rewrite (proj2 Hu), mat_mul_eye_r.
  reflexivity.
Qed.

Lemma Transform_X_X_Branch:
  forall (b: Branch nq) (qbit: nat),
  Qbit_index_valid qbit ->
  b = Execute_rotate_instr_branch nq PI 0 PI qbit (Execute_rotate_instr_branch nq PI 0 PI qbit b).
Proof.
  intros b qbit H.
  unfold Execute_rotate_instr_branch.
  destruct b eqn:Hb.
  simpl.
  f_equal.
  rewrite Gate_X_matrix_gphase.
  rewrite (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
  rewrite Transform_den_uop_involutive.
  - reflexivity.
  - apply mat_single_unitary. apply Gate_X_matrix_unitary.
  - apply mat_single_Hermitian. apply Gate_X_matrix_Hermitian.
Qed.

Lemma Transform_X_X: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_X qbit) (Gate_X qbit))
  (Gate_I qbit).
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  destruct (PositiveMap.find cstate ps) eqn:Hfind.
  - rewrite <- PFacts.find_mapsto_iff.
    rewrite <- PFacts.find_mapsto_iff in Hfind.
    unfold Execute_rotate_instr.
    rewrite (Transform_X_X_Branch _ _ H).
    apply PositiveMap.map_1.
    apply PositiveMap.map_1.
    apply Hfind.
  - unfold Execute_rotate_instr.
    rewrite PFacts.map_o, PFacts.map_o.
    rewrite Hfind.
    simpl. reflexivity.
Qed.

Lemma Transform_Y_Y_Branch:
  forall (b: Branch nq) (qbit: nat),
  Qbit_index_valid qbit ->
  b = Execute_rotate_instr_branch nq PI PI2 PI2 qbit (Execute_rotate_instr_branch nq PI PI2 PI2 qbit b).
Proof.
  intros b qbit H.
  unfold Execute_rotate_instr_branch.
  destruct b eqn:Hb.
  simpl.
  f_equal.
  rewrite Gate_Y_matrix_gphase.
  rewrite (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
  rewrite Transform_den_uop_involutive.
  - reflexivity.
  - apply mat_single_unitary. apply Gate_Y_matrix_unitary.
  - apply mat_single_Hermitian. apply Gate_Y_matrix_Hermitian.
Qed.

Lemma Transform_Y_Y: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Y qbit) (Gate_Y qbit))
  (Gate_I qbit).
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  destruct (PositiveMap.find cstate ps) eqn:Hfind.
  - rewrite <- PFacts.find_mapsto_iff.
    rewrite <- PFacts.find_mapsto_iff in Hfind.
    unfold Execute_rotate_instr.
    rewrite (Transform_Y_Y_Branch _ _ H).
    apply PositiveMap.map_1.
    apply PositiveMap.map_1.
    apply Hfind.
  - unfold Execute_rotate_instr.
    rewrite PFacts.map_o, PFacts.map_o.
    rewrite Hfind.
    simpl. reflexivity.
Qed.

Lemma Transform_Z_Z_Branch:
  forall (b: Branch nq) (qbit: nat),
  Qbit_index_valid qbit ->
  b = Execute_rotate_instr_branch nq 0 0 PI qbit (Execute_rotate_instr_branch nq 0 0 PI qbit b).
Proof.
  intros b qbit H.
  unfold Execute_rotate_instr_branch.
  destruct b eqn:Hb.
  simpl.
  f_equal.
  rewrite Gate_Z_matrix_gphase.
  rewrite (Gate_matrix_den_uop_gphase _ _ H), (Gate_matrix_den_uop_gphase _ _ H).
  rewrite Transform_den_uop_involutive.
  - reflexivity.
  - apply mat_single_unitary. apply Gate_Z_matrix_unitary.
  - apply mat_single_Hermitian. apply Gate_Z_matrix_Hermitian.
Qed.

Lemma Transform_Z_Z: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  (SeqInstr (Gate_Z qbit) (Gate_Z qbit))
  (Gate_I qbit).
Proof.
  intros qbit.
  unfold Instruction_equiv, ProgramState_equiv.
  intros H ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  destruct (PositiveMap.find cstate ps) eqn:Hfind.
  - rewrite <- PFacts.find_mapsto_iff.
    rewrite <- PFacts.find_mapsto_iff in Hfind.
    unfold Execute_rotate_instr.
    rewrite (Transform_Z_Z_Branch _ _ H).
    apply PositiveMap.map_1.
    apply PositiveMap.map_1.
    apply Hfind.
  - unfold Execute_rotate_instr.
    rewrite PFacts.map_o, PFacts.map_o.
    rewrite Hfind.
    simpl. reflexivity.
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
  destruct (PositiveMap.find cstate ps) eqn:Hfind.
Admitted.

End Transform.
