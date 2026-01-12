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
  change (mat_single nq qbit (mat_rot PI 0 PI)) with (Gate_X_matrix nq qbit).
  remember (Gate_X_matrix nq qbit) as A.
  unfold den_uop.
  rewrite (mat_mul_assoc A _ _), (mat_mul_assoc A _ _), <- (mat_mul_assoc _ (A†) (A†)).
  rewrite <- mat_mul_conjtrans.
  rewrite HeqA.
  rewrite (Gate_X_matrix_square _ _ H).
  rewrite mat_scale_conjtrans, mat_scale_mul_assoc, mat_mul_eye_l.
  rewrite mat_scale_mul_comm, <- mat_scale_cmul_assoc, mat_eye_conjtrans.
  rewrite <- mat_scale_mul_comm, mat_mul_eye_r.
  com_simpl.
  assert (Hcom: ((-1)%R * (-1)%R = Cone)%com). unfold com_mul, Cone. simpl. f_equal. lra. lra.
  rewrite Hcom, mat_scale_1. reflexivity. 
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
    apply PositiveMap.map_1 with (f:=Execute_rotate_instr_branch nq PI 0 PI qbit) in Hfind.
    apply PositiveMap.map_1 with (f:=Execute_rotate_instr_branch nq PI 0 PI qbit) in Hfind.
    remember (Execute_rotate_instr_branch nq PI 0 PI qbit (Execute_rotate_instr_branch nq PI 0 PI qbit b)) as b'.
    rewrite <- (Transform_X_X_Branch _ _ H) in Heqb'.
    rewrite <- Heqb'.
    apply Hfind.
  - unfold Execute_rotate_instr.
    rewrite PFacts.map_o, PFacts.map_o.
    rewrite Hfind.
    simpl. reflexivity.
Qed.

End Transform.
