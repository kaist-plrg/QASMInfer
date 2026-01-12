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

Lemma Transform_I: forall (qbit: nat),
  Instruction_equivalence nq
  (Gate_I qbit)
  NopInstr.
Proof.
  intros qbit.
  unfold Instruction_equivalence, ProgramState_equivalence.
  intros ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate.
  simpl.
  reflexivity.
Qed.

Lemma Transform_X_X_Branch:
  forall (b: Branch nq) (qbit: nat),
  b = Execute_rotate_instr_branch nq PI 0 PI qbit (Execute_rotate_instr_branch nq PI 0 PI qbit b).
Proof.
  intros b qbit.
  unfold Execute_rotate_instr_branch.
  destruct b eqn:Hb.
  simpl.
  f_equal.
  remember (mat_single nq qbit (mat_rot PI 0 PI)) as A.
  assert (Hu: mat_unitary A).
  {
    rewrite HeqA. apply mat_single_unitary. apply mat_rot_unitary.
  }
  (* Problem: A is not Hermitian due to the global phase *)
  unfold den_uop.
  rewrite (mat_mul_assoc A _ _), (mat_mul_assoc A _ _).
  rewrite <- HH at 2. rewrite HH at 2.
  rewrite (proj2 Hu), mat_mul_eye_l, <- mat_mul_assoc.
  rewrite (proj2 Hu), mat_mul_eye_r.
  reflexivity.
Admitted.

Lemma Transform_X_X: forall (qbit: nat),
  Instruction_equivalence nq
  (SeqInstr (Gate_X qbit) (Gate_X qbit))
  (Gate_I qbit).
Proof.
  intros qbit.
  unfold Instruction_equivalence, ProgramState_equivalence.
  intros ps Hinv.
  unfold PositiveMap.Equal.
  intros cstate. simpl.
  destruct (PositiveMap.find cstate ps) eqn:Hfind.
  - rewrite <- PFacts.find_mapsto_iff.
    rewrite <- PFacts.find_mapsto_iff in Hfind.
    unfold Execute_rotate_instr.
    apply PositiveMap.map_1 with (f:=Execute_rotate_instr_branch nq PI 0 PI qbit) in Hfind.
    apply PositiveMap.map_1 with (f:=Execute_rotate_instr_branch nq PI 0 PI qbit) in Hfind.
    remember (Execute_rotate_instr_branch nq PI 0 PI qbit (Execute_rotate_instr_branch nq PI 0 PI qbit b)) as b'.
    rewrite <- Transform_X_X_Branch in Heqb'.
    rewrite <- Heqb'.
    apply Hfind.
  - unfold Execute_rotate_instr.
    rewrite PFacts.map_o, PFacts.map_o.
    rewrite Hfind.
    simpl. reflexivity.
Qed.

End Transform.
