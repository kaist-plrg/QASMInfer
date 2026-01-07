Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equivalence.
Require Import QASMInfer.transform.Gates.

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

Lemma Transform_I: forall (ps: ProgramState nq) (qbit: nat),
  ProgramState_equivalence nq
  (Execute_suppl nq (Gate_I qbit) ps)
  ps.
Proof.
    intros ps qbit.
    unfold ProgramState_equivalence, PositiveMap.Equal.
    intros y.
    unfold Gate_I.
    simpl.
    reflexivity.
Qed.

Lemma Transform_X_X: forall (ps: ProgramState nq) (qbit: nat),
  ProgramState_equivalence nq
  (Execute_suppl nq (SeqInstr (Gate_X qbit) (Gate_X qbit)) ps)
  ps.
Proof.
    intros ps qbit.
    unfold ProgramState_equivalence, PositiveMap.Equal.
    intros y.
    unfold Gate_X.
    simpl.
    destruct (PositiveMap.find y ps) eqn:Hfind.
    - rewrite <- PFacts.find_mapsto_iff.
      rewrite <- PFacts.find_mapsto_iff in Hfind.
      unfold Execute_rotate_instr.
      apply PositiveMap.map_1 with (f:=Execute_rotate_instr_branch nq pi 0 pi qbit) in Hfind.
      apply PositiveMap.map_1 with (f:=Execute_rotate_instr_branch nq pi 0 pi qbit) in Hfind.
      
Admitted.

End Transform.