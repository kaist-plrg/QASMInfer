Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section Equivalence.

Variable nq: nat.
Variable nc: nat.

Definition ProgramState_equiv (ps1 ps2: ProgramState nq): Prop :=
  PositiveMap.Equal ps1 ps2.

Definition ProgramState_behavioral_equiv (ps1 ps2: ProgramState nq): Prop :=
  forall (cstate: positive),
  (PositiveMap.find cstate ps1 = None /\ PositiveMap.find cstate ps2 = None) \/
  (exists branch1 branch2, PositiveMap.find cstate ps1 = Some branch1 /\ PositiveMap.find cstate ps2 = Some branch2 /\ B_prob nq branch1 = B_prob nq branch2).

Definition Instruction_equiv (instr1 instr2: Instruction): Prop :=
  forall (ps: ProgramState nq),
  ProgramState_invariant nq ps ->
  ProgramState_equiv
  (Execute_suppl nq instr1 ps)
  (Execute_suppl nq instr2 ps).

Lemma ProgramState_equiv_implies_behavioral_equiv:
  forall (ps1 ps2: ProgramState nq),
  ProgramState_equiv ps1 ps2 -> ProgramState_behavioral_equiv ps1 ps2.
Proof.
    intros ps1 ps2 Heq.
    unfold ProgramState_behavioral_equiv.
    intros cstate.
    unfold ProgramState_equiv, PositiveMap.Equal in Heq.
    destruct (PositiveMap.find cstate ps1) eqn:H1.
    - right. exists b. exists b.
      split; split.
      { rewrite <- Heq. apply H1. }
      { reflexivity. }
    - left.
      split.
      { reflexivity. }
      { rewrite <- Heq. apply H1. }
Qed.

End Equivalence.