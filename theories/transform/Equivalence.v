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

(* Some thoughts: is this good definition? *)
Definition ProgramState_equivalence (ps1 ps2: ProgramState nq): Prop :=
  PositiveMap.Equal ps1 ps2.

Definition ProgramState_behavioral_equivalence (ps1 ps2: ProgramState nq): Prop :=
  forall (cstate: positive) (branch1 branch2: Branch nq) (prob1 prob2: R),
  ((PositiveMap.MapsTo cstate branch1 ps1 /\ prob1 = B_prob nq branch1) \/ (~PositiveMap.MapsTo cstate branch1 ps1 /\ prob1 = 0%R)) ->
  ((PositiveMap.MapsTo cstate branch2 ps2 /\ prob2 = B_prob nq branch2) \/ (~PositiveMap.MapsTo cstate branch2 ps2 /\ prob2 = 0%R)) ->
  prob1 = prob2.

Lemma ProgramState_equivalence_implies_behavioral:
  forall (ps1 ps2: ProgramState nq),
  ProgramState_equivalence ps1 ps2 -> ProgramState_behavioral_equivalence ps1 ps2.
Proof.
    intros ps1 ps2 Heq.
    unfold ProgramState_behavioral_equivalence.
    intros cstate branch1 branch2 prob1 prob2 H1 H2.
    unfold ProgramState_equivalence in Heq.
    destruct H1 as [[Hin Hprob] | [Hnin Hprob]].
    -
Admitted.

End Equivalence.