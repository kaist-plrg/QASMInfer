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

(* ============================================================================================== *)
(* Equivalence Definition ======================================================================= *)

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

Definition Instruction_behavioral_equiv (instr1 instr2: Instruction): Prop :=
  forall (ps: ProgramState nq),
  ProgramState_invariant nq ps ->
  ProgramState_behavioral_equiv
  (Execute_suppl nq instr1 ps)
  (Execute_suppl nq instr2 ps).

(* Equality of result, weakest equality definition *)
Definition Instruction_result_equiv (instr1 instr2: Instruction): Prop :=
  Execute_and_calculate_prob nq nc instr1 = Execute_and_calculate_prob nq nc instr2.

(* ============================================================================================== *)
(* Check equivalence ============================================================================ *)

Lemma ProgramState_equiv_equivalence: Equivalence ProgramState_equiv.
Proof.
  apply PFacts.Equal_ST.
Qed.

Lemma ProgramState_behavioral_equiv_equivalence: Equivalence ProgramState_behavioral_equiv.
Proof.
  split.
  - intros ps.
    unfold ProgramState_behavioral_equiv.
    intros cstate.
    destruct (PositiveMap.find cstate ps).
    + right. exists b, b.
      repeat split; reflexivity.
    + left. split; reflexivity.
  - intros ps1 ps2 H.
    unfold ProgramState_behavioral_equiv in *.
    intros cstate.
    specialize (H cstate).
    destruct H as [[H1 H2] | (branch1 & branch2 & Hf1 & Hf2 & Hb)].
    + left. split; assumption.
    + right. exists branch2, branch1.
      repeat split; try assumption.
      symmetry; assumption.
  - intros ps1 ps2 ps3 H1 H2.
    unfold ProgramState_behavioral_equiv in *.
    intros cstate.
    specialize (H1 cstate).
    specialize (H2 cstate).
    destruct H1 as [[H1none H2none] | (b1 & b2 & H1some & H2some & Hb12)].
    + destruct H2 as [[_ H3none] | (b2' & b3 & H2some' & _ & _)].
      * left. split; assumption.
      * rewrite H2none in H2some'. discriminate.
    + destruct H2 as [[H2none _] | (b2' & b3 & H2some' & H3some & Hb23)].
      * rewrite H2some in H2none. discriminate.
      * rewrite H2some in H2some'. inversion H2some'. subst b2'.
        right. exists b1, b3.
        repeat split; try assumption.
        eapply eq_trans.
        -- exact Hb12.
        -- exact Hb23.
Qed.

Lemma Instruction_equiv_equivalence: Equivalence Instruction_equiv.
Proof.
  split.
  - intros instr.
    unfold Instruction_equiv.
    intros ps Hinv.
    apply ProgramState_equiv_equivalence.
  - intros instr1 instr2 H.
    unfold Instruction_equiv in *.
    intros ps Hinv.
    apply ProgramState_equiv_equivalence.
    apply H.
    apply Hinv.
  - intros instr1 instr2 instr3 H1 H2.
    unfold Instruction_equiv in *.
    intros ps Hinv.
    apply ProgramState_equiv_equivalence with (y := Execute_suppl nq instr2 ps).
    + apply H1. apply Hinv.
    + apply H2. apply Hinv.
Qed.

Lemma Instruction_behavioral_equiv_equivalence: Equivalence Instruction_behavioral_equiv.
Proof.
  split.
  - intros instr.
    unfold Instruction_behavioral_equiv.
    intros ps Hinv.
    apply ProgramState_behavioral_equiv_equivalence.
  - intros instr1 instr2 H.
    unfold Instruction_equiv in *.
    intros ps Hinv.
    apply ProgramState_behavioral_equiv_equivalence.
    apply H.
    apply Hinv.
  - intros instr1 instr2 instr3 H1 H2.
    unfold Instruction_equiv in *.
    intros ps Hinv.
    apply ProgramState_behavioral_equiv_equivalence with (y := Execute_suppl nq instr2 ps).
    + apply H1. apply Hinv.
    + apply H2. apply Hinv.
Qed.

Lemma Instruction_result_equiv_equivalence: Equivalence Instruction_result_equiv.
Proof.
  split.
  - intros instr.
    unfold Instruction_result_equiv.
    reflexivity.
  - intros instr1 instr2 H.
    unfold Instruction_result_equiv in *.
    symmetry. apply H.
  - intros instr1 instr2 instr3 H1 H2.
    unfold Instruction_result_equiv in *.
    rewrite H1, H2. reflexivity.
Qed.

(* ============================================================================================== *)
(* Proof of equivalence ========================================================================= *)

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

Corollary Instruction_equiv_implies_behavioral_equiv:
  forall (instr1 instr2: Instruction),
  Instruction_equiv instr1 instr2 -> Instruction_behavioral_equiv instr1 instr2.
Proof.
  intros instr1 instr2 Hequiv ps Hinv.
  apply ProgramState_equiv_implies_behavioral_equiv.
  apply Hequiv.
  apply Hinv.
Qed.

Theorem Instruction_equiv_rewrite:
  forall (pre_instr post_instr instr1 instr2: Instruction),
  Instruction_equiv instr1 instr2 ->
  Instruction_equiv
  (SeqInstr pre_instr (SeqInstr instr1 post_instr))
  (SeqInstr pre_instr (SeqInstr instr2 post_instr)).
Proof.
  intros pre post instr1 instr2 Hequiv ps Hinv.
  simpl.
  unfold ProgramState_equiv.
  remember (Execute_suppl nq pre ps) as ps'.
Admitted.

End Equivalence.