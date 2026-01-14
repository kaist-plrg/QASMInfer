Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.
Module POrd := OrdProperties PositiveMap.

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
(* Proof about equivalance preservation (Proper) of Execute_suppl =============================== *)

Lemma fold_left_eqlistA_Proper
  {A B} (RA : relation A) (RB : relation B)
  (step : B -> A -> B) :
  (forall a1 a2 b1 b2, RA a1 a2 -> RB b1 b2 -> RB (step b1 a1) (step b2 a2)) ->
  forall l1 l2 acc1 acc2,
    eqlistA RA l1 l2 ->
    RB acc1 acc2 ->
    RB (fold_left step l1 acc1) (fold_left step l2 acc2).
Proof.
  intros Hstep l1 l2 acc1 acc2 Hel Hacc.
  revert acc1 acc2 Hacc.
  induction Hel; intros acc1 acc2 Hacc; simpl.
  - exact Hacc.
  - apply IHHel.
    apply (Hstep x x' acc1 acc2); assumption.
Qed.

Lemma PositiveMap_fold_Proper_gen
  (f : positive -> Branch nq -> ProgramState nq -> ProgramState nq):
  (forall k b, Proper (ProgramState_equiv ==> ProgramState_equiv) (f k b)) ->
  Proper (ProgramState_equiv ==> ProgramState_equiv ==> ProgramState_equiv)
         (fun ps base_ps => PositiveMap.fold f ps base_ps).
Proof.
  intros Hf ps1 ps2 Heq base1 base2 Heqbase.
  rewrite PositiveMap.fold_1, PositiveMap.fold_1.
  apply (fold_left_eqlistA_Proper (POrd.O.eqke (elt:=Branch nq))).
  - intros [k1 b1] [k2 b2] acc1 acc2 Hpq Hacc.
    destruct Hpq as [Hk Hb]. simpl in *.
    rewrite Hk, Hb.
    apply Hf. apply Hacc.
  - apply POrd.elements_Equal_eqlistA.
    apply Heq.
  - apply Heqbase.
Qed.

Lemma PositiveMap_add_Proper (k: positive) (b: Branch nq):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (PositiveMap.add k b).
Proof.
  intros ps1 ps2 Heq.
  unfold ProgramState_equiv, PositiveMap.Equal in *.
  intros k'.
  rewrite PFacts.add_o, PFacts.add_o.
  destruct (PProperties.F.eq_dec k k').
  - reflexivity.
  - apply Heq.
Qed.

Lemma Execute_rotate_instr_Proper (theta phi lambda: R) (target: nat):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_rotate_instr nq theta phi lambda target).
Proof.
  intros ps1 ps2 Heq cstate.
  unfold Execute_rotate_instr.
  rewrite PFacts.map_o, PFacts.map_o.
  f_equal.
  apply Heq.
Qed.

Lemma Execute_cnot_instr_Proper (control target: nat):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_cnot_instr nq control target).
Proof.
  intros ps1 ps2 Heq cstate.
  unfold Execute_cnot_instr.
  rewrite PFacts.map_o, PFacts.map_o.
  f_equal.
  apply Heq.
Qed.

Lemma Execute_swap_instr_Proper (q1 q2: nat):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_swap_instr nq q1 q2).
Proof.
  intros ps1 ps2 Heq cstate.
  unfold Execute_swap_instr.
  rewrite PFacts.map_o, PFacts.map_o.
  f_equal.
  apply Heq.
Qed.

Lemma ProgramState_merge_step_Proper (k: positive) (b: Branch nq):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (merge_step nq k b).
Proof.
  intros ps1 ps2 Heq.
  unfold merge_step.
  rewrite Heq.
  destruct (PositiveMap.find k ps2).
  - apply PositiveMap_add_Proper. apply Heq.
  - apply PositiveMap_add_Proper. apply Heq.
Qed.

Lemma ProgramState_merge_Proper:
  Proper (ProgramState_equiv ==> ProgramState_equiv ==> ProgramState_equiv) (ProgramState_merge nq).
Proof.
  intros ps1 ps2 Heq ps1' ps2' Heq'.
  unfold ProgramState_merge.
  apply PositiveMap_fold_Proper_gen; try assumption.
  apply ProgramState_merge_step_Proper.
Qed.

Lemma Execute_measure_instr_Proper (qbit cbit: nat):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_measure_instr nq qbit cbit).
Proof.
  intros ps1 ps2 Heq cstate.
  unfold Execute_measure_instr.
  apply PositiveMap_fold_Proper_gen.
  - intros k b ps1' ps2' Heq'.
    apply ProgramState_merge_Proper.
    + apply Heq'.
    + apply ProgramState_equiv_equivalence.
  - apply Heq.
  - apply ProgramState_equiv_equivalence.
Qed.

Lemma Execute_reset_instr_Proper (target: nat):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_reset_instr nq target).
Proof.
  intros ps1 ps2 Heq cstate.
  unfold Execute_reset_instr.
  rewrite PFacts.map_o, PFacts.map_o.
  f_equal.
  apply Heq.
Qed.

Lemma Execute_suppl_Proper (instr: Instruction):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_suppl nq instr).
Proof.
  induction instr; intros ps1 ps2 Heq; simpl.
  - assumption.
  - apply Execute_rotate_instr_Proper. assumption.
  - apply Execute_cnot_instr_Proper. assumption.
  - apply Execute_swap_instr_Proper. assumption.
  - apply Execute_measure_instr_Proper. assumption.
  - apply IHinstr2. apply IHinstr1. assumption.
  - apply PositiveMap_fold_Proper_gen.
    + intros k b' ps1' ps2' Heq'.
      apply ProgramState_merge_Proper.
      * apply Heq'.
      * apply ProgramState_equiv_equivalence.
    + apply Heq.
    + apply ProgramState_equiv_equivalence.
  - apply Execute_reset_instr_Proper. assumption.
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
  assert (Hinv': ProgramState_invariant nq ps').
  {
    rewrite Heqps'. apply Execute_suppl_valid_invariant. apply Hinv.
  }
  apply Execute_suppl_Proper.
  apply (Hequiv ps' Hinv').
Qed.

Theorem Instruction_equiv_nop:
  forall (pre_instr post_instr: Instruction),
  Instruction_equiv
  (SeqInstr pre_instr (SeqInstr NopInstr post_instr))
  (SeqInstr pre_instr post_instr).
Proof.
  intros pre post ps Hinv.
  simpl.
  apply Execute_suppl_Proper.
  apply ProgramState_equiv_equivalence.
Qed.

End Equivalence.