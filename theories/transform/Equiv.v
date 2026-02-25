Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.
From Stdlib Require Import RelationClasses Morphisms Setoid.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.
Module POrd := OrdProperties PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section EQUIVALENCE.

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

(* To prove if case *)
Definition Instruction_valid_equiv (instr1 instr2: Instruction): Prop :=
  forall (ps: ProgramState nq),
  ProgramState_valid nq ps ->
  ProgramState_equiv
  (Execute_suppl nq instr1 ps)
  (Execute_suppl nq instr2 ps).

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

Lemma Instruction_valid_equiv_equivalence: Equivalence Instruction_valid_equiv.
Proof.
  split.
  - intros instr.
    unfold Instruction_valid_equiv.
    intros ps Hvalid.
    reflexivity.
  - intros instr1 instr2 H.
    unfold Instruction_valid_equiv in *.
    intros ps Hvalid.
    symmetry. apply H. apply Hvalid.
  - intros instr1 instr2 instr3 H1 H2.
    unfold Instruction_valid_equiv in *.
    intros ps Hvalid.
    apply ProgramState_equiv_equivalence with (y := Execute_suppl nq instr2 ps).
    + apply H1. apply Hvalid.
    + apply H2. apply Hvalid.
Qed.

Lemma Instruction_equiv_equivalence: Equivalence Instruction_equiv.
Proof.
  split.
  - intros instr.
    unfold Instruction_equiv.
    intros ps Hinv.
    reflexivity.
  - intros instr1 instr2 H.
    unfold Instruction_equiv in *.
    symmetry.
    apply H.
    apply H0.
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
  induction instr using Instruction_ind'; intros ps1 ps2 Heq; simpl.
  - assumption.
  - apply Execute_rotate_instr_Proper. assumption.
  - apply Execute_cnot_instr_Proper. assumption.
  - apply Execute_swap_instr_Proper. assumption.
  - apply Execute_measure_instr_Proper. assumption.
  - revert ps1 ps2 Heq.
    induction is; intros ps1 ps2 Heq.
    + simpl. apply Heq.
    + simpl. inversion H. apply IHis.
      * apply H3.
      * apply H2. apply Heq.
  - apply PositiveMap_fold_Proper_gen.
    + intros k b' ps1' ps2' Heq'.
      apply ProgramState_merge_Proper.
      * apply Heq'.
      * apply ProgramState_equiv_equivalence.
    + apply Heq.
    + apply ProgramState_equiv_equivalence.
  - apply Execute_reset_instr_Proper. assumption.
Qed.

(* Proving ProgramState_merge is symmetric *)
(* TODO - Is this really needed? *)

Lemma find_merge_step_eq :
  forall ps k b,
  PositiveMap.find k (merge_step nq k b ps) =
  match PositiveMap.find k ps with
  | Some b' => Some (Branch_merge nq b b')
  | None => Some b
  end.
Proof.
  intros ps k b.
  unfold merge_step.
  destruct (PositiveMap.find k ps) eqn:Hfind.
  - rewrite PFacts.add_eq_o; try reflexivity.
  - rewrite PFacts.add_eq_o; try reflexivity.
Qed.

Lemma find_merge_step_neq :
  forall ps k x b,
  k <> x ->
  PositiveMap.find x (merge_step nq k b ps) = PositiveMap.find x ps.
Proof.
  intros ps k x b Hneq.
  unfold merge_step.
  destruct (PositiveMap.find k ps) eqn:Hfind;
  rewrite PFacts.add_neq_o;
  try reflexivity;
  try assumption.
Qed.

Lemma Branch_merge_commute:
  forall b1 b2,
  Branch_merge nq b1 b2 = Branch_merge nq b2 b1.
Proof.
  intros [p1 q1] [p2 q2].
  unfold Branch_merge. simpl.
  f_equal.
  - rewrite mat_add_comm.
    f_equal; f_equal; f_equal; lca.
  - lra.
Qed.

Lemma Branch_merge_perm :
  forall b b1 b2,
  Branch_valid nq b ->
  Branch_valid nq b1 ->
  Branch_valid nq b2 ->
  Branch_merge nq b1 (Branch_merge nq b2 b) =
  Branch_merge nq b2 (Branch_merge nq b1 b).
Proof.
  assert (Hc: forall (c1 c2 c3: Complex),
  c2 <> 0 ->
  ((c1 / c2) * (c2 / c3) = c1 / c3)%com).
  {
    intros a b c Hb.
    unfold com_div.
    rewrite <- com_mul_assoc.
    rewrite (com_mul_assoc _ b _).
    rewrite com_inv_mult.
    rewrite com_mul_1_l.
    reflexivity.
    apply Hb.
  }
  intros [p1 q1] [p2 q2] [p q] [_ Hb] [_ Hb1] [_ Hb2].
  unfold Branch_merge, Branch_valid in *. simpl in *.
  f_equal.
  - repeat rewrite mat_scale_dist_l.
    repeat rewrite <- mat_scale_scale_comm.
    repeat rewrite mat_add_assoc.
    replace (RTC (q + q1)%R) with (q + q1)%com by lca.
    replace (RTC (q2 + q1)%R) with (q2 + q1)%com by lca.
    f_equal.
    + rewrite mat_add_comm.
      f_equal; f_equal;
      rewrite com_mul_comm, Hc.
      f_equal. lca.
      apply com_proj_neq_fst. simpl. lra.
      f_equal. lca.
      apply com_proj_neq_fst. simpl. lra.
    + f_equal.
      rewrite com_mul_comm, Hc.
      rewrite com_mul_comm, Hc.
      f_equal. lca.
      apply com_proj_neq_fst. simpl. lra.
      apply com_proj_neq_fst. simpl. lra.
  - lra.
Qed.

Lemma ProgramState_merge_step_commute:
  forall (ps: ProgramState nq) (k1 k2: positive) (b1 b2: Branch nq),
  Branch_valid nq b1 ->
  Branch_valid nq b2 ->
  ProgramState_valid nq ps ->
  ProgramState_equiv
  (merge_step nq k1 b1 (merge_step nq k2 b2 ps))
  (merge_step nq k2 b2 (merge_step nq k1 b1 ps)).
Proof.
  intros ps k1 k2 b1 b2 Hb1 Hb2 Hps cstate.
  unfold ProgramState_valid in Hps.
  destruct (Pos.eq_dec k1 k2) as [Hk|Hk]; subst.
  - destruct (Pos.eq_dec k2 cstate) as [Hc|Hc]; subst.
    + repeat rewrite find_merge_step_eq.
      destruct (PositiveMap.find cstate ps) eqn:Hfind; f_equal.
      apply Branch_merge_perm; try assumption.
      apply Hps with cstate.
      rewrite PFacts.find_mapsto_iff. apply Hfind.
      apply Branch_merge_commute.
    + repeat rewrite find_merge_step_neq.
      reflexivity.
      all: assumption.
  - destruct (Pos.eq_dec k1 cstate) as [Hc1|Hc1];
    destruct (Pos.eq_dec k2 cstate) as [Hc2|Hc2]; subst.
    + lia.
    + rewrite find_merge_step_eq, find_merge_step_neq.
      rewrite find_merge_step_neq, find_merge_step_eq.
      destruct (PositiveMap.find cstate ps); reflexivity.
      all: assumption.
    + rewrite find_merge_step_neq, find_merge_step_eq.
      rewrite find_merge_step_eq, find_merge_step_neq.
      destruct (PositiveMap.find cstate ps); reflexivity.
      all: assumption.
    + repeat rewrite find_merge_step_neq.
      reflexivity.
      all: assumption.
Qed.

Lemma ProgramState_merge_empty_r:
  forall ps: ProgramState nq,
  ProgramState_equiv ps (ProgramState_merge nq ps (PositiveMap.empty (Branch nq))).
Proof.
  intros ps.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_bis.
  - intros m m' a Heq H.
    rewrite <- Heq.
    apply H.
  - reflexivity.
  - intros k b a m Hmapsto Hnotin Heq.
    unfold merge_step.
    rewrite <- Heq.
    apply PFacts.not_find_in_iff in Hnotin.
    rewrite Hnotin.
    apply PositiveMap_add_Proper.
    apply Heq.
Qed.

Lemma ProgramState_valid_equal:
  forall ps1 ps2: ProgramState nq,
  ProgramState_valid nq ps1 ->
  ProgramState_equiv ps1 ps2 ->
  ProgramState_valid nq ps2.
Proof.
  intros ps1 ps2 Hvalid Heq.
  unfold ProgramState_valid in *.
  intros cstate branch Hmapsto.
  rewrite <- Heq in Hmapsto.
  apply Hvalid with cstate.
  apply Hmapsto.
Qed.

Lemma ProgramState_valid_add:
  forall (ps: ProgramState nq) (k: positive) (b: Branch nq),
  (~ PositiveMap.In k ps) ->
  ProgramState_valid nq (PositiveMap.add k b ps) ->
  ProgramState_valid nq ps /\ Branch_valid nq b.
Proof.
  intros ps k b Hnotin Hvalid.
  split.
  - intros cstate branch Hmapsto.
    apply Hvalid with cstate.
    rewrite PFacts.find_mapsto_iff.
    rewrite PFacts.add_o.
Admitted.

Lemma ProgramState_merge_add_r:
  forall (ps m: ProgramState nq) (k: positive) (b: Branch nq),
  Branch_valid nq b ->
  ProgramState_valid nq ps ->
  ~ PositiveMap.In k m ->
  ProgramState_equiv
    (merge_step nq k b (ProgramState_merge nq ps m))
    (ProgramState_merge nq ps (PositiveMap.add k b m)).
Proof.
  intros ps m k b Hbv Hps Hnotin.
  revert Hps.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_bis.
  - intros m0 m1 a Heq H Hps.
    rewrite H.
    apply ProgramState_merge_Proper.
    apply Heq.
    reflexivity.
    apply ProgramState_valid_equal with (ps1 := m1).
    apply Hps.
    rewrite Heq. reflexivity.
  - rewrite PProperties.fold_Empty.
    apply PFacts.not_find_in_iff in Hnotin.
    unfold merge_step.
    rewrite Hnotin.
    reflexivity.
    apply ProgramState_equiv_equivalence.
    apply PositiveMap.empty_1.
  - intros k' b' a m' Hmapsto Hnotin' IH Hps.
    assert (ProgramState_valid nq m' /\ Branch_valid nq b').
    {
      apply ProgramState_valid_add with k'.
      apply Hnotin'.
      apply Hps.
    }
    destruct H as [Hm' Hb'].
    apply ProgramState_equiv_equivalence with (y := merge_step nq k' b' (merge_step nq k b a)).
    + rewrite ProgramState_merge_step_commute.
      reflexivity.
      apply Hbv.
      apply Hb'.
      all: shelve.
    + rewrite PProperties.fold_add.
      * apply ProgramState_merge_step_Proper.
        apply IH.
        apply Hm'.
      * apply ProgramState_equiv_equivalence.
      * intros k0 k1 Hk b0 b1 Hb.
        rewrite Hk, Hb.  
        apply ProgramState_merge_step_Proper.
      * intros k0 k1 b0 b1 a' Hk.
        rewrite ProgramState_merge_step_commute.
        reflexivity.
        all: shelve.
      * apply Hnotin'.
Admitted.

Lemma ProgramState_merge_symmetry:
  forall ps1 ps2: ProgramState nq,
  ProgramState_valid nq ps1 ->
  ProgramState_valid nq ps2 ->
  ProgramState_equiv (ProgramState_merge nq ps1 ps2) (ProgramState_merge nq ps2 ps1).
Proof.
  intros ps1 ps2.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_weak.
  - intros m m' a Heq H Hps1 Hps2.
    rewrite H.
    apply ProgramState_merge_Proper.
    reflexivity.
    apply Heq.
    apply ProgramState_valid_equal with (ps1 := m').
    apply Hps1.
    rewrite Heq. reflexivity.
    apply Hps2.
  - intros _ _. apply ProgramState_merge_empty_r.
  - intros k b a m Hnotin IH Hps1 Hps2 cstate.
    rewrite <- (ProgramState_merge_add_r ps2 m k b).
    apply ProgramState_merge_step_Proper.
    apply IH.
    intros cstate' branch' Hmapsto.
    apply Hps1 with cstate'.
    rewrite PFacts.find_mapsto_iff.
    shelve.
    apply Hps2.
    apply Hps1 with k.
    rewrite PFacts.find_mapsto_iff.
    rewrite PFacts.add_eq_o; try reflexivity.
    apply Hps2.
    apply Hnotin.
Admitted.

(* ============================================================================================== *)
(* Proof of equivalence ========================================================================= *)

Lemma ProgramState_equiv_Execute_suppl_seq:
  forall (instr1 instr2: Instruction) (ps: ProgramState nq),
  ProgramState_equiv
  (Execute_suppl nq qasm{ instr1; instr2 } ps)
  (Execute_suppl nq instr2 (Execute_suppl nq instr1 ps)).
Proof.
  intros instr1 instr2 ps.
  destruct instr1; destruct instr2; simpl.
  all: try (simpl; reflexivity).
  all: rewrite fold_left_app; reflexivity.
Qed.

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

Lemma Instruction_valid_equiv_implies_equiv:
  forall (instr1 instr2: Instruction),
  Instruction_valid_equiv instr1 instr2 -> Instruction_equiv instr1 instr2.
Proof.
  intros instr1 instr2 Hvalid_equiv ps Hinv.
  apply Hvalid_equiv.
  apply ProgramState_invariant_valid.
  apply Hinv.
Qed.

Lemma Instruction_equiv_implies_behavioral_equiv:
  forall (instr1 instr2: Instruction),
  Instruction_equiv instr1 instr2 -> Instruction_behavioral_equiv instr1 instr2.
Proof.
  intros instr1 instr2 Hequiv ps Hinv.
  apply ProgramState_equiv_implies_behavioral_equiv.
  apply Hequiv.
  apply Hinv.
Qed.

Lemma Instruction_valid_equiv_rewrite:
  forall (pre_instr post_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_valid_equiv instr1 instr2 ->
  Instruction_valid_equiv
  qasm{ pre_instr; instr1; post_instr }
  qasm{ pre_instr; instr2; post_instr }.
Proof.
  intros pre post instr1 instr2 Hequiv ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Execute_suppl_Proper.
  apply Hequiv.
  apply Execute_suppl_valid.
  apply Hvalid.
Qed.

Corollary Instruction_valid_equiv_rewrite_start:
  forall (post_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_valid_equiv instr1 instr2 ->
  Instruction_valid_equiv
  qasm{ instr1; post_instr }
  qasm{ instr2; post_instr }.
Proof.
  intros post instr1 instr2 Hequiv ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Execute_suppl_Proper.
  apply Hequiv.
  apply Hvalid.
Qed.

Corollary Instruction_valid_equiv_rewrite_end:
  forall (pre_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_valid_equiv instr1 instr2 ->
  Instruction_valid_equiv
  qasm{ pre_instr; instr1 }
  qasm{ pre_instr; instr2 }.
Proof.
  intros pre instr1 instr2 Hequiv ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Hequiv.
  apply Execute_suppl_valid.
  apply Hvalid.
Qed.

Lemma Instruction_equiv_rewrite:
  forall (pre_instr post_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_equiv instr1 instr2 ->
  Instruction_equiv
  qasm{ pre_instr; instr1; post_instr }
  qasm{ pre_instr; instr2; post_instr }.
Proof.
  intros pre post instr1 instr2 Hequiv ps Hinv.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Execute_suppl_Proper.
  apply Hequiv.
  apply Execute_suppl_valid_invariant.
  apply Hinv.
Qed.

Corollary Instruction_equiv_rewrite_start:
  forall (post_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_equiv instr1 instr2 ->
  Instruction_equiv
  qasm{ instr1; post_instr }
  qasm{ instr2; post_instr }.
Proof.
  intros post instr1 instr2 Hequiv ps Hinv.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Execute_suppl_Proper.
  apply Hequiv.
  apply Hinv.
Qed.

Corollary Instruction_equiv_rewrite_end:
  forall (pre_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_equiv instr1 instr2 ->
  Instruction_equiv
  qasm{ pre_instr; instr1 }
  qasm{ pre_instr; instr2 }.
Proof.
  intros pre instr1 instr2 Hequiv ps Hinv.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Hequiv.
  apply Execute_suppl_valid_invariant.
  apply Hinv.
Qed.

Lemma Instruction_valid_equiv_nop:
  forall (pre_instr post_instr: Instruction),
  Instruction_valid_equiv
  qasm{ pre_instr; nop; post_instr }
  qasm{ pre_instr; post_instr }.
Proof.
  intros pre post ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Execute_suppl_Proper.
  reflexivity.
Qed.

Corollary Instruction_valid_equiv_nop_start:
  forall (post_instr: Instruction),
  Instruction_valid_equiv
  qasm{ nop; post_instr }
  post_instr.
Proof.
  intros post ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  reflexivity.
Qed.

Corollary Instruction_valid_equiv_nop_end:
  forall (pre_instr: Instruction),
  Instruction_valid_equiv
  qasm{ pre_instr; nop }
  pre_instr.
Proof.
  intros pre ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  reflexivity.
Qed.

Corollary Instruction_equiv_nop:
  forall (pre_instr post_instr: Instruction),
  Instruction_equiv
  qasm{ pre_instr; nop; post_instr }
  qasm{ pre_instr; post_instr }.
Proof.
  intros pre post.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_nop.
Qed.

Corollary Instruction_equiv_nop_start:
  forall (post_instr: Instruction),
  Instruction_equiv
  qasm{ nop; post_instr }
  post_instr.
Proof.
  intros post.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_nop_start.
Qed.

Corollary Instruction_equiv_nop_end:
  forall (pre_instr: Instruction),
  Instruction_equiv
  qasm{ pre_instr; nop }
  pre_instr.
Proof.
  intros pre.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_nop_end.
Qed.

Lemma Instruction_valid_equiv_Seq_list_eq:
  forall (instr: Instruction) (il: list Instruction),
  Instruction_valid_equiv
  qasm{ seq[ instr :: il ] }
  qasm{ instr; seq[ il ] }.
Proof.
  intros instr il ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  reflexivity.
Qed.

Corollary Instruction_equiv_Seq_list_eq:
  forall (instr: Instruction) (il: list Instruction),
  Instruction_equiv
  qasm{ seq[ instr :: il ] }
  qasm{ instr; seq[ il ] }.
Proof.
  intros instr il.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_Seq_list_eq.
Qed.

Lemma Instruction_valid_equiv_Seq_list_list_eq:
  forall (il1 il2: list Instruction),
  Instruction_valid_equiv
  qasm{ seq[ il1 ++ il2 ] }
  qasm{ seq[ il1 ]; seq[ il2 ] }.
Proof.
  intros il1 il2 ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  cbn [Execute_suppl].
  rewrite List.fold_left_app.
  apply ProgramState_equiv_equivalence.
Qed.

Corollary Instruction_equiv_Seq_list_list_eq:
  forall (il1 il2: list Instruction),
  Instruction_equiv
  qasm{ seq[ il1 ++ il2 ] }
  qasm{ seq[ il1 ]; seq[ il2 ] }.
Proof.
  intros il1 il2.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_Seq_list_list_eq.
Qed.

Lemma Instruction_valid_equiv_Seq_singleton:
  forall (instr: Instruction),
  Instruction_valid_equiv
  qasm{ seq[ [instr] ] }
  qasm{ instr }.
Proof.
  intros instr ps.
  cbn [Execute_suppl].
  reflexivity.
Qed.

Corollary Instruction_equiv_Seq_singleton:
  forall (instr: Instruction),
  Instruction_equiv
  qasm{ seq[ [instr] ] }
  qasm{ instr }.
Proof.
  intros instr.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_Seq_singleton.
Qed.

Lemma Instruction_valid_equiv_assoc:
  forall (instr1 instr2 instr3: Instruction),
  Instruction_valid_equiv
  qasm{ instr1; instr2; instr3 }
  qasm{ (instr1; instr2); instr3 }.
Proof.
  intros instr1 instr2 instr3 ps Hvalid.
  repeat rewrite ProgramState_equiv_Execute_suppl_seq.
  apply Execute_suppl_Proper.
  rewrite ProgramState_equiv_Execute_suppl_seq.
  reflexivity.
Qed.

Corollary Instruction_equiv_assoc:
  forall (instr1 instr2 instr3: Instruction),
  Instruction_equiv
  qasm{ instr1; instr2; instr3 }
  qasm{ (instr1; instr2); instr3 }.
Proof.
  intros instr1 instr2 instr3.
  apply Instruction_valid_equiv_implies_equiv.
  apply Instruction_valid_equiv_assoc.
Qed.

End EQUIVALENCE.

Global Instance Instruction_valid_equiv_Equivalence (nq: nat):
  Equivalence (Instruction_valid_equiv nq).
Proof.
  apply Instruction_valid_equiv_equivalence.
Qed.

Global Instance qasm_seq_valid_equiv_Proper (nq : nat) :
  Proper (Instruction_valid_equiv nq ==> Instruction_valid_equiv nq ==> Instruction_valid_equiv nq) qasm_seq.
Proof.
  intros pre1 pre2 Hpre post1 post2 Hpost.
  apply Instruction_valid_equiv_equivalence with (y:= qasm{ pre2; post1 }).
  - apply Instruction_valid_equiv_rewrite_start. apply Hpre.
  - apply Instruction_valid_equiv_rewrite_end. apply Hpost.
Qed.

Global Instance Instruction_equiv_Equivalence (nq: nat):
  Equivalence (Instruction_equiv nq).
Proof.
  apply Instruction_equiv_equivalence.
Qed.

Global Instance qasm_seq_equiv_Proper (nq : nat) :
  Proper (Instruction_equiv nq ==> Instruction_equiv nq ==> Instruction_equiv nq) qasm_seq.
Proof.
  intros pre1 pre2 Hpre post1 post2 Hpost.
  apply Instruction_equiv_equivalence with (y:= qasm{ pre2; post1 }).
  - apply Instruction_equiv_rewrite_start. apply Hpre.
  - apply Instruction_equiv_rewrite_end. apply Hpost.
Qed.
