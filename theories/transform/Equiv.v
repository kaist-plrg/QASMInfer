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
  PositiveMap.Equal (PositiveMap.map (B_prob nq) ps1) (PositiveMap.map (B_prob nq) ps2).
  
Fixpoint Instr_max_index (instr: Instruction): nat :=
  match instr with
  | NopInstr                    => 0
  | RotateInstr _ _ _ target    => target
  | CnotInstr control target    => max control target
  | SwapInstr q1 q2             => max q1 q2
  | MeasureInstr qbit cbit      => qbit
  | SeqInstr il                 => List.fold_left (fun q instr => max q (Instr_max_index instr)) il 0
  | IfInstr cbit cond subinstr  => Instr_max_index subinstr
  | ResetInstr target           => target
  end.

Definition Instr_bounded (n_qbit: nat) (instr: Instruction) :=
  Instr_max_index instr < n_qbit.

(* For inductive hypothesis *)
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
  forall (nq1 nq2: nat),
  Instr_bounded nq1 instr1 -> Instr_bounded nq2 instr2 ->  
  Execute_and_calculate_prob nq1 nc instr1 =
  Execute_and_calculate_prob nq2 nc instr2.

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
    apply PFacts.Equal_ST.
  - intros ps1 ps2 H.
    apply PFacts.Equal_ST.
    apply H.
  - intros ps1 ps2 ps3 H1 H2.
    apply PFacts.Equal_trans with (m' := PositiveMap.map (B_prob nq) ps2).
    apply H1. apply H2.
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

Lemma Execute_and_calculate_prob_nq_irrel :
  forall instr, Instruction_result_equiv instr instr.
Proof.
  intros instr nq1 nq2.
  unfold Execute_and_calculate_prob.
Admitted.

Lemma Instruction_result_equiv_equivalence:
  Equivalence Instruction_result_equiv.
Proof.
  split.
  - intros instr.
    apply Execute_and_calculate_prob_nq_irrel.
  - intros instr1 instr2 H12 nq1 nq2 Hq1 Hq2.
    symmetry.
    apply H12; assumption.
  - intros instr1 instr2 instr3 H12 H23 nq1 nq3 Hvalid1 Hvalid3.
    set (nq2 := S (Instr_max_index instr2)).

    assert (Hvalid2 : Instr_max_index instr2 < nq2). {
      unfold nq2. lia.
    }

    transitivity (Execute_and_calculate_prob nq2 nc instr2).
    + apply H12; assumption.
    + apply H23; assumption.
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

Lemma ProgramState_fold_Proper
  (f : positive -> Branch nq -> ProgramState nq -> ProgramState nq):
  (forall k b, Proper (ProgramState_equiv ==> ProgramState_equiv) (f k b)) ->
  Proper (ProgramState_equiv ==> ProgramState_equiv ==> ProgramState_equiv)
        (PositiveMap.fold f).
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

Lemma ProgramState_add_Proper (k: positive) (b: Branch nq):
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
  - apply ProgramState_add_Proper. apply Heq.
  - apply ProgramState_add_Proper. apply Heq.
Qed.

Lemma ProgramState_merge_Proper:
  Proper (ProgramState_equiv ==> ProgramState_equiv ==> ProgramState_equiv) (ProgramState_merge nq).
Proof.
  intros ps1 ps2 Heq ps1' ps2' Heq'.
  unfold ProgramState_merge.
  apply ProgramState_fold_Proper; try assumption.
  apply ProgramState_merge_step_Proper.
Qed.

Lemma Execute_measure_instr_Proper (qbit cbit: nat):
  Proper (ProgramState_equiv ==> ProgramState_equiv) (Execute_measure_instr nq qbit cbit).
Proof.
  intros ps1 ps2 Heq cstate.
  unfold Execute_measure_instr.
  apply ProgramState_fold_Proper.
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
  - apply ProgramState_fold_Proper.
    + intros k b' ps1' ps2' Heq'.
      apply ProgramState_merge_Proper.
      * apply Heq'.
      * apply ProgramState_equiv_equivalence.
    + apply Heq.
    + apply ProgramState_equiv_equivalence.
  - apply Execute_reset_instr_Proper. assumption.
Qed.

(* Proving ProgramState_merge is symmetric *)

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

Lemma ProgramState_merge_step_neq_commute:
  forall (ps: ProgramState nq) (k1 k2: positive) (b1 b2: Branch nq),
  k1 <> k2 ->
  ProgramState_equiv
  (merge_step nq k1 b1 (merge_step nq k2 b2 ps))
  (merge_step nq k2 b2 (merge_step nq k1 b1 ps)).
Proof.
  intros ps k1 k2 b1 b2 Hneq cstate.
  destruct (Pos.eq_dec k1 cstate) as [Hc1|Hc1];
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

Lemma ProgramState_merge_step_transpose:
  forall (ps: ProgramState nq) (k1 k2: positive) (b1 b2: Branch nq),
  Branch_valid nq b1 ->
  Branch_valid nq b2 ->
  ProgramState_valid nq ps ->
  ProgramState_equiv
  (merge_step nq k1 b1 (merge_step nq k2 b2 ps))
  (merge_step nq k2 b2 (merge_step nq k1 b1 ps)).
Proof.
  intros ps k1 k2 b1 b2 Hb1 Hb2 Hvalid cstate.
  destruct (Pos.eq_dec k1 k2) as [Hk|Hk]; subst.
  - destruct (Pos.eq_dec k2 cstate) as [Hc|Hc]; subst.
    + repeat rewrite find_merge_step_eq.
      destruct (PositiveMap.find cstate ps) eqn:Hfind.
      * f_equal. apply Branch_merge_transpose.
        2-3: assumption.
        apply Hvalid with cstate.
        rewrite PFacts.find_mapsto_iff.
        apply Hfind.
      * f_equal. apply Branch_merge_commute.
    + repeat rewrite find_merge_step_neq.
      reflexivity.
      all: assumption.
  - apply ProgramState_merge_step_neq_commute.
    apply Hk.
Qed.

Corollary ProgramState_merge_step_transpose_neqkey:
  PProperties.transpose_neqkey ProgramState_equiv (merge_step nq).
Proof.
  intros k1 k2 b1 b2 Hneq ps cstate.
  apply ProgramState_merge_step_neq_commute.
  apply ps.
Qed.

Lemma ProgramState_merge_empty_l:
  forall ps: ProgramState nq,
  ProgramState_equiv ps (ProgramState_merge nq (PositiveMap.empty (Branch nq)) ps).
Proof.
  intros ps.
  unfold ProgramState_merge.
  rewrite PProperties.fold_Empty.
  reflexivity.
  apply ProgramState_equiv_equivalence.
  apply PositiveMap.empty_1.
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
    apply ProgramState_add_Proper.
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

Lemma ProgramState_valid_add_inj:
  forall k b m,
  (~ PositiveMap.In k m) ->
  ProgramState_valid nq (PositiveMap.add k b m) ->
  ProgramState_valid nq m.
Proof.
  intros k b m Hnotin Hvalid.
  intros cstate branch Hmapsto.
  apply Hvalid with cstate.
  rewrite PFacts.find_mapsto_iff in Hmapsto.
  rewrite PFacts.not_find_in_iff in Hnotin.
  rewrite PFacts.find_mapsto_iff.
  destruct (Pos.eq_dec cstate k) as [Heq|Hneq].
  - rewrite Heq, Hnotin in Hmapsto.
    discriminate Hmapsto.
  - rewrite PFacts.add_neq_o.
    apply Hmapsto.
    lia.
Qed.

Lemma ProgramState_merge_add_r:
  forall (ps m: ProgramState nq) (k: positive) (b: Branch nq),
  Branch_valid nq b ->
  ProgramState_valid nq ps ->
  ProgramState_valid nq m ->
  ~ PositiveMap.In k m ->
  ProgramState_equiv
    (merge_step nq k b (ProgramState_merge nq ps m))
    (ProgramState_merge nq ps (PositiveMap.add k b m)).
Proof.
  intros ps m k b Hbv Hps Hm Hnotin.
  apply proj2 with (A := ProgramState_valid nq (ProgramState_merge nq ps m)).
  revert Hps.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_bis.
  - intros m0 m1 a Heq H Hps.
    assert (Hm0: ProgramState_valid nq m0). {
      apply ProgramState_valid_equal with m1.
      apply Hps. rewrite Heq. reflexivity.
    }
    apply H in Hm0.
    destruct Hm0 as [H1 H2].
    split.
    apply H1.
    rewrite H2.
    apply ProgramState_merge_Proper.
    apply Heq.
    reflexivity.
  - intros _. split. apply Hm.
    rewrite PProperties.fold_Empty.
    apply PFacts.not_find_in_iff in Hnotin.
    unfold merge_step.
    rewrite Hnotin.
    reflexivity.
    apply ProgramState_equiv_equivalence.
    apply PositiveMap.empty_1.
  - intros k' b' a m' Hmapsto Hnotin' IH Hps.
    assert (Hm': ProgramState_valid nq m'). {
      apply ProgramState_valid_add_inj with k' b'.
      apply Hnotin'.
      apply Hps.
    }
    assert (Hb': Branch_valid nq b'). {
      apply Hps with k'.
      rewrite PFacts.find_mapsto_iff, PFacts.add_eq_o.
      all: reflexivity.
    }
    apply IH in Hm'.
    destruct Hm' as [Ha Heq].
    split.
    + apply ProgramState_merge_step_valid.
      apply Ha.
      apply Hb'.
    + rewrite PProperties.fold_add.
      * rewrite ProgramState_merge_step_transpose.
        apply ProgramState_merge_step_Proper.
        apply Heq.
        apply Hbv.
        apply Hb'.
        apply Ha.
      * apply ProgramState_equiv_equivalence.
      * intros k0 k1 Hk b0 b1 Hb.
        rewrite Hk, Hb.
        apply ProgramState_merge_step_Proper.
      * apply ProgramState_merge_step_transpose_neqkey.
      * apply Hnotin'.
Qed.

Lemma ProgramState_merge_commute:
  forall ps1 ps2: ProgramState nq,
  ProgramState_valid nq ps1 ->
  ProgramState_valid nq ps2 ->
  ProgramState_equiv (ProgramState_merge nq ps1 ps2) (ProgramState_merge nq ps2 ps1).
Proof.
  intros ps1 ps2 Hps1 Hps2.
  revert Hps1.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_bis.
  - intros m m' a Heq H Hps1.
    rewrite H.
    apply ProgramState_merge_Proper.
    reflexivity.
    apply Heq.
    apply ProgramState_valid_equal with m'.
    apply Hps1.
    rewrite Heq. reflexivity.
  - rewrite <- (ProgramState_merge_empty_r ps2).
    reflexivity.
  - intros k b a m Hmapsto Hnotin Heq Hps1.
    assert (Hm: ProgramState_valid nq m). {
      apply ProgramState_valid_add_inj with k b.
      apply Hnotin.
      apply Hps1.
    }
    rewrite <- (ProgramState_merge_add_r ps2 m k b).
    apply ProgramState_merge_step_Proper.
    apply Heq.
    apply Hm.
    apply Hps1 with k.
    rewrite PFacts.find_mapsto_iff, PFacts.add_eq_o; reflexivity.
    apply Hps2.
    apply Hm.
    apply Hnotin.
Qed.

Lemma ProgramState_merge_step_fold_transpose :
  forall ps acc k b,
    Branch_valid nq b ->
    ProgramState_valid nq ps ->
    ProgramState_valid nq acc ->
    ProgramState_equiv
      (merge_step nq k b (ProgramState_merge nq ps acc))
      (ProgramState_merge nq ps (merge_step nq k b acc)).
Proof.
  intros ps acc k b Hb Hps Hacc.

  assert
    (ProgramState_valid nq (ProgramState_merge nq ps acc) /\
     ProgramState_valid nq (ProgramState_merge nq ps (merge_step nq k b acc)) /\
     ProgramState_equiv
       (merge_step nq k b (ProgramState_merge nq ps acc))
       (ProgramState_merge nq ps (merge_step nq k b acc))) as HR.
  - unfold ProgramState_merge.
    apply PProperties.fold_rel with
      (R := fun a c =>
        ProgramState_valid nq a /\
        ProgramState_valid nq c /\
        ProgramState_equiv (merge_step nq k b a) c).
    + constructor.
      * apply Hacc.
      * constructor.
        -- apply ProgramState_merge_step_valid.
           apply Hacc. apply Hb.
        -- reflexivity.
    + intros k' b' a c Hmapsto HR'.
      destruct HR' as [Ha [Hc Heq]].

      assert (Hb' : Branch_valid nq b').
      * apply Hps with (cstate:=k') (branch:=b').
        apply Hmapsto.
      * constructor.
        -- apply ProgramState_merge_step_valid.
           apply Ha. apply Hb'.
        -- constructor.
           ++ apply ProgramState_merge_step_valid.
              apply Hc. apply Hb'.
           ++ apply ProgramState_equiv_equivalence with
                (y := merge_step nq k' b' (merge_step nq k b a)).
              ** apply ProgramState_merge_step_transpose.
                 apply Hb. apply Hb'. apply Ha.
              ** apply ProgramState_merge_step_Proper.
                 apply Heq.
  - destruct HR as [Hvl [Hvr Heq]].
    apply Heq.
Qed.

Lemma ProgramState_merge_transpose :
  forall ps1 ps2 acc,
    ProgramState_valid nq ps1 ->
    ProgramState_valid nq ps2 ->
    ProgramState_valid nq acc ->
    ProgramState_equiv
      (ProgramState_merge nq ps1 (ProgramState_merge nq ps2 acc))
      (ProgramState_merge nq ps2 (ProgramState_merge nq ps1 acc)).
Proof.
  intros ps1 ps2 acc Hps1 Hps2 Hacc.

  assert
    (ProgramState_valid nq
       (ProgramState_merge nq ps1 (ProgramState_merge nq ps2 acc)) /\
     ProgramState_valid nq
       (ProgramState_merge nq ps1 acc) /\
     ProgramState_equiv
       (ProgramState_merge nq ps1 (ProgramState_merge nq ps2 acc))
       (ProgramState_merge nq ps2 (ProgramState_merge nq ps1 acc))) as HR.
  - unfold ProgramState_merge.
    apply PProperties.fold_rel with
      (R := fun a c =>
        ProgramState_valid nq a /\
        ProgramState_valid nq c /\
        ProgramState_equiv a (ProgramState_merge nq ps2 c)).

    + constructor.
      * apply ProgramState_merge_valid.
        apply Hps2. apply Hacc.
      * constructor.
        apply Hacc. reflexivity.

    + intros k b a c Hmapsto HR'.
      destruct HR' as [Ha [Hc Heq]].

      assert (Hb : Branch_valid nq b).
      * apply Hps1 with (cstate:=k) (branch:=b).
        apply Hmapsto.

      * constructor.
        -- apply ProgramState_merge_step_valid.
           apply Ha. apply Hb.
        -- constructor.
           ++ apply ProgramState_merge_step_valid.
              apply Hc. apply Hb.
           ++ apply ProgramState_equiv_equivalence with
                (y := merge_step nq k b (ProgramState_merge nq ps2 c)).
              ** apply ProgramState_merge_step_Proper.
                 apply Heq.
              ** apply ProgramState_merge_step_fold_transpose.
                 apply Hb. apply Hps2. apply Hc.

  - destruct HR as [Hvl [Hvr Heq]].
    apply Heq.
Qed.

Corollary ProgramState_merge_transpose_left :
  forall ps1 ps2 acc,
    ProgramState_valid nq ps1 ->
    ProgramState_valid nq ps2 ->
    ProgramState_valid nq acc ->
    ProgramState_equiv
      (ProgramState_merge nq (ProgramState_merge nq acc ps1) ps2)
      (ProgramState_merge nq (ProgramState_merge nq acc ps2) ps1).
Proof.
  intros ps1 ps2 acc Hps1 Hps2 Hacc. intros y.
  rewrite ProgramState_merge_commute with (ps2:=ps1).
  rewrite ProgramState_merge_commute with (ps2:=ps2).
  transitivity (PositiveMap.find y (ProgramState_merge nq ps2 (ProgramState_merge nq ps1 acc))).
  apply ProgramState_merge_Proper. reflexivity. apply ProgramState_merge_commute.
  3: rewrite ProgramState_merge_transpose.
  3: apply ProgramState_merge_Proper; try reflexivity.
  3: apply ProgramState_merge_commute.
  all: try apply ProgramState_merge_valid.
  all: assumption.
Qed.

Lemma Branch_merge_Execute_swap_instr_branch:
  forall q1 q2 b1 b2,
  Branch_merge nq (Execute_swap_instr_branch nq q1 q2 b1)
                  (Execute_swap_instr_branch nq q1 q2 b2) =
  Execute_swap_instr_branch nq q1 q2 (Branch_merge nq b1 b2).
Proof.
  intros q1 q2 [Q1 p1] [Q2 p2].
  unfold Execute_swap_instr_branch, Branch_merge.
  simpl. f_equal.
  rewrite <- den_uop_scale, <- den_uop_scale.
  rewrite den_uop_add.
  reflexivity.
Qed.

Lemma Execute_swap_instr_merge :
  forall q1 q2 ps0 ps1,
  ProgramState_equiv
    (ProgramState_merge nq (Execute_swap_instr nq q1 q2 ps0)
                           (Execute_swap_instr nq q1 q2 ps1))
    (Execute_swap_instr nq q1 q2 (ProgramState_merge nq ps0 ps1)).
Proof.
  intros q1 q2 ps0 ps1.
  unfold ProgramState_merge, Execute_swap_instr.
  rewrite PositiveMap_fold_map.
  apply PProperties.fold_rec_bis.
  - intros m0 m1 a Heq H.
    rewrite H.
    apply Execute_swap_instr_Proper.
    apply ProgramState_merge_Proper.
    apply Heq. reflexivity.
  - apply Execute_swap_instr_Proper.
    rewrite PProperties.fold_Empty.
    reflexivity.
    apply ProgramState_equiv_equivalence.
    apply PositiveMap.empty_1.
  - intros k b a m Hmapsto Hnotin Heq.
    apply ProgramState_equiv_equivalence with (y :=
      merge_step nq k (Execute_swap_instr_branch nq q1 q2 b)
      (PositiveMap.map (Execute_swap_instr_branch nq q1 q2)
        (PositiveMap.fold (merge_step nq) m ps1))).
    + apply ProgramState_merge_step_Proper.
      apply Heq.
    + rewrite PProperties.fold_add.
      * remember (PositiveMap.fold (merge_step nq) m ps1) as ps.
        intros cstate.
        unfold merge_step.
        repeat rewrite PositiveMap_find_map.
        destruct (PositiveMap.find k ps) eqn:Hfind; simpl.
        {
          destruct (Pos.eq_dec k cstate).
          - rewrite PFacts.add_eq_o, PFacts.add_eq_o; try assumption.
            simpl. f_equal.
            apply Branch_merge_Execute_swap_instr_branch.
          - rewrite PFacts.add_neq_o, PFacts.add_neq_o; try assumption.
            rewrite PositiveMap_find_map.
            reflexivity.
        }
        {
          destruct (Pos.eq_dec k cstate).
          - rewrite PFacts.add_eq_o, PFacts.add_eq_o; try assumption.
            simpl. reflexivity.
          - rewrite PFacts.add_neq_o, PFacts.add_neq_o; try assumption.
            rewrite PositiveMap_find_map.
            reflexivity.
        }
      * apply ProgramState_equiv_equivalence.
      * intros k1 k2 Hk b1 b2 Hb.
        rewrite Hk, Hb.
        apply ProgramState_merge_step_Proper.
      * apply ProgramState_merge_step_transpose_neqkey.
      * apply Hnotin.
Qed.

(* swap map - merge equality *)
Lemma Execute_swap_instr_branch_merge :
  forall b1 b2 qbit1 qbit2,
    Branch_valid nq b1 ->
    Branch_valid nq b2 ->
    Execute_swap_instr_branch nq qbit1 qbit2
      (Branch_merge nq b1 b2)
    =
    Branch_merge nq
      (Execute_swap_instr_branch nq qbit1 qbit2 b1)
      (Execute_swap_instr_branch nq qbit1 qbit2 b2).
Proof.
  intros b1 b2 qbit1 qbit2 Hb1 Hb2.
  destruct b1; destruct b2.
  unfold Branch_merge, Execute_swap_instr_branch; simpl.
  f_equal.
  rewrite <- den_uop_scale, <- den_uop_scale, <- den_uop_add.
  reflexivity.
Qed.

Lemma Execute_swap_instr_map_merge :
  forall ps1 ps2 qbit1 qbit2,
    ProgramState_valid nq ps1 ->
    ProgramState_valid nq ps2 ->
    ProgramState_equiv
      (PositiveMap.map
        (Execute_swap_instr_branch nq qbit1 qbit2)
        (ProgramState_merge nq ps1 ps2))
      (ProgramState_merge nq
        (PositiveMap.map
          (Execute_swap_instr_branch nq qbit1 qbit2)
          ps1)
        (PositiveMap.map
          (Execute_swap_instr_branch nq qbit1 qbit2)
          ps2)).
Proof.
  intros ps1 ps2 qbit1 qbit2 Hps1 Hps2 cstate.

  rewrite PFacts.map_o.
  repeat rewrite ProgramState_merge_o.
  repeat rewrite PFacts.map_o.

  destruct (PositiveMap.find cstate ps1) as [b1 |] eqn:E1;
  destruct (PositiveMap.find cstate ps2) as [b2 |] eqn:E2;
  simpl; try reflexivity.

  assert (Hb1 : Branch_valid nq b1).
  {
    eapply Hps1.
    apply PositiveMap.find_2.
    exact E1.
  }

  assert (Hb2 : Branch_valid nq b2).
  {
    eapply Hps2.
    apply PositiveMap.find_2.
    exact E2.
  }

  rewrite Execute_swap_instr_branch_merge by assumption.
  reflexivity.
Qed.

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
  rewrite PFacts.map_o, PFacts.map_o.
  f_equal.
  apply Heq.
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

Lemma Instruction_behavioral_equiv_implies_result_equiv:
  forall (instr1 instr2: Instruction),
  Instruction_behavioral_equiv instr1 instr2 -> Instruction_result_equiv instr1 instr2.
Proof.
  intros instr1 instr2 Hequiv.
  intros nq1 nq2 Hq1 Hq2.
  unfold Instruction_behavioral_equiv, ProgramState_behavioral_equiv in Hequiv.

  unfold Execute_and_calculate_prob, Execute.
Admitted.

Lemma Execute_suppl_seq:
  forall (ps: ProgramState nq) (instr1 instr2: Instruction),
  ProgramState_equiv
  (Execute_suppl nq qasm{ instr1; instr2 } ps)
  (Execute_suppl nq instr2 (Execute_suppl nq instr1 ps)).
Proof.
  intros ps instr1 instr2 cstate.
  unfold qasm_seq.
  destruct instr1; destruct instr2; simpl.
  all: try reflexivity.
  all: rewrite fold_left_app.
  all: try reflexivity.
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

Lemma Instruction_behavioral_equiv_rewrite_end:
  forall (pre_instr: Instruction) (instr1 instr2: Instruction),
  Instruction_behavioral_equiv instr1 instr2 ->
  Instruction_behavioral_equiv
  qasm{ pre_instr; instr1 }
  qasm{ pre_instr; instr2 }.
Proof.
  intros pre instr1 instr2 Hequiv ps Hinv.
  apply ProgramState_behavioral_equiv_equivalence
  with (y := Execute_suppl nq instr1 (Execute_suppl nq pre ps)).
  - apply ProgramState_equiv_implies_behavioral_equiv.
    apply Execute_suppl_seq.
  - apply ProgramState_behavioral_equiv_equivalence
    with (y := Execute_suppl nq instr2 (Execute_suppl nq pre ps)).
    + apply Hequiv.
      apply Execute_suppl_valid_invariant.
      apply Hinv.
    + apply ProgramState_behavioral_equiv_equivalence.
      apply ProgramState_equiv_implies_behavioral_equiv.
      apply Execute_suppl_seq.
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
