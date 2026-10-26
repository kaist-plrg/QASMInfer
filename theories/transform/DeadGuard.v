Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Valid.
Require Import QASMInfer.transform.Transform.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.
Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.
Import ListNotations.
Open Scope nat_scope.

(* A conservative, recursive write check: even a guarded measurement counts. *)
Fixpoint Instruction_no_write (bit : nat) (instr : Instruction) : bool :=
  match instr with
  | MeasureInstr _ target => negb (Nat.eqb bit target)
  | SeqInstr instrs => forallb (Instruction_no_write bit) instrs
  | IfInstr _ _ body => Instruction_no_write bit body
  | _ => true
  end.

(* Empty-LHS sites use the existing deep preorder: before each list head,
   then inside its sequence/conditional, then the remaining list. There is
   no site at the end of an empty list. Rejected sites retain their ordinal. *)
Fixpoint Dead_guard_site_count (instr : Instruction) : nat :=
  match instr with
  | SeqInstr instrs =>
      let fix count_list xs :=
        match xs with
        | [] => 0
        | head :: tail =>
            S ((match head with
                | SeqInstr _ => Dead_guard_site_count head
                | IfInstr _ _ body => Dead_guard_site_count body
                | _ => 0
                end) + count_list tail)
        end in count_list instrs
  | IfInstr _ _ body => S (Dead_guard_site_count body)
  | _ => 1
  end.

Definition Dead_guard_child_count (instr : Instruction) : nat :=
  match instr with
  | SeqInstr _ => Dead_guard_site_count instr
  | IfInstr _ _ body => Dead_guard_site_count body
  | _ => 0
  end.

Fixpoint Dead_guard_apply_list (bit : nat) (body : Instruction)
    (rewrite : Instruction -> nat -> option Instruction)
    (instrs : list Instruction) (occurrence : nat) : option (list Instruction) :=
  match instrs with
  | [] => None
  | head :: tail =>
      match occurrence with
      | O => Some (IfInstr bit true body :: instrs)
      | S next =>
          if next <? Dead_guard_child_count head then
            let child_index := match head with SeqInstr _ => next | _ => S next end in
            Datatypes.option_map (fun head' => head' :: tail) (rewrite head child_index)
          else if Instruction_no_write bit head then
            Datatypes.option_map (cons head)
              (Dead_guard_apply_list bit body rewrite tail
                (next - Dead_guard_child_count head))
          else None
      end
  end.

Fixpoint Dead_guard_apply (bit : nat) (body instr : Instruction)
    (occurrence : nat) : option Instruction :=
  match instr with
  | SeqInstr instrs =>
      Datatypes.option_map SeqInstr
        (Dead_guard_apply_list bit body (Dead_guard_apply bit body) instrs occurrence)
  | IfInstr c cond inner =>
      match occurrence with
      | O => Some (SeqInstr [IfInstr bit true body; instr])
      | S next => Datatypes.option_map (IfInstr c cond) (Dead_guard_apply bit body inner next)
      end
  | _ =>
      match occurrence with
      | O => Some (SeqInstr [IfInstr bit true body; instr])
      | S _ => None
      end
  end.

Lemma CState_read_init : forall nc bit,
  CState_read bit (CState_init nc) = false.
Proof.
  unfold CState_init.
  induction nc; intros bit; destruct bit; simpl; auto.
Qed.

Lemma CState_read_empty : forall bit, CState_read bit 1%positive = false.
Proof. intros []; reflexivity. Qed.

Lemma CState_branch_other : forall target bit cs,
  bit <> target ->
  CState_read bit (fst (CState_branch target cs)) = CState_read bit cs /\
  CState_read bit (snd (CState_branch target cs)) = CState_read bit cs.
Proof.
  induction target; intros bit cs Hneq.
  - destruct bit; [contradiction |].
    destruct cs; simpl; try rewrite CState_read_empty; split; reflexivity.
  - destruct bit.
    + destruct cs; simpl;
        destruct (CState_branch target _) as [c0 c1]; split; reflexivity.
    + destruct cs; simpl;
        match goal with
        | |- context[CState_branch target ?c] =>
            pose proof (IHtarget bit c ltac:(lia)) as Hother
        end;
        destruct (CState_branch target _) as [c0 c1]; simpl in *;
        try rewrite CState_read_empty in *; exact Hother.
Qed.

Section DEAD_GUARD.
Variable nq : nat.

Definition ProgramState_bit_zero (bit : nat) (ps : ProgramState nq) : Prop :=
  forall cs b, PositiveMap.MapsTo cs b ps -> CState_read bit cs = false.

Lemma bit_zero_empty : forall bit,
  ProgramState_bit_zero bit (PositiveMap.empty (Branch nq)).
Proof.
  intros bit cs b H; apply PFacts.empty_mapsto_iff in H; contradiction.
Qed.

Lemma bit_zero_add : forall bit cs b ps,
  CState_read bit cs = false -> ProgramState_bit_zero bit ps ->
  ProgramState_bit_zero bit (PositiveMap.add cs b ps).
Proof.
  intros bit cs b ps Hcs Hps k v H.
  apply PFacts.add_mapsto_iff in H.
  destruct H as [[<- _] | [_ H]]; eauto.
Qed.

Lemma bit_zero_map : forall bit f ps,
  ProgramState_bit_zero bit ps ->
  ProgramState_bit_zero bit (PositiveMap.map f ps).
Proof.
  intros bit f ps Hps cs b H.
  apply PFacts.map_mapsto_iff in H.
  destruct H as [v [_ H]]; eauto.
Qed.

Lemma bit_zero_merge : forall bit ps1 ps2,
  ProgramState_bit_zero bit ps1 -> ProgramState_bit_zero bit ps2 ->
  ProgramState_bit_zero bit (ProgramState_merge nq ps1 ps2).
Proof.
  intros bit ps1 ps2 H1 H2 cs b H.
  change (PositiveMap.find cs (ProgramState_merge nq ps1 ps2) = Some b) in H.
  rewrite ProgramState_merge_o in H.
  destruct (PositiveMap.find cs ps1) eqn:E1;
    destruct (PositiveMap.find cs ps2) eqn:E2; try discriminate;
    eauto using PFacts.find_mapsto_iff.
Qed.

Lemma bit_zero_measure : forall bit q target ps,
  bit <> target -> ProgramState_bit_zero bit ps ->
  ProgramState_bit_zero bit (Execute_measure_instr nq q target ps).
Proof.
  intros bit q target ps Hneq Hps.
  unfold Execute_measure_instr.
  apply PProperties.fold_rec_nodep.
  - apply bit_zero_empty.
  - intros cs b acc Hmaps Hacc.
    apply bit_zero_merge; [exact Hacc |].
    pose proof (Hps cs b Hmaps) as Hzero.
    pose proof (CState_branch_other target bit cs Hneq) as Hother.
    unfold Execute_measure_instr_branch.
    destruct (CState_branch target cs) as [c0 c1]; simpl in Hother.
    destruct Hother as [H0 H1].
    destruct (Rgt_dec _ _), (Rgt_dec _ _);
      repeat apply bit_zero_add; try congruence; apply bit_zero_empty.
Qed.

Lemma Execute_no_write_bit_zero : forall instr bit ps,
  Instruction_no_write bit instr = true -> ProgramState_bit_zero bit ps ->
  ProgramState_bit_zero bit (Execute_suppl nq instr ps).
Proof.
  induction instr using Instruction_ind'; intros bit ps Hfree Hzero;
    cbn [Execute_suppl] in *.
  - exact Hzero.
  - apply bit_zero_map; exact Hzero.
  - apply bit_zero_map; exact Hzero.
  - apply bit_zero_map; exact Hzero.
  - apply bit_zero_measure; [|exact Hzero].
    apply Bool.negb_true_iff, Nat.eqb_neq in Hfree; exact Hfree.
  - cbn [Instruction_no_write] in Hfree.
    revert ps Hfree Hzero.
    induction H; intros ps Hfree Hzero; simpl in *; auto.
    apply andb_true_iff in Hfree as [Hx Hxs].
    apply IHForall; auto.
  - apply PProperties.fold_rec_nodep; [apply bit_zero_empty |].
    intros cs b acc Hmaps Hacc.
    apply bit_zero_merge; [exact Hacc |].
    destruct (Bool.eqb (CState_read cbit cs) cond).
    + apply IHinstr; [exact Hfree |].
      apply bit_zero_add; [eauto | apply bit_zero_empty].
    + apply bit_zero_add; [eauto | apply bit_zero_empty].
  - apply bit_zero_map; exact Hzero.
  (* Named qelib1 gates transform branch values without changing classical keys. *)
  - apply bit_zero_map; exact Hzero. (* CzInstr *)
  - apply bit_zero_map; exact Hzero. (* CyInstr *)
  - apply bit_zero_map; exact Hzero. (* ChInstr *)
  - apply bit_zero_map; exact Hzero. (* CsxInstr *)
  - apply bit_zero_map; exact Hzero. (* ToffoliInstr *)
  - apply bit_zero_map; exact Hzero. (* CswapInstr *)
  - apply bit_zero_map; exact Hzero. (* RccxInstr *)
Qed.

Lemma Execute_dead_if_zero : forall bit body ps,
  ProgramState_valid nq ps -> ProgramState_bit_zero bit ps ->
  ProgramState_equiv nq (Execute_suppl nq (IfInstr bit true body) ps) ps.
Proof.
  intros bit body ps Hvalid Hzero.
  cbn [Execute_suppl].
  enough (H : ProgramState_valid nq ps /\
    ProgramState_equiv nq
      (PositiveMap.fold
        (fold_step nq (fun cs b =>
          if Bool.eqb (CState_read bit cs) true
          then Execute_suppl nq body (PositiveMap.add cs b (PositiveMap.empty _))
          else PositiveMap.add cs b (PositiveMap.empty _)))
        ps (PositiveMap.empty _)) ps) by apply H.
  apply (PProperties.fold_rec_bis
    (P := fun m a => ProgramState_valid nq m /\ ProgramState_equiv nq a m)).
  - intros m m' a Heq [Hv Ha]; split.
    + eapply ProgramState_valid_equal; eassumption.
    + etransitivity; eassumption.
  - split; [apply ProgramState_empty_valid | reflexivity].
  - intros cs b a m Hmaps Hnotin [Hv Ha].
    assert (Hb : Branch_valid nq b) by (apply Hvalid with cs; assumption).
    split; [apply ProgramState_add_valid; assumption |].
    unfold fold_step.
    rewrite (Hzero cs b Hmaps); simpl.
    etransitivity.
    + apply ProgramState_merge_Proper; [exact Ha | reflexivity].
    + symmetry; apply ProgramState_merge_singleton_add; assumption.
Qed.

Definition Instruction_equiv_zero (bit : nat) (left right : Instruction) : Prop :=
  forall ps, ProgramState_valid nq ps -> ProgramState_bit_zero bit ps ->
    ProgramState_equiv nq (Execute_suppl nq left ps) (Execute_suppl nq right ps).

Lemma bit_zero_equal : forall bit ps1 ps2,
  ProgramState_equiv nq ps1 ps2 ->
  ProgramState_bit_zero bit ps1 -> ProgramState_bit_zero bit ps2.
Proof.
  intros bit ps1 ps2 Heq Hzero cs b Hmaps.
  apply Hzero with b.
  change (PositiveMap.find cs ps1 = Some b).
  rewrite Heq; exact Hmaps.
Qed.

Lemma bit_zero_add_inv : forall bit cs b ps,
  ~ PositiveMap.In cs ps ->
  ProgramState_bit_zero bit (PositiveMap.add cs b ps) ->
  ProgramState_bit_zero bit ps.
Proof.
  intros bit cs b ps Hnotin Hzero k v Hmaps.
  apply Hzero with v, PFacts.add_mapsto_iff; right; split; [|exact Hmaps].
  intro E; subst; apply Hnotin; exists v; exact Hmaps.
Qed.

Lemma Instruction_if_zero_congr : forall bit c cond left right,
  Instruction_equiv_zero bit left right ->
  Instruction_equiv_zero bit (IfInstr c cond left) (IfInstr c cond right).
Proof.
  intros bit c cond left right Hbody ps.
  apply ProgramState_ind with (m := ps).
  - intros m0 m1 Heq IH Hv Hz.
    etransitivity; [apply Execute_suppl_Proper; symmetry; exact Heq |].
    etransitivity; [apply IH | apply Execute_suppl_Proper; exact Heq].
    + eapply ProgramState_valid_equal; [exact Hv | symmetry; exact Heq].
    + eapply bit_zero_equal; [symmetry; exact Heq | exact Hz].
  - intros; reflexivity.
  - intros cs b m Hnotin IH Hv Hz.
    assert (Hb : Branch_valid nq b).
    { apply Hv with cs; apply PFacts.add_mapsto_iff; left; auto. }
    assert (Hm : ProgramState_valid nq m).
    { eapply ProgramState_valid_add_inj; eassumption. }
    assert (Hcs : CState_read bit cs = false).
    { apply Hz with b; apply PFacts.add_mapsto_iff; left; auto. }
    cbn [Execute_suppl].
    rewrite ProgramState_fold_stepF_add.
    rewrite ProgramState_fold_stepF_add.
    unfold fold_step at 1 3.
    apply ProgramState_merge_Proper.
    all: try apply Execute_if_instr_branch_valid.
    all: try assumption.
    all: try apply ProgramState_empty_valid.
    + apply IH; [exact Hm | eapply bit_zero_add_inv; eassumption].
    + destruct (Bool.eqb (CState_read c cs) cond); [|reflexivity].
      apply Hbody; [apply ProgramState_singleton_valid; exact Hb |].
      apply bit_zero_add; [exact Hcs | apply bit_zero_empty].
Qed.

Lemma Dead_guard_apply_list_sound : forall bit body rewrite instrs,
  Forall (fun instr => forall index result,
    rewrite instr index = Some result -> Instruction_equiv_zero bit result instr) instrs ->
  forall index result,
  Dead_guard_apply_list bit body rewrite instrs index = Some result ->
  Instruction_equiv_zero bit (SeqInstr result) (SeqInstr instrs).
Proof.
  intros bit body rewrite instrs H.
  induction H as [|head tail Hhead Htail IH]; intros index result Happ;
    destruct index; cbn [Dead_guard_apply_list] in Happ; try discriminate.
  - injection Happ as <-; intros ps Hv Hz; cbn [Execute_suppl].
    change (ProgramState_equiv nq
      (Execute_suppl nq (SeqInstr (head :: tail)) (Execute_suppl nq (IfInstr bit true body) ps))
      (Execute_suppl nq (SeqInstr (head :: tail)) ps)).
    apply Execute_suppl_Proper, Execute_dead_if_zero; assumption.
  - destruct (index <? Dead_guard_child_count head).
    + destruct (rewrite head _) as [head'|] eqn:E; try discriminate.
      injection Happ as <-; intros ps Hv Hz; cbn [Execute_suppl].
      change (ProgramState_equiv nq
        (Execute_suppl nq (SeqInstr tail) (Execute_suppl nq head' ps))
        (Execute_suppl nq (SeqInstr tail) (Execute_suppl nq head ps))).
      apply Execute_suppl_Proper; eapply Hhead; eassumption.
    + destruct (Instruction_no_write bit head) eqn:Hfree; try discriminate.
      destruct (Dead_guard_apply_list bit body rewrite tail _) as [tail'|] eqn:E;
        try discriminate.
      injection Happ as <-; intros ps Hv Hz; cbn [Execute_suppl].
      apply (IH _ _ E).
      * apply Execute_suppl_valid; exact Hv.
      * apply Execute_no_write_bit_zero; assumption.
Qed.

Lemma Dead_guard_here_sound : forall bit body instr,
  Instruction_equiv_zero bit (SeqInstr [IfInstr bit true body; instr]) instr.
Proof.
  intros bit body instr ps Hv Hz.
  change (ProgramState_equiv nq
    (Execute_suppl nq instr (Execute_suppl nq (IfInstr bit true body) ps))
    (Execute_suppl nq instr ps)).
  apply Execute_suppl_Proper, Execute_dead_if_zero; assumption.
Qed.

Theorem Dead_guard_apply_sound : forall instr bit body index result,
  Dead_guard_apply bit body instr index = Some result ->
  Instruction_equiv_zero bit result instr.
Proof.
  induction instr using Instruction_ind'; intros bit body index result Happ.
  all: try (destruct index; cbn [Dead_guard_apply] in Happ; try discriminate;
    injection Happ as <-; apply Dead_guard_here_sound).
  - cbn [Dead_guard_apply] in Happ.
    destruct (Dead_guard_apply_list bit body (Dead_guard_apply bit body) is index)
      as [result_list|] eqn:E; try discriminate.
    injection Happ as <-.
    eapply Dead_guard_apply_list_sound; [|exact E].
    eapply Forall_impl; [|exact H].
    intros instr IH; apply IH.
  - destruct index; cbn [Dead_guard_apply] in Happ.
    + injection Happ as <-; apply Dead_guard_here_sound.
    + destruct (Dead_guard_apply bit body instr index) as [inner|] eqn:E;
        try discriminate.
      injection Happ as <-.
      apply Instruction_if_zero_congr; eapply IHinstr; exact E.
Qed.

Definition Program_equiv (nc : nat) (left right : Instruction) : Prop :=
  ProgramState_equiv nq (Execute nq nc left) (Execute nq nc right).

Lemma ProgramState_init_bit_zero : forall nc bit,
  ProgramState_bit_zero bit (ProgramState_init nq nc).
Proof.
  intros; apply bit_zero_add; [apply CState_read_init | apply bit_zero_empty].
Qed.

Theorem Transform_dead_if_deep : forall nc bit body instr index result,
  Dead_guard_apply bit body instr index = Some result ->
  Program_equiv nc result instr.
Proof.
  intros nc bit body instr index result Happ.
  apply (Dead_guard_apply_sound instr bit body index result Happ).
  - apply ProgramState_init_valid.
  - apply ProgramState_init_bit_zero.
Qed.

Theorem Transform_dead_if_prefix : forall nc bit body prefix suffix,
  forallb (Instruction_no_write bit) prefix = true ->
  Program_equiv nc
    (SeqInstr (prefix ++ IfInstr bit true body :: suffix))
    (SeqInstr (prefix ++ suffix)).
Proof.
  intros nc bit body prefix suffix Hfree.
  unfold Program_equiv, Execute; cbn [Execute_suppl].
  repeat rewrite fold_left_app; simpl.
  change (ProgramState_equiv nq
    (Execute_suppl nq (SeqInstr suffix)
      (Execute_suppl nq (IfInstr bit true body)
        (Execute_suppl nq (SeqInstr prefix) (ProgramState_init nq nc))))
    (Execute_suppl nq (SeqInstr suffix)
      (Execute_suppl nq (SeqInstr prefix) (ProgramState_init nq nc)))).
  apply Execute_suppl_Proper, Execute_dead_if_zero.
  - apply Execute_suppl_valid, ProgramState_init_valid.
  - apply Execute_no_write_bit_zero; [exact Hfree | apply ProgramState_init_bit_zero].
Qed.

End DEAD_GUARD.
