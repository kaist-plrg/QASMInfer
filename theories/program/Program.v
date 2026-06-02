Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section PROGRAM.

Variable nq : nat. (* number of qubits *)
Variable nc : nat.  (* number of classical bits *)


(* desugared QASM instructions ================================================================== *)

Inductive Instruction : Type :=
| NopInstr: Instruction
| RotateInstr: R -> R -> R -> nat -> Instruction  (* U (theta phi lambda) qbit *)
| CnotInstr: nat -> nat -> Instruction  (* CnotInstr a b: flip b iff a *)
| SwapInstr: nat -> nat -> Instruction  (* SwapInstr a b: swap a b *)
| MeasureInstr: nat -> nat -> Instruction  (* MeasureInstr q c: *)
| SeqInstr: list Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction  (* if cbit == 0 (false) or cbit == 1 (true) *)
| ResetInstr: nat -> Instruction.  (* reset qbit to 0 *)

Lemma Instruction_ind' :
  forall (P : Instruction -> Prop),
    P NopInstr ->
    (forall theta phi lambda target, P (RotateInstr theta phi lambda target)) ->
    (forall control target, P (CnotInstr control target)) ->
    (forall q1 q2, P (SwapInstr q1 q2)) ->
    (forall qbit cbit, P (MeasureInstr qbit cbit)) ->
    (forall is, Forall P is -> P (SeqInstr is)) ->
    (forall cbit cond subinstr, P subinstr -> P (IfInstr cbit cond subinstr)) ->
    (forall target, P (ResetInstr target)) ->
    forall instr, P instr.
Proof.
  intros P Hnop Hrot Hcnot Hswap Hmeas Hseq Hif Hreset.

  fix IH 1.
  intro instr.
  destruct instr.
  - exact Hnop.
  - exact (Hrot r r0 r1 n).
  - exact (Hcnot n n0).
  - exact (Hswap n n0).
  - exact (Hmeas n n0).
  - (* SeqInstr l *)
    apply Hseq.
    induction l as [|x xs IHxs].
    + constructor.
    + constructor.
      * exact (IH x).
      * exact IHxs.
  - (* IfInstr *)
    exact (Hif n b instr (IH instr)).
  - exact (Hreset n).
Qed.

(* ============================================================================================== *)
(* classical state as positive numbers ========================================================= *)
(* `positive` is defined inductively as:
   1. xH    (base, i.e., 1)
   2. xI p  (append 1, i.e., multiply by 2 and add 1. notation: p~1)
   3. xO p  (append 0, i.e., multiply by 2.           notation: p~0)
   Note: OpenQASMCore's 0-th bit is the outermost bit in this `positive`
   representation. Bits that is out of range are interpreted as 0s, as OpenQASM
   initializes classical bits to 0. Doesn't care about index overflow since the
   desugaring process ensures that won't happen. *)

(* No index overflow means that every classical state is uniquely represented
   since we initialize number of bits to zero (1~0~0~...~0) and only set bits
   within range. So we can use this to implement branch unification; two
   branches with the same classical state, has the same positive representation
   of classical state. *)

Definition CState := positive.

Fixpoint CState_init_suppl (n: nat) : positive :=
  match n with
  | O => xH
  | S n' => (CState_init_suppl n')~0
  end.

Definition CState_init : CState := CState_init_suppl nc.


Fixpoint CState_read (idx: nat) (cstate: CState) : bool :=
  match idx, cstate with
  | O, xO _ => false
  | O, xI _ => true
  | S idx', xO c | S idx', xI c => CState_read idx' c
  | _, xH    => false  (* idx overflow -> just read 0, unreachable due to the desugaring process *)
end.


(* given a cstate and an index, produce two cstates by branching at the index by 0 and 1 *)
Fixpoint CState_branch (idx: nat) (cstate: CState) : (CState * CState) :=
  match idx, cstate with
  (* | O, _ => (cstate, cstate)%positive *)
  | O, xO c | O, xI c =>
      (c~0, c~1)%positive
  | O, xH =>
      (1~0, 1~1)%positive (* idx overflow -> just write 0 and 1, unreachable due to the desugaring process *)
  | S idx', xO c =>
      let (c0, c1) := CState_branch idx' c in
      (c0~0, c1~0)%positive
  | S idx', xI c =>
      let (c0, c1) := CState_branch idx' c in
      (c0~1, c1~1)%positive
  | S idx', xH =>
      let (c0, c1) := CState_branch idx' xH in
      (c0~0, c1~0)%positive  (* idx overflow -> pad with 0s, unreachable due to the desugaring process *)
end.

Lemma CState_branch_correct:
  forall (idx: nat) (cstate: CState),
    let (c0, c1) := CState_branch idx cstate in
    CState_read idx c1 = true /\ CState_read idx c0 = false.
Proof.
  induction idx, cstate; simpl; auto.
  all: destruct (CState_branch idx _) as [c0 c1] eqn:eb; simpl.
  1-2: specialize (IHidx cstate).
  3:   specialize (IHidx 1%positive).
  all: destruct (CState_branch idx _) as [c0' c1'] eqn:eb' in IHidx.
  all: rewrite eb in eb'.
  all: injection eb' as Hc0 Hc1.
  all: rewrite Hc0, Hc1.
  all: apply IHidx.
Qed.

Lemma CState_branch_different:
  forall (idx: nat) (cstate: CState),
    let (c0, c1) := CState_branch idx cstate in
    c0 <> c1.
Proof.
  intros.
  assert (Hread_value: let (c0, c1) := CState_branch idx cstate in
    CState_read idx c1 = true /\ CState_read idx c0 = false). {
    apply CState_branch_correct.
  }
  remember (CState_branch idx cstate) as branches eqn:Hbranches.
  destruct branches as [c0 c1].
  intros Heq.
  assert (Hread: CState_read idx c1 = CState_read idx c0). {
    rewrite Heq.
    reflexivity.
  }
  destruct Hread_value as [Hread1 Hread0].
  rewrite Hread1, Hread0 in Hread.
  discriminate.
Qed.

(* ============================================================================================== *)
(* Branches for different classical states ====================================================== *)

Record Branch: Type := {
  B_qstate: Matrix nq; (* density matrix *)
  B_prob: R; (* probability of the branch *)
  (* B_prob_valid: (B_prob > 0)%R; TODO: prove later that prob is always > 0 separately (for equivalence) *)
}.

Definition Branch_valid (b: Branch): Prop := den_valid (B_qstate b) /\ (B_prob b > 0)%R.

Definition Branch_invariant (b: Branch): Prop := den_valid (B_qstate b) /\ (B_prob b > 0)%R /\ (B_prob b <= 1)%R.

Definition Branch_init: Branch := {|
    B_qstate := den_init nq;
    B_prob := 1;
  |}.

Definition Branch_merge (b0 b1: Branch): Branch :=
  {|
    B_qstate :=
      (B_prob b0 / (B_prob b0 + B_prob b1))%com .* B_qstate b0 +
      (B_prob b1 / (B_prob b0 + B_prob b1))%com .* B_qstate b1;
    B_prob := B_prob b0 + B_prob b1;
  |}.

Lemma Branch_invariant_valid:
  forall (b: Branch), Branch_invariant b -> Branch_valid b.
Proof.
  intros b Hbi.
  unfold Branch_valid.
  unfold Branch_invariant in Hbi.
  destruct Hbi as [Hden [Hgt0 Hle1]].
  split. apply Hden. apply Hgt0.
Qed.

Lemma Branch_merge_valid: forall (b0 b1: Branch),
  Branch_valid b0 -> Branch_valid b1 -> Branch_valid (Branch_merge b0 b1).
Proof.
  intros b0 b1 [Hvalid0 Hprob0] [Hvalid1 Hprob1].
  unfold Branch_merge, Branch_valid in *; simpl.
  split.
  apply den_valid_mix.
  all: try lra; assumption.
Qed.

Lemma Branch_merge_prob_sum:
  forall (b0 b1: Branch),
    B_prob (Branch_merge b0 b1) = (B_prob b0 + B_prob b1)%R.
Proof.
  intros b0 b1.
  unfold Branch_merge.
  simpl.
  reflexivity.
Qed.

Lemma Branch_merge_commute:
  forall b1 b2,
  Branch_merge b1 b2 = Branch_merge b2 b1.
Proof.
  intros [p1 q1] [p2 q2].
  unfold Branch_merge. simpl.
  f_equal.
  - rewrite mat_add_comm.
    f_equal; f_equal; f_equal; lca.
  - lra.
Qed.

Lemma Branch_merge_transpose :
  forall b b1 b2,
  Branch_valid b ->
  Branch_valid b1 ->
  Branch_valid b2 ->
  Branch_merge b1 (Branch_merge b2 b) =
  Branch_merge b2 (Branch_merge b1 b).
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

(* ============================================================================================== *)
(* Program state as pos -> branch, i.e., map from cstate to qstate and probability ============== *)
(* This is possible thanks to branch unification ================================================ *)

Definition ProgramState: Type := PositiveMap.t Branch.

(* every qstate in ProgramState is valid *)
Definition ProgramState_valid (ps: ProgramState): Prop :=
  forall (cstate: positive) (branch: Branch),
    PositiveMap.MapsTo cstate branch ps -> Branch_valid branch.

Definition ProgramState_sum_prob (ps: ProgramState) : R :=
  (PositiveMap.fold (fun _ b acc => acc + b) (PositiveMap.map B_prob ps) 0)%R.

Definition ProgramState_prob_valid (ps: ProgramState): Prop :=
  (ProgramState_sum_prob ps = 1)%R.

Definition ProgramState_branch_invariant (ps: ProgramState): Prop :=
  forall (cstate: positive) (branch: Branch),
    PositiveMap.MapsTo cstate branch ps -> Branch_invariant branch.

Definition ProgramState_invariant (ps: ProgramState): Prop :=
  ProgramState_branch_invariant ps /\ ProgramState_prob_valid ps.

Definition ProgramState_init: ProgramState :=
  PositiveMap.add CState_init Branch_init (PositiveMap.empty Branch).

Definition merge_step (cstate: positive) (branch:Branch) (acc: PositiveMap.t Branch) :=
  match PositiveMap.find cstate acc with
  | Some branch' => PositiveMap.add cstate (Branch_merge branch branch') acc
  | None         => PositiveMap.add cstate branch acc
  end.

Definition ProgramState_merge (ps0 ps1: ProgramState): ProgramState :=
  PositiveMap.fold merge_step ps0 ps1.

Lemma ProgramState_branch_invariant_valid:
  forall (ps: ProgramState), ProgramState_branch_invariant ps -> ProgramState_valid ps.
Proof.
  intros ps Hbi.
  unfold ProgramState_valid.
  intros cstate branch Hmapsto.
  apply Branch_invariant_valid.
  unfold ProgramState_branch_invariant in Hbi.
  apply Hbi with (cstate:=cstate).
  apply Hmapsto.
Qed.

Lemma ProgramState_invariant_valid:
  forall (ps: ProgramState), ProgramState_invariant ps -> ProgramState_valid ps.
Proof.
  intros ps [Hbi Hprob_valid].
  apply ProgramState_branch_invariant_valid.
  apply Hbi.
Qed. 

Lemma ProgramState_init_valid: ProgramState_valid ProgramState_init.
Proof.
  unfold ProgramState_init.
  intros cstate branch Hmaps.
  apply PFacts.add_mapsto_iff in Hmaps.
  destruct Hmaps as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_empty]].
  - rewrite <- Hbranch_eq.
    unfold Branch_init, Branch_valid; simpl.
    split.
    apply den_valid_init.
    lra.
  - apply PFacts.empty_mapsto_iff in Hmaps_empty.
    contradiction.
Qed.

Lemma ProgramState_ind (P : ProgramState -> Prop):
  (forall m m',
      PositiveMap.Equal m m' ->
      P m ->
      P m') ->
  P (PositiveMap.empty Branch) ->
  (forall k b m,
      ~ PositiveMap.In k m ->
      P m ->
      P (PositiveMap.add k b m)) ->
  forall m, P m.
Proof.
  intros P_morph P_empty P_add m.

  eapply PProperties.fold_rec_bis
    with
      (P := fun m _ => P m)
      (f := fun _ _ _ => tt)
      (i := tt)
      (m := m).
  - intros m1 m2 _ Heq HP.
    eapply P_morph; eauto.
  - exact P_empty.
  - intros k x _ m0 Hkx Hnotin IH.
    apply P_add.
    apply Hnotin.
    exact IH.
Qed.

Lemma ProgramState_sum_prob_empty:
  forall (ps: ProgramState),
  PositiveMap.Empty ps ->
  ProgramState_sum_prob ps = 0%R.
Proof.
  intros ps Hempty.
  unfold ProgramState_sum_prob.
  rewrite PositiveMap_fold_map.
  rewrite PositiveMap.fold_1.
  apply PProperties.elements_Empty in Hempty.
  rewrite Hempty.
  reflexivity.
Qed.

Lemma ProgramState_init_prob_valid: ProgramState_prob_valid ProgramState_init.
Proof.
  unfold ProgramState_init, ProgramState_prob_valid, ProgramState_sum_prob.
  rewrite PositiveMap_fold_map.
  rewrite PProperties.fold_Add
  with (m1 := PositiveMap.empty Branch) (k := CState_init) (e := Branch_init).
  - unfold PositiveMap.fold, PositiveMap.xfoldi, PositiveMap.empty.
    simpl. lra.
  - apply eq_equivalence.
  - unfold Proper. reflexivity.
  - unfold PProperties.transpose_neqkey.
    intros. lra.
  - intro H.
    apply PFacts.empty_in_iff in H.
    apply H.
  - unfold PProperties.Add.
    intros. reflexivity.
Qed.

Lemma ProgramState_init_invariant: ProgramState_invariant ProgramState_init.
Proof.
  unfold ProgramState_invariant.
  split.
  - unfold ProgramState_init.
    intros cstate branch Hmaps.
    apply PFacts.add_mapsto_iff in Hmaps.
    destruct Hmaps as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_empty]].
    + rewrite <- Hbranch_eq.
      unfold Branch_init, Branch_invariant; simpl.
      split.
      apply den_valid_init.
      lra.
    + apply PFacts.empty_mapsto_iff in Hmaps_empty.
      contradiction.
  - apply ProgramState_init_prob_valid.
Qed.

Lemma ProgramState_empty_valid:
  ProgramState_valid (PositiveMap.empty Branch).
Proof.
  intros cstate branch Hmaps.
  apply PositiveMap.empty_1 in Hmaps.
  exfalso. apply Hmaps.
Qed.

Lemma ProgramState_singleton_valid:
  forall k b,
  Branch_valid b ->
  ProgramState_valid (PositiveMap.add k b (PositiveMap.empty Branch)).
Proof.
  intros k b Hb k' b' H.
  rewrite PFacts.find_mapsto_iff in H.
  destruct (PositiveMap.E.eq_dec k k').
  - subst. rewrite PFacts.add_eq_o in H; inversion H; subst.
    apply Hb. reflexivity.
  - rewrite PFacts.add_neq_o in H.
    rewrite PFacts.empty_o in H.
    discriminate H. apply n.
Qed.

Lemma ProgramState_map_valid: forall {f: Branch -> Branch} {ps: ProgramState},
  ProgramState_valid ps -> (forall b, Branch_valid b -> Branch_valid (f b)) ->
  ProgramState_valid (PositiveMap.map f ps).
Proof.
  unfold ProgramState_valid.
  intros f ps Hps Hf_valid cstate branch' Hmaps.
  apply PFacts.map_mapsto_iff in Hmaps.
  destruct Hmaps as [branch [Hb' Hfind]].
  specialize (Hps cstate branch).
  rewrite Hb'.
  apply Hf_valid.
  apply Hps.
  apply Hfind.
Qed.

Lemma ProgramState_map_prob_preserve: forall (f: Branch -> Branch) (ps: ProgramState),
  (forall b, B_prob b = B_prob (f b)) ->
  ProgramState_sum_prob ps = ProgramState_sum_prob (PositiveMap.map f ps).
Proof.
  intros f ps Hf_prob.
  unfold ProgramState_sum_prob.
  apply PProperties.fold_Equal.
  - apply eq_equivalence.
  - unfold Proper. reflexivity.
  - unfold PProperties.transpose_neqkey.
    intros. lra.
  - intros x.
    rewrite PositiveMap_find_map, PositiveMap_find_map, PositiveMap_find_map.
    destruct (PositiveMap.find x ps) eqn:Hfind.
    + simpl. rewrite Hf_prob. reflexivity.
    + reflexivity.
Qed.

Corollary ProgramState_map_prob_valid: forall (f: Branch -> Branch) (ps: ProgramState),
  ProgramState_prob_valid ps -> (forall b, B_prob b = B_prob (f b)) ->
  ProgramState_prob_valid (PositiveMap.map f ps).
Proof.
  unfold ProgramState_prob_valid.
  intros f ps Hps Hf_prob.
  rewrite <- Hps.
  symmetry.
  apply ProgramState_map_prob_preserve.
  apply Hf_prob.
Qed.

Lemma ProgramState_merge_step_valid:
  forall (cstate: positive) (branch: Branch) (ps: ProgramState),
  ProgramState_valid ps -> Branch_valid branch ->
  ProgramState_valid (merge_step cstate branch ps).
Proof.
  intros cstate branch ps Hps Hb.
  unfold merge_step.
  destruct (PositiveMap.find cstate ps) eqn:Hfind.
  - apply PFacts.find_mapsto_iff in Hfind.
    intros cstate' branch' Hmaps'.
    apply PFacts.add_mapsto_iff in Hmaps'.
    destruct Hmaps' as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_acc]].
    + rewrite <- Hbranch_eq.
      unfold ProgramState_valid in *.
      apply Branch_merge_valid.
      * apply Hb.
      * apply (Hps cstate').
        rewrite <- Hcstate_eq.
        assumption.
    + apply (Hps cstate' branch' Hmaps_acc).
  - apply PFacts.not_find_in_iff in Hfind.
    intros cstate' branch' Hmaps'.
    apply PFacts.add_mapsto_iff in Hmaps'.
    destruct Hmaps' as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_acc]].
    + rewrite <- Hbranch_eq.
      unfold ProgramState_valid in *.
      apply Hb.
    + apply (Hps cstate' branch' Hmaps_acc).
Qed.

Lemma ProgramState_merge_valid: forall (ps0 ps1: ProgramState),
  ProgramState_valid ps0 -> ProgramState_valid ps1 ->
  ProgramState_valid (ProgramState_merge ps0 ps1).
Proof.
  intros ps0 ps1 Hps0 Hps1.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_nodep.
  assumption.
  intros cstate_fold branch_fold acc Hmaps_fold Hacc_valid.
  apply ProgramState_merge_step_valid.
  - assumption.
  - apply Hps0 with cstate_fold.
    apply Hmaps_fold.
Qed.

Lemma ProgramState_fold_add_prob (k: positive) (b: Branch) (ps: ProgramState) :
  PositiveMap.find k ps = None ->
  (PositiveMap.fold (fun _ b acc => acc + B_prob b) (PositiveMap.add k b ps) 0)%R =
  (PositiveMap.fold (fun _ b acc => acc + B_prob b) ps 0 + B_prob b)%R.
Proof.
  intros Hfind.
  rewrite <- PFacts.not_find_in_iff in Hfind.
  rewrite PProperties.fold_add
  with (m := ps) (k := k) (e := b).
  - reflexivity.
  - apply eq_equivalence.
  - unfold Proper. reflexivity.
  - unfold PProperties.transpose_neqkey.
    intros. lra.
  - apply Hfind.
Qed.

Lemma ProgramState_merge_step
  (k:positive) (b:Branch) (ps: ProgramState) :
  ProgramState_sum_prob (merge_step k b ps)
  = (ProgramState_sum_prob ps + B_prob b)%R.
Proof.
  unfold merge_step, ProgramState_sum_prob.
  rewrite PositiveMap_fold_map, PositiveMap_fold_map.
  destruct (PositiveMap.find k ps) eqn:Hfind.
  - rewrite -> PositiveMap_add_remove_equal.
    rewrite <- PositiveMap_add_remove with (k:=k) (old:=b0) (ps:=ps).
    rewrite ProgramState_fold_add_prob.
    rewrite ProgramState_fold_add_prob.
    + rewrite Branch_merge_prob_sum.
      lra.
    + rewrite PProperties.F.remove_eq_o; reflexivity.
    + rewrite PProperties.F.remove_eq_o; reflexivity.
    + assumption.
  - rewrite ProgramState_fold_add_prob.
    + reflexivity.
    + assumption.
Qed.

Lemma fold_left_add_const {A} (w : A -> R) (l : list A) (a c : R) :
  (fold_left (fun acc x => acc + w x) l (a + c)
  = fold_left (fun acc x => acc + w x) l a + c)%R.
Proof.
  revert a.
  induction l as [|x xs IH]; intro a; simpl.
  - lra.
  - rewrite <- IH. f_equal. lra.
Qed.

Lemma ProgramState_merge_prob_sum (ps0 ps1: ProgramState) :
  ProgramState_sum_prob (ProgramState_merge ps0 ps1) =
  (ProgramState_sum_prob ps0 + ProgramState_sum_prob ps1)%R.
Proof.
  unfold ProgramState_merge.
  unfold ProgramState_sum_prob at 1 2.
  rewrite PositiveMap_fold_map, PositiveMap_fold_map.
  rewrite PositiveMap.fold_1, PositiveMap.fold_1, PositiveMap.fold_1.
  revert ps1.
  induction (PositiveMap.elements ps0) as [| (k, b) rest IH]; intros ps1; simpl.
  - unfold ProgramState_sum_prob.
    rewrite PositiveMap_fold_map.
    rewrite PositiveMap.fold_1. 
    lra.
  - rewrite IH.
    rewrite ProgramState_merge_step.
    rewrite fold_left_add_const.
    lra.
Qed.

Lemma ProgramState_fold_merge_prob_preserve:
  forall (ps: ProgramState) (f: CState -> Branch -> ProgramState),
  (forall cstate b, Branch_valid b -> B_prob b = ProgramState_sum_prob (f cstate b)) ->
  ProgramState_valid ps ->
  ProgramState_sum_prob ps = ProgramState_sum_prob (PositiveMap.fold (fun cstate branch acc =>
    ProgramState_merge acc (f cstate branch)) ps (PositiveMap.empty Branch)).
Proof.
  intros ps f Hf_prob Hpsvalid.
  apply PProperties.fold_rec.
  - intros m E.
    rewrite ProgramState_sum_prob_empty.
    rewrite ProgramState_sum_prob_empty.
    + reflexivity.
    + apply PositiveMap.empty_1.
    + apply E.
  - intros k e a m m' H1 H2 H3 H4.
    rewrite ProgramState_merge_prob_sum.
    rewrite <- H4.
    rewrite <- Hf_prob.
    + assert (HE: PositiveMap.Equal m' (PositiveMap.add k e m)).
      { unfold PositiveMap.Equal. apply H3. }
      unfold ProgramState_sum_prob.
      rewrite PositiveMap_fold_map, PositiveMap_fold_map.
      rewrite PProperties.fold_Equal with (m2 := PositiveMap.add k e m).
      1: rewrite PProperties.fold_add.
      * reflexivity.
      * apply eq_equivalence.
      * (unfold Proper; reflexivity).
      * (unfold PProperties.transpose_neqkey; intros; lra).
      * assumption.
      * apply eq_equivalence.
      * (unfold Proper; reflexivity).
      * (unfold PProperties.transpose_neqkey; intros; lra).
      * assumption. 
    + unfold ProgramState_valid in Hpsvalid.
      apply Hpsvalid with (cstate := k) (branch := e).
      apply H1.
Qed.

Lemma ProgramState_merge_o :
  forall ps1 ps2 cstate,
    PositiveMap.find cstate (ProgramState_merge ps1 ps2)
    =
    match PositiveMap.find cstate ps1,
          PositiveMap.find cstate ps2 with
    | Some b1, Some b2 =>
        Some (Branch_merge b1 b2)
    | Some b1, None =>
        Some b1
    | None, Some b2 =>
        Some b2
    | None, None =>
        None
    end.
Proof.
  intros ps1 ps2 cstate.
  unfold ProgramState_merge.
  revert cstate.

  pattern ps1, (PositiveMap.fold merge_step ps1 ps2).
  apply PProperties.fold_rec.

  - (* Empty *)
    intros m0 Hempty cstate.
    destruct (PositiveMap.find cstate m0) as [b |] eqn:Hfind.
    + exfalso.
      apply (Hempty cstate b).
      apply PositiveMap.find_2.
      exact Hfind.
    + destruct (PositiveMap.find cstate ps2); reflexivity.

  - (* Add *)
    intros k branch acc m m' Hmapsto Hnotin Hadd IH cstate.
    unfold merge_step.

    unfold PProperties.Add in Hadd.

    destruct (PositiveMap.E.eq_dec k cstate) as [Heq | Hneq].

    + (* k = cstate *)
      subst cstate.

      assert (Hfind_m_none : PositiveMap.find k m = None).
      {
        destruct (PositiveMap.find k m) as [b0 |] eqn:Hfind.
        - exfalso.
          apply Hnotin.
          exists b0.
          apply PositiveMap.find_2.
          exact Hfind.
        - reflexivity.
      }

      specialize (IH k).
      rewrite Hfind_m_none in IH.

      specialize (Hadd k).
      rewrite PProperties.F.add_o in Hadd.
      destruct (PositiveMap.E.eq_dec k k) as [_ | Hkk].
      2: contradiction.

      rewrite Hadd.
      rewrite IH.

      destruct (PositiveMap.find k ps2) as [b2 |] eqn:Hps2;
        rewrite PProperties.F.add_o;
        destruct (PositiveMap.E.eq_dec k k) as [_ | Hkk];
        try contradiction;
        reflexivity.

    + (* k <> cstate *)
      specialize (Hadd cstate).
      rewrite PProperties.F.add_o in Hadd.
      destruct (PositiveMap.E.eq_dec k cstate) as [Hkc | _].
      { contradiction. }

      rewrite Hadd.

      specialize (IH cstate).

      destruct (PositiveMap.find k acc) as [branch' |] eqn:Hacc;
        rewrite PProperties.F.add_o;
        destruct (PositiveMap.E.eq_dec k cstate) as [Hkc | _];
        try contradiction;
        exact IH.
Qed.

(* ============================================================================================== *)
(* execution ==================================================================================== *)

Definition Execute_rotate_instr_branch (theta phi lambda: R) (target: nat) (branch: Branch): Branch :=
  {|
    B_qstate := den_uop (mat_single nq target (mat_rot theta phi lambda)) (B_qstate branch) ;
    B_prob := B_prob branch;
  |}.

Definition Execute_rotate_instr (theta phi lambda: R) (target: nat) (ps: ProgramState): ProgramState :=
  PositiveMap.map (Execute_rotate_instr_branch theta phi lambda target) ps.


Definition Execute_cnot_instr_branch (control target: nat) (branch: Branch): Branch :=
  {|
    B_qstate := den_uop (mat_cnot control target) (B_qstate branch) ;
    B_prob := B_prob branch;
  |}.

Definition Execute_cnot_instr (control target: nat) (ps: ProgramState): ProgramState :=
  PositiveMap.map (Execute_cnot_instr_branch control target) ps.


Definition Execute_swap_instr_branch (q1 q2: nat) (branch: Branch): Branch :=
  {|
    B_qstate := den_uop (mat_swap q1 q2) (B_qstate branch) ;
    B_prob := B_prob branch;
  |}.

Definition Execute_swap_instr (q1 q2: nat) (ps: ProgramState): ProgramState :=
  PositiveMap.map (Execute_swap_instr_branch q1 q2) ps.


Definition Execute_measure_instr_branch (qbit cbit: nat) (cstate: CState) (branch: Branch): ProgramState :=
  let prob0 := com_real (den_prob_0 qbit (B_qstate branch)) in
  let prob1 := com_real (den_prob_1 qbit (B_qstate branch)) in
  let (cstate0, cstate1) := CState_branch cbit cstate in
  match (Rgt_dec prob0 0), (Rgt_dec prob1 0) with
  | left _, left _ => (* true, true *)
      PositiveMap.add cstate0 {|
          B_qstate := den_measure_0 qbit (B_qstate branch);
          B_prob := B_prob branch * prob0;
        |}
        (PositiveMap.add cstate1 {|
          B_qstate := den_measure_1 qbit (B_qstate branch);
          B_prob := B_prob branch * prob1;
        |} (PositiveMap.empty Branch))
  | left _, right _ => (* true, false *)
      PositiveMap.add cstate0 {|
          B_qstate := den_measure_0 qbit (B_qstate branch);
          B_prob := B_prob branch * prob0;
        |} (PositiveMap.empty Branch)
  | right _, left _ => (* false, true *)
      PositiveMap.add cstate1 {|
          B_qstate := den_measure_1 qbit (B_qstate branch);
          B_prob := B_prob branch * prob1;
        |} (PositiveMap.empty Branch)
  | right _, right _ => (* false, false *)
      PositiveMap.empty Branch
  end.

Definition Execute_measure_instr (qbit cbit: nat) (ps: ProgramState): ProgramState :=
  PositiveMap.fold (fun cstate branch acc =>
    ProgramState_merge acc (Execute_measure_instr_branch qbit cbit cstate branch)
  ) ps (PositiveMap.empty Branch).


Definition Execute_reset_instr_branch (target: nat) (branch: Branch): Branch :=
  {|
    B_qstate := den_reset target (B_qstate branch);
    B_prob := B_prob branch;
  |}.

Definition Execute_reset_instr (target: nat) (ps: ProgramState): ProgramState :=
  PositiveMap.map (Execute_reset_instr_branch target) ps.


Fixpoint Execute_suppl (instr: Instruction) (ps: ProgramState): ProgramState :=
    match instr with
    | NopInstr                            => ps
    | RotateInstr theta phi lambda target => Execute_rotate_instr theta phi lambda target ps
    | CnotInstr control target            => Execute_cnot_instr control target ps
    | SwapInstr q1 q2                     => Execute_swap_instr q1 q2 ps
    | MeasureInstr qbit cbit              => Execute_measure_instr qbit cbit ps
    | SeqInstr il                         => List.fold_left (fun ps' instr => Execute_suppl instr ps') il ps
    | IfInstr cbit cond subinstr          => PositiveMap.fold (fun cstate b acc =>
        let ps_single := PositiveMap.add cstate b (PositiveMap.empty Branch) in
        ProgramState_merge acc (
          if (eqb (CState_read cbit cstate) cond)
          then Execute_suppl subinstr ps_single
          else ps_single
        )
      ) ps (PositiveMap.empty Branch)
    | ResetInstr target                   => Execute_reset_instr target ps
    end.

Definition Execute (instr: Instruction): ProgramState :=
  Execute_suppl instr ProgramState_init.

Fixpoint Cstate_to_binary_little_endian (n: nat) (cstate: CState) (acc: nat): nat := match n with
  | O => acc
  | S n' => let bit := if (CState_read n' cstate) then 1 else 0 in
            Cstate_to_binary_little_endian n' cstate (2 * acc + bit)
end.

Definition Cstate_to_binary (num_cbits: nat) (cstate: CState) := Cstate_to_binary_little_endian num_cbits cstate O.

(*  0 -> true
    1 -> false     ===> 1011 (value of 0 is the leftmost bit in the result) (big endian)
    2 -> true      ===> In qasm, they use little endian so have to reverse it
    3 -> true *)

Definition Execute_and_calculate_prob (instr: Instruction) :=
  PositiveMap.elements (PositiveMap.map (fun b => B_prob b) (Execute instr)).

(* ============================================================================================== *)
(* Proof about quantum states =================================================================== *)

Lemma Execute_rotate_instr_valid:
  forall (theta phi lambda: R) (target: nat) (ps: ProgramState),
  ProgramState_valid ps ->
  ProgramState_valid (Execute_rotate_instr theta phi lambda target ps).
Proof.
  intros.
  apply ProgramState_map_valid.
  - apply H.
  - intros b [Hvalid Hprob].
    unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
    split.
    apply den_valid_uop.
    apply mat_single_unitary.
    apply mat_rot_unitary.
    all: assumption.
Qed.

Lemma Execute_cnot_instr_valid:
  forall (control target: nat) (ps: ProgramState),
  ProgramState_valid ps ->
  ProgramState_valid (Execute_cnot_instr control target ps).
Proof.
  intros.
  apply ProgramState_map_valid.
  - apply H.
  - intros b [Hvalid Hprob].
    unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
    split.
    apply den_valid_uop.
    apply mat_cnot_unitary.
    all: assumption.
Qed.

Lemma Execute_swap_instr_valid:
  forall (q1 q2: nat) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_valid (Execute_swap_instr q1 q2 ps).
Proof.
  intros.
  apply ProgramState_map_valid.
  - apply H.
  - intros b [Hvalid Hprob].
    unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
    split.
    apply den_valid_uop.
    apply mat_swap_unitary.
    all: assumption.
Qed.

Lemma Execute_measure_instr_branch_valid:
  forall (qbit cbit: nat) (cstate: CState) (branch: Branch),
  Branch_valid branch ->
  ProgramState_valid (Execute_measure_instr_branch qbit cbit cstate branch).
Proof.
  intros qbit cbit cstate branch [Hvalid Hprob].
  unfold Execute_measure_instr_branch, ProgramState_valid.
  intros cstate' branch'.
  destruct (CState_branch cbit cstate) as [cstate0 cstate1].
  destruct (Rgt_dec (com_real (den_prob_0 qbit (B_qstate branch))) 0) eqn:Hdec0,
           (Rgt_dec (com_real (den_prob_1 qbit (B_qstate branch))) 0) eqn:Hdec1;
           unfold den_prob_0, den_prob_1, com_real in *.
  - intros Hmaps.
    apply PFacts.add_mapsto_iff in Hmaps.
    destruct Hmaps as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps]].
    + rewrite <- Hbranch_eq.
      unfold Branch_valid; simpl.
      split.
      * apply den_valid_measure.
        apply mat_proj0_projection.
        apply Hvalid.
        apply com_proj_neq_fst.
        simpl; lra.
      * nra.
    + apply PFacts.add_mapsto_iff in Hmaps.
      destruct Hmaps as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq' Hmaps]].
      * rewrite <- Hbranch_eq.
        unfold Branch_valid; simpl.
        split.
        -- apply den_valid_measure.
          apply mat_proj1_projection.
          apply Hvalid.
          apply com_proj_neq_fst.
          simpl; lra.
        -- nra.
      * apply PFacts.empty_mapsto_iff in Hmaps.
        contradiction.
  - intros Hmaps.
    apply PFacts.add_mapsto_iff in Hmaps.
    destruct Hmaps as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps]].
    + rewrite <- Hbranch_eq.
      unfold Branch_valid; simpl.
      split.
      * apply den_valid_measure.
        apply mat_proj0_projection.
        apply Hvalid.
        apply com_proj_neq_fst.
        simpl; lra.
      * nra.
    + apply PFacts.empty_mapsto_iff in Hmaps.
      contradiction.
  - intros Hmaps.
    apply PFacts.add_mapsto_iff in Hmaps.
    destruct Hmaps as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps]].
    + rewrite <- Hbranch_eq.
      unfold Branch_valid; simpl.
      split.
      * apply den_valid_measure.
        apply mat_proj1_projection.
        apply Hvalid.
        apply com_proj_neq_fst.
        simpl; lra.
      * nra.
    + apply PFacts.empty_mapsto_iff in Hmaps.
      contradiction.
  - intros Hmaps.
    apply PFacts.empty_mapsto_iff in Hmaps.
    contradiction.
Qed.

Lemma Execute_measure_instr_valid:
  forall (qbit cbit: nat) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_valid (Execute_measure_instr qbit cbit ps).
Proof.
  intros qbit cbit ps Hpsvalid.
  unfold Execute_measure_instr.
  apply PProperties.fold_rec_nodep.
  - unfold ProgramState_valid; intros.
    apply PFacts.empty_mapsto_iff in H.
    contradiction.
  - intros cstate_fold branch_fold acc Hmaps_fold Hacc_valid.
    apply (ProgramState_merge_valid _ _ Hacc_valid).
    apply Execute_measure_instr_branch_valid.
    apply (Hpsvalid cstate_fold branch_fold Hmaps_fold).
Qed.

Lemma Execute_measure_sum_one:
  forall (qbit: nat) (branch: Branch) (prob0 prob1: R),
  Branch_valid branch -> 
  prob0 = com_real (den_prob_0 qbit (B_qstate branch)) ->
  prob1 = com_real (den_prob_1 qbit (B_qstate branch)) ->
  (prob0 + prob1 = 1)%R.
Proof.
  intros qbit branch prob0 prob1 Hvalid Hprob0 Hprob1.
  rewrite Hprob0, Hprob1.
  rewrite <- com_real_plus.
  unfold den_prob_0, den_prob_1, den_prob.
  rewrite <- mat_add_trace, <- mat_mul_dist_l, mat_proj_sum, mat_mul_eye_r.
  assert (G: \tr B_qstate branch = 1).
  {
    apply den_valid_normalized.
    destruct Hvalid as [H_den_valid _].
    apply H_den_valid.
  }
  rewrite G. reflexivity.
Qed.

Lemma Matrix_projection_probability_nonnegative:
  forall (Q P: Matrix nq),
  den_valid Q -> mat_projection P
  -> (den_prob P Q >= 0)%R.
Proof.
  intros Q P H_den [H_proj_mult H_hermit].
  apply den_valid_positive in H_den.
  unfold mat_positive in H_den.
  unfold den_prob.
  rewrite <- H_proj_mult, mat_mul_assoc.
  rewrite mat_mul_trace_comm.
  apply mat_trace_positive.
  unfold mat_positive.
  intros v.
  rewrite vec_mat_mat_mul_assoc, vec_mat_vec_mul_assoc, mat_mat_vec_mul_assoc, <- vec_mat_vec_mul_assoc.
  assert (E: (P *| v) |† = v |† |* P).
  {
    rewrite mat_vec_mul_conjtrans.
    rewrite H_hermit.
    reflexivity.
  }
  rewrite <- E.
  apply H_den.
Qed.

Corollary Branch_density_zero_zero:
  forall (qbit: nat) (branch: Branch) (prob0: R),
  Branch_valid branch ->
  prob0 = com_real (den_prob_0 qbit (B_qstate branch)) ->
  ~ (prob0 > 0)%R ->
  (prob0 = 0)%R.
Proof.
  intros qbit branch prob0 Hvalid Hprob0 Hle0.
  unfold den_prob_0 in *.
  assert (H: (den_prob (mat_proj0 nq qbit) (B_qstate branch) >= 0)%R).
  {
    apply Matrix_projection_probability_nonnegative.
    apply Hvalid.
    apply mat_proj0_projection.
  }
  destruct H as [Hc _].
  rewrite <- Hprob0 in Hc.
  lra.
Qed.

Corollary Branch_density_one_zero:
  forall (qbit: nat) (branch: Branch) (prob1: R),
  Branch_valid branch ->
  prob1 = com_real (den_prob_1 qbit (B_qstate branch)) ->
  ~ (prob1 > 0)%R ->
  (prob1 = 0)%R.
Proof.
  intros qbit branch prob1 Hvalid Hprob1 Hle0.
  unfold den_prob_1 in *.
  assert (H: (den_prob (mat_proj1 nq qbit) (B_qstate branch) >= 0)%R).
  {
    apply Matrix_projection_probability_nonnegative.
    apply Hvalid.
    apply mat_proj1_projection.
  }
  destruct H as [Hc _].
  rewrite <- Hprob1 in Hc.
  lra.
Qed.

Lemma Execute_measure_instr_branch_prob_preserve:
  forall (qbit cbit: nat) (cstate: CState) (branch: Branch),
  Branch_valid branch ->
  B_prob branch = 
  ProgramState_sum_prob (Execute_measure_instr_branch qbit cbit cstate branch).
Proof.
  intros qbit cbit cstate branch Hbranch_valid.
  unfold Execute_measure_instr_branch, ProgramState_sum_prob.
  remember (com_real (den_prob_0 qbit (B_qstate branch))) as prob0.
  remember (com_real (den_prob_1 qbit (B_qstate branch))) as prob1.
  assert (Hprob_sum: (prob0 + prob1 = 1)%R).
  {
    apply (Execute_measure_sum_one qbit branch prob0 prob1 Hbranch_valid Heqprob0 Heqprob1).
  }
  destruct (Rgt_dec prob0 0) eqn:Hdec0,
           (Rgt_dec prob1 0) eqn:Hdec1.
  - rewrite PositiveMap_fold_map.
    assert (Hdiff: let (cstate0, cstate1) := CState_branch cbit cstate in cstate0 <> cstate1).
    {
      apply CState_branch_different.
    }
    remember (CState_branch cbit cstate) as cstates.
    destruct cstates as [cstate0 cstate1].
    remember {|
      B_qstate := den_measure_0 qbit (B_qstate branch);
      B_prob := B_prob branch * prob0;
    |} as branch0.
    remember {|
      B_qstate := den_measure_1 qbit (B_qstate branch);
      B_prob := B_prob branch * prob1;
    |} as branch1.
    rewrite PProperties.fold_add
    with (m := PositiveMap.add cstate1 branch1 (PositiveMap.empty Branch)) (k := cstate0) (e := branch0).
    rewrite PProperties.fold_add
    with (m := PositiveMap.empty Branch) (k := cstate1) (e := branch1).
    all: try exact eq_equivalence.
    all: try (unfold Proper; reflexivity).
    all: try (unfold PProperties.transpose_neqkey; intros; lra).
    + unfold PositiveMap.fold, PositiveMap.xfoldi, PositiveMap.empty.
      rewrite Heqbranch0, Heqbranch1.
      simpl.
      rewrite Rplus_assoc, <- Rmult_plus_distr_l.
      rewrite (Rplus_comm prob1 prob0), Hprob_sum.
      lra.
    + intro H.
      apply PFacts.empty_in_iff in H.
      apply H.
    + apply PFacts.not_find_in_iff.
      rewrite PProperties.F.add_neq_o.
      * rewrite PProperties.F.empty_o. reflexivity.
      * intro H. subst. contradiction.
  - rewrite PositiveMap_fold_map.
    remember (CState_branch cbit cstate) as cstates.
    destruct cstates as [cstate0 cstate1].
    remember {|
      B_qstate := den_measure_0 qbit (B_qstate branch);
      B_prob := B_prob branch * prob0;
    |} as branch0.
    rewrite PProperties.fold_add
    with (m := PositiveMap.empty Branch) (k := cstate0) (e := branch0).
    all: try exact eq_equivalence.
    all: try (unfold Proper; reflexivity).
    all: try (unfold PProperties.transpose_neqkey; intros; lra).
    + unfold PositiveMap.fold, PositiveMap.xfoldi, PositiveMap.empty.
      rewrite Heqbranch0.
      simpl.
      assert (Heq1: prob1 = 0%R).
      {
        apply (Branch_density_one_zero qbit branch prob1 Hbranch_valid Heqprob1 n).
      }
      rewrite Heq1 in Hprob_sum.
      rewrite Rplus_0_r in Hprob_sum.
      rewrite Hprob_sum.
      lra.
    + intro H.
      apply PFacts.empty_in_iff in H.
      apply H.
  - rewrite PositiveMap_fold_map.
    remember (CState_branch cbit cstate) as cstates.
    destruct cstates as [cstate0 cstate1].
    remember {|
      B_qstate := den_measure_1 qbit (B_qstate branch);
      B_prob := B_prob branch * prob1;
    |} as branch1.
    rewrite PProperties.fold_add
    with (m := PositiveMap.empty Branch) (k := cstate1) (e := branch1).
    all: try exact eq_equivalence.
    all: try (unfold Proper; reflexivity).
    all: try (unfold PProperties.transpose_neqkey; intros; lra).
    + unfold PositiveMap.fold, PositiveMap.xfoldi, PositiveMap.empty.
      rewrite Heqbranch1.
      simpl.
      assert (Heq0: prob0 = 0%R).
      {
        apply (Branch_density_zero_zero qbit branch prob0 Hbranch_valid Heqprob0 n).
      }
      rewrite Heq0 in Hprob_sum.
      rewrite Rplus_0_l in Hprob_sum.
      rewrite Hprob_sum.
      lra.
    + intro H.
      apply PFacts.empty_in_iff in H.
      apply H.
  - assert (Heq0: prob0 = 0%R).
    apply (Branch_density_zero_zero qbit branch prob0 Hbranch_valid Heqprob0 n).
    assert (Heq1: prob1 = 0%R).
    apply (Branch_density_one_zero qbit branch prob1 Hbranch_valid Heqprob1 n0).
    rewrite Heq0, Heq1 in Hprob_sum.
    lra.
Qed.

Lemma Execute_measure_instr_prob_preserve:
  forall (qbit cbit: nat) (ps: ProgramState),
  ProgramState_valid ps ->
  ProgramState_sum_prob ps = ProgramState_sum_prob (Execute_measure_instr qbit cbit ps).
Proof.
  unfold Execute_measure_instr.
  intros qbit cbit ps Hpsvalid.
  apply (ProgramState_fold_merge_prob_preserve ps (Execute_measure_instr_branch qbit cbit)).
  - apply Execute_measure_instr_branch_prob_preserve.
  - apply Hpsvalid.
Qed.

Lemma Execute_reset_instr_valid:
  forall (target: nat) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_valid (Execute_reset_instr target ps).
Proof.
  intros.
  apply ProgramState_map_valid.
  - apply H.
  - intros b [Hvalid Hprob].
    unfold Execute_reset_instr_branch, Branch_valid in *; simpl.
    split.
    apply den_valid_reset.
    apply Hvalid.
    assumption.
Qed.


Arguments Execute_rotate_instr _ _ _ _ : simpl never.
Arguments Execute_cnot_instr _ _ _ : simpl never.
Arguments Execute_swap_instr _ _ _ : simpl never.
Arguments Execute_measure_instr _ _ _ : simpl never.


Lemma Execute_suppl_valid:
  forall (instr: Instruction) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_valid (Execute_suppl instr ps).
Proof.
  induction instr using Instruction_ind'.
  all: intros; simpl.
  - exact H.
  - apply Execute_rotate_instr_valid; apply H.
  - apply Execute_cnot_instr_valid; apply H.
  - apply Execute_swap_instr_valid; apply H.
  - apply Execute_measure_instr_valid; apply H.
  - generalize dependent ps. induction is; simpl; intros.
    + apply H0.
    + inversion H. apply IHis.
      * apply H4.
      * apply H3. apply H0.
  - apply PProperties.fold_rec_nodep.
    + unfold ProgramState_valid; intros.
      apply PFacts.empty_mapsto_iff in H0.
      contradiction.
    + intros cstate_fold branch_fold acc Hmaps_fold Hacc_valid.
      destruct (eqb (CState_read cbit cstate_fold) cond) eqn:Hcond.
      all: apply (ProgramState_merge_valid _ _ Hacc_valid).
      1: apply IHinstr.
      all: intros cstate' branch' Hmaps'.
      all: apply PFacts.add_mapsto_iff in Hmaps'.
      all: destruct Hmaps' as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_acc]].
      all: subst.
      all: apply (H cstate' branch'); try assumption.
      all: apply PFacts.empty_mapsto_iff in Hmaps_acc.
      all: contradiction.
  - apply Execute_reset_instr_valid; apply H.
Qed.

Lemma Execute_suppl_prob_valid:
  forall (instr: Instruction) (ps: ProgramState),
  ProgramState_valid ps ->
  ProgramState_sum_prob ps = ProgramState_sum_prob (Execute_suppl instr ps).
Proof.
  induction instr using Instruction_ind'.
  all: intros; simpl;
  try (apply ProgramState_map_prob_preserve; intros b; reflexivity).
  - reflexivity.
  - apply Execute_measure_instr_prob_preserve. apply H.
  - generalize dependent ps.
    induction is; simpl; intros.
    + reflexivity.
    + inversion H. rewrite (H3 _ H0). apply IHis.
      * apply H4.
      * apply Execute_suppl_valid. apply H0.
  - apply ProgramState_fold_merge_prob_preserve.
    + intros cstate branch Hbvalid.
      destruct (eqb (CState_read cbit cstate) cond).
      * rewrite <- IHinstr.
        unfold ProgramState_sum_prob.
        rewrite PositiveMap_fold_map, PProperties.fold_add.
        -- rewrite <- PositiveMap_fold_map with (f:=(fun _ v acc => (acc + v)%R)) (g:=B_prob).
           change (B_prob branch = ProgramState_sum_prob (PositiveMap.empty Branch) + B_prob branch)%R.
           rewrite ProgramState_sum_prob_empty.
           lra. apply PositiveMap.empty_1.
        -- apply eq_equivalence.
        -- unfold Proper. reflexivity.
        -- unfold PProperties.transpose_neqkey. intros. lra.
        -- intros HI. apply PFacts.empty_in_iff in HI. apply HI.
        -- unfold ProgramState_valid.
           intros cstate' branch' Hmapsto.
           rewrite PFacts.add_mapsto_iff in Hmapsto.
           destruct Hmapsto as [[Hcstate Hbranch] | [Hcstate Hbranch]].
           { rewrite <- Hbranch. apply Hbvalid. }
           { rewrite PFacts.empty_mapsto_iff in Hbranch. contradiction. }
      * unfold ProgramState_sum_prob.
        rewrite PositiveMap_fold_map, PProperties.fold_add.
        -- change (B_prob branch = ProgramState_sum_prob (PositiveMap.empty Branch) + B_prob branch)%R.
           rewrite ProgramState_sum_prob_empty.
           lra. apply PositiveMap.empty_1.
        -- apply eq_equivalence.
        -- unfold Proper. reflexivity.
        -- unfold PProperties.transpose_neqkey. intros. lra.
        -- intros HI. apply PFacts.empty_in_iff in HI. apply HI.
    + apply H.
Qed.

Lemma Execute_suppl_valid_prob:
  forall (instr: Instruction) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_prob_valid ps ->
  ProgramState_prob_valid (Execute_suppl instr ps).
Proof.
  intros.
  unfold ProgramState_prob_valid in *.
  rewrite <- H0.
  symmetry.
  apply Execute_suppl_prob_valid.
  apply H.
Qed.

Lemma ProgramState_valid_sum_prob_nonnegative:
  forall (ps: ProgramState),
  ProgramState_valid ps -> (Rge (ProgramState_sum_prob ps) 0)%R.
Proof.
  intros ps Hpsvalid.
  unfold ProgramState_valid in Hpsvalid.
  unfold ProgramState_sum_prob.
  rewrite PositiveMap_fold_map.
  apply PProperties.fold_rec.
  - intros m Hm.
    lra.
  - intros k e a m m' H1 H2 H3 H4.
    assert (H: Rge (B_prob e) 0).
    {
      unfold Branch_valid in Hpsvalid.
      apply Rgt_ge.
      eapply (proj2 (Hpsvalid k e H1)). 
    }
    lra.
Qed. 

Lemma ProgramState_valid_invariant:
  forall (ps: ProgramState),
  ProgramState_valid ps /\ ProgramState_prob_valid ps -> ProgramState_invariant ps.
Proof.
  intros ps [Hvalid Hprob].
  unfold ProgramState_invariant.
  split.
  - unfold ProgramState_branch_invariant.
    intros cstate branch Hmapsto.
    unfold Branch_invariant.
    unfold ProgramState_valid, Branch_valid in Hvalid.
    rewrite <- and_assoc.
    split.
    + apply Hvalid with (cstate:=cstate). apply Hmapsto.
    + unfold ProgramState_prob_valid, ProgramState_sum_prob in Hprob.
      rewrite PositiveMap_fold_map, <- (PositiveMap_add_remove cstate branch) in Hprob.
      * remember (PositiveMap.remove cstate ps) as ps'.
        rewrite PProperties.fold_add with (eqA := @eq R) in Hprob.
        -- assert (Hge: Rge (ProgramState_sum_prob ps') 0).
           {
             apply ProgramState_valid_sum_prob_nonnegative.
             unfold ProgramState_valid.
             intros cstate' branch' Hmapsto'.
             apply (Hvalid cstate' branch').
             rewrite Heqps' in Hmapsto'.
             apply PositiveMap.remove_3 with (x:= cstate).
             apply Hmapsto'.
           }
           unfold ProgramState_sum_prob in Hge.
           rewrite PositiveMap_fold_map in Hge.
           lra.
        -- apply eq_equivalence.
        -- unfold Proper. reflexivity.
        -- unfold PProperties.transpose_neqkey. intros. lra.
        -- rewrite Heqps'. apply PositiveMap.remove_1. reflexivity. 
      * rewrite <- PFacts.find_mapsto_iff. apply Hmapsto. 
  - apply Hprob.
Qed.

Lemma Execute_suppl_valid_invariant:
  forall (instr: Instruction) (ps: ProgramState),
  ProgramState_invariant ps -> ProgramState_invariant (Execute_suppl instr ps).
Proof.
  intros instr ps [Hbinv Hprob].
  split.
  - apply ProgramState_valid_invariant. split.
    + apply Execute_suppl_valid. apply ProgramState_branch_invariant_valid. apply Hbinv.
    + apply Execute_suppl_valid_prob.
      * apply ProgramState_branch_invariant_valid. apply Hbinv.
      * apply Hprob.
  - apply Execute_suppl_valid_prob.
    + apply ProgramState_branch_invariant_valid. apply Hbinv.
    + apply Hprob.
Qed.

Theorem Execute_valid: forall (instr: Instruction),
  ProgramState_valid (Execute instr).
Proof.
  intros.
  unfold Execute.
  apply Execute_suppl_valid.
  apply ProgramState_init_valid.
Qed.

Theorem Execute_invariant: forall (instr: Instruction),
  ProgramState_invariant (Execute instr).
Proof.
  intros.
  unfold Execute.
  apply Execute_suppl_valid_invariant.
  apply ProgramState_init_invariant.
Qed.

End PROGRAM.

(* ============================================================================================== *)
(* Notation of OpenQASMCore ===================================================================== *)

Definition qasm_seq (i j : Instruction) : Instruction :=
  match i, j with
  | SeqInstr is, SeqInstr js => SeqInstr (is ++ js)
  | SeqInstr is, _          => SeqInstr (is ++ [j])
  | _,          SeqInstr js => SeqInstr (i :: js)
  | _,          _           => SeqInstr [i; j]
  end.

Arguments qasm_seq _ _ : simpl never.

Declare Custom Entry qasm.

Notation "qasm{ e }" := e (e custom qasm at level 99).
Notation "( x )" := x (in custom qasm at level 0, x at level 99).
Notation "$ t" := t (in custom qasm at level 0, t constr at level 0).
Notation "x" := x (in custom qasm at level 0, x constr at level 0).

Notation "'nop'" := NopInstr (in custom qasm at level 0).

Notation "'U' ( θ , φ , λ ) q" :=
  (RotateInstr θ φ λ q)
  (in custom qasm at level 0,
     θ constr at level 0, φ constr at level 0, λ constr at level 0, q constr at level 0).

Notation "'cx' a b" :=
  (CnotInstr a b)
  (in custom qasm at level 0, a constr at level 0, b constr at level 0).

Notation "'swap' a b" :=
  (SwapInstr a b)
  (in custom qasm at level 0, a constr at level 0, b constr at level 0).

Notation "'measure' q '->' c" :=
  (MeasureInstr q c)
  (in custom qasm at level 0, q constr at level 0, c constr at level 0).

Notation "'reset' q" :=
  (ResetInstr q)
  (in custom qasm at level 0, q constr at level 0).

Notation "'if' '(' cb '==' 0 ')' i" :=
  (IfInstr cb false i)
  (in custom qasm at level 60, right associativity,
     cb constr at level 0, i custom qasm at level 99).

Notation "'if' '(' cb '==' 1 ')' i" :=
  (IfInstr cb true i)
  (in custom qasm at level 60, right associativity,
     cb constr at level 0, i custom qasm at level 99).

Notation "i ; j" :=
  (qasm_seq i j)
  (in custom qasm at level 70, right associativity,
     i custom qasm, j custom qasm at level 70).

Notation "'seq[' is ']'" :=
  (SeqInstr is)
  (in custom qasm at level 0, is constr at level 0).