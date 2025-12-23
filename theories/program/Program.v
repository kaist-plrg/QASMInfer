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
| SeqInstr: Instruction -> Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction  (* if cbit == 0 (false) or cbit == 1 (true) *)
| ResetInstr: nat -> Instruction.  (* reset qbit to 0 *)


(* ============================================================================================== *)
(* desugared QASM program ======================================================================= *)

Record InlinedProgram : Type := {
  IP_num_cbits: nat; (* TODO: Remove? *)
  IP_instrs: Instruction;
}.

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

(* Example tests:
Compute (CState_read 0 (1~0~1)%positive).  (* expect true *)
Compute (CState_read 1 (1~0~1)%positive).  (* expect false *)
Compute (CState_read 2 (1~0~1)%positive).  (* expect false (idx overflow) *)
Compute (CState_branch 1 (CState_init_suppl 10)).  (* expect ((1~)0~0, (1~)1~0) *)
Compute (CState_branch 3 (1~1~0)%positive).  (* expect (1~0~0~1~0, 1~1~0~1~0) *)
*)


(* ============================================================================================== *)
(* Branches for different classical states ====================================================== *)

Record Branch: Type := {
  B_qstate: Matrix nq; (* density matrix *)
  B_prob: R; (* probability of the branch *)
  (* B_prob_valid: (B_prob > 0)%R; TODO: prove later that prob is always > 0 separately (for equivalence) *)
}.

Definition Branch_valid (b: Branch): Prop := den_valid (B_qstate b) /\ (B_prob b > 0)%R.

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

Lemma Branch_merge_valid: forall (b0 b1: Branch),
  Branch_valid b0 -> Branch_valid b1 -> Branch_valid (Branch_merge b0 b1).
Proof.
  intros b0 b1 [Hvalid0 Hprob0] [Hvalid1 Hprob1].
  unfold Branch_merge, Branch_valid in *; simpl.
  split.
  apply den_valid_mix.
  all: try lra; assumption.
Qed.


(* ============================================================================================== *)
(* Program state as pos -> branch, i.e., map from cstate to qstate and probability ============== *)
(* This is possible thanks to branch unification ================================================ *)

Definition ProgramState: Type := PositiveMap.t Branch.

(* every qstate in ProgramState is valid *)
Definition ProgramState_valid (ps: ProgramState): Prop :=
  forall (cstate: positive) (branch: Branch),
    PositiveMap.MapsTo cstate branch ps -> Branch_valid branch.

Definition ProgramState_init: ProgramState :=
  PositiveMap.add CState_init Branch_init (PositiveMap.empty Branch).

Definition ProgramState_merge (ps0 ps1: ProgramState): ProgramState :=
  PositiveMap.fold (fun cstate branch acc =>
    match PositiveMap.find cstate acc with
    | Some branch' =>
        PositiveMap.add cstate (Branch_merge branch branch') acc
    | None =>
        PositiveMap.add cstate branch acc
    end) ps0 ps1.

Lemma ProgramState_map_valid: forall (f: Branch -> Branch) (ps: ProgramState),
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

Lemma ProgramState_merge_valid: forall (ps0 ps1: ProgramState),
  ProgramState_valid ps0 -> ProgramState_valid ps1 ->
  ProgramState_valid (ProgramState_merge ps0 ps1).
Proof.
  intros ps0 ps1 Hps0 Hps1.
  unfold ProgramState_merge.
  apply PProperties.fold_rec_nodep.
  assumption.
  intros cstate_fold branch_fold acc Hmaps_fold Hacc_valid.
  destruct (PositiveMap.find cstate_fold acc) eqn:Hfind.
  - apply PFacts.find_mapsto_iff in Hfind.
    intros cstate' branch' Hmaps'.
    apply PFacts.add_mapsto_iff in Hmaps'.
    destruct Hmaps' as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_acc]].
    + rewrite <- Hbranch_eq.
      unfold ProgramState_valid in *.
      apply Branch_merge_valid.
      * apply (Hps0 cstate_fold branch_fold Hmaps_fold).
      * apply (Hacc_valid cstate').
        rewrite <- Hcstate_eq.
        assumption.
    + apply (Hacc_valid cstate' branch' Hmaps_acc).
  - apply PFacts.not_find_in_iff in Hfind.
    intros cstate' branch' Hmaps'.
    apply PFacts.add_mapsto_iff in Hmaps'.
    destruct Hmaps' as [[Hcstate_eq Hbranch_eq] | [Hcstate_neq Hmaps_acc]].
    + rewrite <- Hbranch_eq.
      unfold ProgramState_valid in *.
      apply (Hps0 cstate_fold branch_fold Hmaps_fold).
    + apply (Hacc_valid cstate' branch' Hmaps_acc).
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
    | SeqInstr i1 i2                      => Execute_suppl i2 (Execute_suppl i1 ps)
    | IfInstr cbit cond subinstr          => PositiveMap.fold (fun cstate b acc =>
        let ps_single := PositiveMap.add cstate b (PositiveMap.empty Branch) in
        if (eqb (CState_read cbit cstate) cond)
        then Execute_suppl subinstr ps_single
        else ps_single) ps (PositiveMap.empty Branch)
    | ResetInstr target                   => Execute_reset_instr target ps
    end.

Definition Execute (program: InlinedProgram): ProgramState :=
  Execute_suppl (IP_instrs program) ProgramState_init.

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

Definition Calculate_prob (ps: ProgramState): PositiveMap.t R :=
  PositiveMap.map (fun b => B_prob b) ps.

Definition Execute_and_calculate_prob (program: InlinedProgram): PositiveMap.t R :=
  Calculate_prob (Execute program).

(* ============================================================================================== *)
(* Proof about quantum states =================================================================== *)

Lemma Execute_rotate_instr_valid:
  forall (theta phi lambda: R) (target: nat) (ps: ProgramState),
  ProgramState_valid ps ->
  ProgramState_valid (Execute_rotate_instr theta phi lambda target ps).
Proof.
  intros.
  apply (ProgramState_map_valid _ _ H).
  intros b [Hvalid Hprob].
  unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
  split.
  apply den_valid_uop.
  apply mat_single_unitary.
  apply mat_rot_unitary.
  assumption.
  assumption.
Qed.

Lemma Execute_cnot_instr_valid:
  forall (control target: nat) (ps: ProgramState),
  ProgramState_valid ps ->
  ProgramState_valid (Execute_cnot_instr control target ps).
Proof.
  intros.
  apply (ProgramState_map_valid _ _ H).
  intros b [Hvalid Hprob].
  unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
  split.
  apply den_valid_uop.
  apply mat_cnot_unitary.
  assumption.
  assumption.
Qed.

Lemma Execute_swap_instr_valid:
  forall (q1 q2: nat) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_valid (Execute_swap_instr q1 q2 ps).
Proof.
  intros.
  apply (ProgramState_map_valid _ _ H).
  intros b [Hvalid Hprob].
  unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
  split.
  apply den_valid_uop.
  apply mat_swap_unitary.
  assumption.
  assumption.
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


Lemma Execute_reset_instr_valid:
  forall (target: nat) (ps: ProgramState),
  ProgramState_valid ps -> ProgramState_valid (Execute_reset_instr target ps).
Proof.
  intros.
  apply (ProgramState_map_valid _ _ H).
  intros b [Hvalid Hprob].
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
  induction instr.
  all: intros; simpl.
  - exact H.
  - apply Execute_rotate_instr_valid; apply H.
  - apply Execute_cnot_instr_valid; apply H.
  - apply Execute_swap_instr_valid; apply H.
  - apply Execute_measure_instr_valid; apply H.
  - apply IHinstr2; apply IHinstr1; apply H.
  - apply PProperties.fold_rec_nodep.
    + unfold ProgramState_valid; intros.
      apply PFacts.empty_mapsto_iff in H0.
      contradiction.
    + intros cstate_fold branch_fold acc Hmaps_fold Hacc_valid.
      destruct (eqb (CState_read n cstate_fold) b) eqn:Hcond.
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


Theorem Execute_valid: forall (program: InlinedProgram),
  ProgramState_valid (Execute program).
Proof.
  intros.
  unfold Execute.
  apply Execute_suppl_valid.
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

End PROGRAM.
