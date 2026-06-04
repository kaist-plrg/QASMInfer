Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Valid.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section SWAP_HELPER.

Fixpoint change_qbit_instr (chan_fn: nat -> nat) (instr: Instruction): Instruction :=
  match instr with
  | NopInstr => NopInstr
  | RotateInstr phi theta lambda qbit =>
    RotateInstr phi theta lambda (chan_fn qbit)
  | CnotInstr qbit1 qbit2 =>
    CnotInstr (chan_fn qbit1) (chan_fn qbit2)
  | SwapInstr qbit1 qbit2 =>
    SwapInstr (chan_fn qbit1) (chan_fn qbit2)
  | MeasureInstr qbit cbit =>
    MeasureInstr (chan_fn qbit) cbit
  | SeqInstr lst =>
    SeqInstr (List.map (change_qbit_instr chan_fn) lst)
  | IfInstr cbit cond instr =>
    IfInstr cbit cond (change_qbit_instr chan_fn instr)
  | ResetInstr qbit => ResetInstr (chan_fn qbit)
  end.

Definition swap_qbit_instr (qbit1 qbit2: nat) :=
  change_qbit_instr (swap_qbit qbit1 qbit2).

(* Property check of swap_qbit_instr *)
Lemma swap_swap_instr:
  forall (qbit1 qbit2: nat) (instr: Instruction),
  swap_qbit_instr qbit1 qbit2
  (swap_qbit_instr qbit1 qbit2 instr)
  = instr.
Proof.
  intros q1 q2 instr.
  induction instr using Instruction_ind'.
  all: unfold swap_qbit_instr in *.
  all: simpl.
  all: repeat rewrite swap_swap_qbit.
  all: try reflexivity.
  - f_equal. induction is.
    + reflexivity.
    + simpl. inversion H.
      rewrite H2, IHis.
      reflexivity. apply H3.
  - f_equal. apply IHinstr.
Qed.

Lemma swap_instr_symm:
  forall (qbit1 qbit2: nat),
  swap_qbit_instr qbit1 qbit2 =
  swap_qbit_instr qbit2 qbit1.
Proof.
  intros qbit1 qbit2.
  apply functional_extensionality.
  intro instr.
  unfold swap_qbit_instr.
  rewrite swap_qbit_symm.
  reflexivity.
Qed.

End SWAP_HELPER.

Section COMMUTE.

Variable nq: nat.

Lemma Instruction_valid_equiv_of_seqs_from_matrix:
  forall (lst1 lst2: list Instruction) (mlst1 mlst2: list (Matrix nq)),
  Matrix_of_list nq lst1 mlst1 ->
  Matrix_of_list nq lst2 mlst2 ->
  (exists lambda: R, List.fold_right (fun a b => b * a) mat_eye mlst1 =
  gphase lambda .* List.fold_right (fun a b => b * a) mat_eye mlst2) ->
  Instruction_valid_equiv nq
  qasm{ seq[ lst1 ] }
  qasm{ seq[ lst2 ] }.
Proof.
  intros lst1 lst2 mlst1 mlst2 H1 H2 [lambda Heq] ps Hvalid.
  rewrite (Matrix_of_list_id _ _ H1).
  rewrite (Matrix_of_list_id _ _ H2).
  rewrite Heq.
  intros cstate. f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  rewrite den_uop_gphase.
  reflexivity.
Qed.

Lemma Instruction_equiv_of_seqs_from_matrix:
  forall (lst1 lst2: list Instruction) (mlst1 mlst2: list (Matrix nq)),
  Matrix_of_list nq lst1 mlst1 ->
  Matrix_of_list nq lst2 mlst2 ->
  (exists lambda: R, List.fold_right (fun a b => b * a) mat_eye mlst1 =
  gphase lambda .* List.fold_right (fun a b => b * a) mat_eye mlst2) ->
  Instruction_equiv nq
  qasm{ seq[ lst1 ] }
  qasm{ seq[ lst2 ] }.
Proof.
  intros lst1 lst2 mlst1 mlst2 H1 H2 [lambda Heq].
  apply Instruction_valid_equiv_implies_equiv.
  eapply Instruction_valid_equiv_of_seqs_from_matrix.
  apply H1. apply H2.
  exists lambda. apply Heq.
Qed.

Corollary Instruction_equiv_of_seqs_from_matrix':
  forall (lst: list Instruction) (mlst: list (Matrix nq))
  (instr: Instruction) (mat: Matrix nq),
  Matrix_of_list nq lst mlst ->
  Matrix_of nq instr mat ->
  (exists lambda: R, List.fold_right (fun a b => b * a) mat_eye mlst =
  gphase lambda .* mat) ->
  Instruction_equiv nq
  qasm{ seq[ lst ] }
  qasm{ instr }.
Proof.
  intros lst mlst instr mat H1 H2 [lambda Heq] ps Hinv.
  rewrite (Matrix_of_list_id _ _ H1).
  rewrite Heq.
  intros cstate.
  rewrite H2.
  f_equal. f_equal.
  apply functional_extensionality.
  intros branch.
  rewrite den_uop_gphase.
  reflexivity.
Qed.

(* Qbit index validity : prevents index out of bounds *)
Definition Qbit_index_valid (qbit: nat): Prop :=
  nq > qbit.

Lemma Commute_X_Y (qbit: nat):
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ X qbit; Y qbit }
  qasm{ Y qbit; X qbit }.
Proof.
  intros H.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists (-PI)%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_X_Y__eq__Z, Gate_matrix_Y_X__eq__Z.
  repeat rewrite (mat_single_scale _ _ H).
  rewrite <- mat_scale_scale_comm. f_equal.
  unfold gphase. rewrite <- com_iexp_mul. f_equal.
  unfold PI. lra.
Qed.

Lemma Commute_Y_Z (qbit: nat):
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Y qbit; Z qbit }
  qasm{ Z qbit; Y qbit }.
Proof.
  intros H.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists (-PI)%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_Z_Y__eq__X, Gate_matrix_Y_Z__eq__X.
  repeat rewrite (mat_single_scale _ _ H).
  rewrite <- mat_scale_scale_comm. f_equal.
  unfold gphase. rewrite <- com_iexp_mul. f_equal.
  unfold PI. lra.
Qed.

Lemma Commute_Z_X (qbit: nat):
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Z qbit; X qbit }
  qasm{ X qbit; Z qbit }.
Proof.
  intros H.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists (-PI)%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_Z_X__eq__Y, Gate_matrix_X_Z__eq__Y.
  repeat rewrite (mat_single_scale _ _ H).
  rewrite <- mat_scale_scale_comm. f_equal.
  unfold gphase. rewrite <- com_iexp_mul. f_equal.
  unfold PI. lra.
Qed.

Lemma Commute_H_X (qbit: nat):
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; X qbit }
  qasm{ Z qbit; H qbit }.
Proof.
  intros H.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists 0%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_H_Z__eq__X_H.
  unfold gphase. com_simpl. mat_simpl.
Qed.

Lemma Commute_H_Y (qbit: nat):
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; Y qbit }
  qasm{ Y qbit; H qbit }.
Proof.
  intros H.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists (-PI)%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_H_Y__eq__Y_H.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  rewrite mat_scale_mul_assoc.
  rewrite <- mat_scale_scale_comm.
  unfold gphase. rewrite <- com_iexp_mul.
  replace (-PI + PI)%R with 0%R by lra.
  com_simpl.
Qed.

Lemma Commute_H_Z (qbit: nat):
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; Z qbit }
  qasm{ X qbit; H qbit }.
Proof.
  intros H.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists 0%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_H_X__eq__Z_H.
  unfold gphase. com_simpl. mat_simpl.
Qed.

Lemma Commute_single_indep (qbit1 qbit2: nat)
  (theta1 phi1 lambda1 theta2 phi2 lambda2: R):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  qbit1 <> qbit2 ->
  Instruction_equiv nq
  qasm{ U (theta1, phi1, lambda1) qbit1; U (theta2, phi2, lambda2) qbit2 }
  qasm{ U (theta2, phi2, lambda2) qbit2; U (theta1, phi1, lambda1) qbit1 }.
Proof.
  intros Hq1 Hq2 Hq.
  eapply Instruction_equiv_of_seqs_from_matrix; mat_of.
  exists 0%R. cbn [fold_right].
  unfold gphase. com_simpl. mat_simpl.
  symmetry.
  apply (mat_single_commute _ _ Hq1 Hq2 Hq).
Qed.

(** ============================================= *)
(** Proving swap commutes with every instructions *)

Lemma Commute_swap_symm (qbit1 qbit2: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ swap qbit1 qbit2 }
  qasm{ swap qbit2 qbit1 }.
Proof.
  intros Hq1 Hq2 ps Hvalid cstate.
  rewrite Matrix_of_swap, Matrix_of_swap.
  f_equal; f_equal.
  apply functional_extensionality.
  intros b.
  f_equal; f_equal.
  apply (mat_swap_symm Hq1 Hq2).
Qed.

Lemma Commute_swap_rot (qbit1 qbit2 target: nat) (theta phi lambda: R):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 qasm{ U (theta, phi, lambda) target })}
  qasm{ U (theta, phi, lambda) target; swap qbit1 qbit2 }.
Proof.
  intros Hq1 Hq2.
  unfold swap_qbit_instr. simpl.
  eapply Instruction_valid_equiv_of_seqs_from_matrix; mat_of.
  exists 0%R. unfold gphase. com_simpl. mat_simpl.
  apply (mat_swap_single_commute _ _ Hq1 Hq2).
Qed.

Lemma Commute_swap_cnot (qbit1 qbit2 control target: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 qasm{ cx control target})}
  qasm{ cx control target; swap qbit1 qbit2}.
Proof.
  intros Hq1 Hq2.
  unfold swap_qbit_instr. simpl.
  eapply Instruction_valid_equiv_of_seqs_from_matrix; mat_of.
  exists 0%R. unfold gphase. com_simpl. mat_simpl.
  apply (mat_swap_ctrl_commute _ _ _ Hq1 Hq2).
Qed.

Lemma Commute_swap_swap (qbit1 qbit2 control target: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 qasm{ swap control target})}
  qasm{ swap control target; swap qbit1 qbit2}.
Proof.
  intros Hq1 Hq2.
  unfold swap_qbit_instr. simpl.
  eapply Instruction_valid_equiv_of_seqs_from_matrix; mat_of.
  exists 0%R. unfold gphase. com_simpl. mat_simpl.
  apply (mat_swap_swap_commute _ _ Hq1 Hq2).
Qed.

Lemma den_prob_0_swap: 
  forall {qbit qbit1 qbit2} Q,
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  den_prob_0 (swap_qbit qbit1 qbit2 qbit)
  (den_uop (mat_swap qbit1 qbit2) Q) =
  @den_prob_0 nq qbit Q.
Proof.
  intros qbit qbit1 qbit2 Q Hq1 Hq2.
  unfold den_prob_0, den_prob.
  destruct (le_lt_dec nq qbit).
  - repeat rewrite mat_proj0_out_of_bounds.
    unfold den_uop.
    mat_simpl.
    rewrite mat_mul_trace_comm.
    rewrite mat_mul_assoc.
    rewrite (proj1 mat_swap_unitary).
    mat_simpl.
    apply l.
    apply (swap_qbit_out_of_bounds Hq1 Hq2 l).
  - repeat rewrite mat_proj0_eq_mat_single.
    unfold den_uop.
    rewrite mat_swap_Hermitian.
    rewrite mat_mul_trace_comm.
    repeat rewrite mat_mul_assoc.
    rewrite mat_swap_single_commute.
    rewrite mat_mul_trace_comm.
    repeat rewrite mat_mul_assoc.
    rewrite <- mat_swap_Hermitian at 1.
    rewrite (proj1 mat_swap_unitary).
    mat_simpl.
    rewrite mat_mul_trace_comm.
    reflexivity.
    apply Hq1.
    apply Hq2.
    apply l.
    apply (swap_qbit_bound Hq1 Hq2 l).
Qed. 

Lemma den_prob_1_swap: 
  forall {qbit qbit1 qbit2} Q,
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  den_prob_1 (swap_qbit qbit1 qbit2 qbit)
  (den_uop (mat_swap qbit1 qbit2) Q) =
  @den_prob_1 nq qbit Q.
Proof.
  intros qbit qbit1 qbit2 Q Hq1 Hq2.
  unfold den_prob_1, den_prob.
  destruct (le_lt_dec nq qbit).
  - repeat rewrite mat_proj1_out_of_bounds.
    unfold den_uop.
    mat_simpl.
    apply l.
    apply (swap_qbit_out_of_bounds Hq1 Hq2 l).
  - repeat rewrite mat_proj1_eq_mat_single.
    unfold den_uop.
    rewrite mat_swap_Hermitian.
    rewrite mat_mul_trace_comm.
    repeat rewrite mat_mul_assoc.
    rewrite mat_swap_single_commute.
    rewrite mat_mul_trace_comm.
    repeat rewrite mat_mul_assoc.
    rewrite <- mat_swap_Hermitian at 1.
    rewrite (proj1 mat_swap_unitary).
    mat_simpl.
    rewrite mat_mul_trace_comm.
    reflexivity.
    apply Hq1.
    apply Hq2.
    apply l.
    apply (swap_qbit_bound Hq1 Hq2 l).
Qed. 

Lemma den_measure_0_swap:
  forall {qbit qbit1 qbit2} Q,
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  den_measure_0 (swap_qbit qbit1 qbit2 qbit)
  (den_uop (mat_swap qbit1 qbit2) Q) =
  den_uop (mat_swap qbit1 qbit2)
  (@den_measure_0 nq qbit Q).
Proof.
  intros qbit qbit1 qbit2 Q Hq1 Hq2.
  unfold den_measure_0, den_measure.
  rewrite den_uop_scale.
  f_equal.
  - f_equal.
    change (den_prob (mat_proj0 nq qbit) Q) with (den_prob_0 qbit Q).
    rewrite <- (den_prob_0_swap _ Hq1 Hq2).
    reflexivity.
  - repeat rewrite den_uop_Hermitian_fold.
    repeat rewrite den_uop_den_uop.
    all: try apply (proj2 (mat_proj0_projection _ _)).
    rewrite (mat_swap_proj0_commute _ Hq1 Hq2).
    reflexivity.
Qed.

Lemma den_measure_1_swap:
  forall {qbit qbit1 qbit2} Q,
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  den_measure_1 (swap_qbit qbit1 qbit2 qbit)
  (den_uop (mat_swap qbit1 qbit2) Q) =
  den_uop (mat_swap qbit1 qbit2)
  (@den_measure_1 nq qbit Q).
Proof.
  intros qbit qbit1 qbit2 Q Hq1 Hq2.
  unfold den_measure_1, den_measure.
  rewrite den_uop_scale.
  f_equal.
  - f_equal.
    change (den_prob (mat_proj1 nq qbit) Q) with (den_prob_1 qbit Q).
    rewrite <- (den_prob_1_swap _ Hq1 Hq2).
    reflexivity.
  - repeat rewrite den_uop_Hermitian_fold.
    repeat rewrite den_uop_den_uop.
    all: try apply (proj2 (mat_proj1_projection _ _)).
    rewrite (mat_swap_proj1_commute _ Hq1 Hq2).
    reflexivity.
Qed.

Lemma Execute_measure_branch_swap :
  forall (qbit1 qbit2 qbit cbit: nat) (cstate: positive) (b: Branch nq),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Branch_valid nq b ->
  ProgramState_equiv nq
    (Execute_measure_instr_branch nq (swap_qbit qbit1 qbit2 qbit) cbit cstate
      (Execute_swap_instr_branch nq qbit1 qbit2 b))
    (Execute_swap_instr nq qbit1 qbit2
      (Execute_measure_instr_branch nq qbit cbit cstate b)).
Proof.
  intros qbit1 qbit2 qbit cbit cstate b Hq1 Hq2 Hb.
  unfold Execute_measure_instr_branch, Execute_swap_instr, Execute_swap_instr_branch.
  remember (CState_branch cbit cstate) as cstate'.
  destruct cstate' as [cstate0 cstate1]. simpl.
  rewrite (den_prob_0_swap _ Hq1 Hq2).
  rewrite (den_prob_1_swap _ Hq1 Hq2).
  destruct b; simpl.
  destruct (Rgt_dec (com_real (den_prob_0 qbit B_qstate)) 0);
  destruct (Rgt_dec (com_real (den_prob_1 qbit B_qstate)) 0);
  intros c; rewrite PFacts.map_o.
  - destruct (Pos.eq_dec cstate0 c) as [He|Hne].
    + repeat rewrite PFacts.add_eq_o; try apply He.
      simpl. f_equal; f_equal.
      rewrite (den_measure_0_swap _ Hq1 Hq2).
      reflexivity.
    + repeat rewrite PFacts.add_neq_o with (x := cstate0); try apply Hne.
      destruct (Pos.eq_dec cstate1 c) as [He'|Hne'].
      * repeat rewrite PFacts.add_eq_o; try apply He'.
        simpl. f_equal; f_equal.
        rewrite (den_measure_1_swap _ Hq1 Hq2).
        reflexivity.
      * repeat rewrite PFacts.add_neq_o; try apply Hne'.
        rewrite PFacts.empty_o.
        reflexivity.
  - destruct (Pos.eq_dec cstate0 c) as [He|Hne].
    + repeat rewrite PFacts.add_eq_o; try apply He.
      simpl. f_equal; f_equal.
      rewrite (den_measure_0_swap _ Hq1 Hq2).
      reflexivity.
    + repeat rewrite PFacts.add_neq_o; try apply Hne.
      rewrite PFacts.empty_o.
      reflexivity.
  - destruct (Pos.eq_dec cstate1 c) as [He|Hne].
    + repeat rewrite PFacts.add_eq_o; try apply He.
      simpl. f_equal; f_equal.
      rewrite (den_measure_1_swap _ Hq1 Hq2).
      reflexivity.
    + repeat rewrite PFacts.add_neq_o; try apply Hne.
      rewrite PFacts.empty_o.
      reflexivity.
  - rewrite PFacts.empty_o.
    reflexivity.
Qed.

Lemma Commute_swap_measure (qbit1 qbit2 qbit: nat) (cbit: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 qasm{ measure qbit -> cbit }) }
  qasm{ measure qbit -> cbit; swap qbit1 qbit2 }.
Proof.
  intros Hq1 Hq2.
  unfold swap_qbit_instr. simpl.
  intros ps.
  apply ProgramState_ind with (P:= fun ps0 =>
    ProgramState_valid nq ps0 ->
    ProgramState_equiv nq
    (Execute_suppl nq _ ps0) (Execute_suppl nq _ ps0)
  ).
  - intros m0 m1 Heq H Hm1.
    assert (Hm0: ProgramState_valid nq m0). {
      eapply ProgramState_valid_equal.
      apply Hm1.
      apply ProgramState_equiv_equivalence.
      apply Heq.
    }
    apply ProgramState_equiv_equivalence with (y :=
      Execute_suppl nq qasm{ swap qbit1 qbit2; measure (swap_qbit qbit1 qbit2 qbit) -> cbit } m0
    ). {
      apply Execute_suppl_Proper.
      apply ProgramState_equiv_equivalence. apply Heq.
    }
    apply ProgramState_equiv_equivalence with (y :=
      Execute_suppl nq qasm{ measure qbit -> cbit; swap qbit1 qbit2 } m0
    ). {
      apply H. apply Hm0.
    }
    apply Execute_suppl_Proper. apply Heq.
  - intros Hempty cstate. simpl.
    unfold Execute_measure_instr, Execute_swap_instr.
    rewrite PProperties.fold_Empty.
    rewrite PFacts.map_o.
    rewrite PProperties.fold_Empty.
    rewrite PFacts.empty_o. reflexivity.
    all: try apply ProgramState_equiv_equivalence.
    apply PositiveMap.empty_1.
    unfold PositiveMap.Empty.
    intros k b.
    rewrite PFacts.find_mapsto_iff.
    rewrite PFacts.map_o.
    rewrite PFacts.empty_o.
    simpl. intros H. discriminate H.
  - intros k b m Hnotin IH Hvalid. simpl.
    assert (Hb: Branch_valid nq b). {
      apply Hvalid with k.
      apply PFacts.find_mapsto_iff.
      apply PFacts.add_eq_o.
      reflexivity.
    }
    assert (Hm: ProgramState_valid nq m). {
      apply ProgramState_valid_add_inj with k b.
      apply Hnotin. apply Hvalid. 
    }

    set (fun k b => Execute_measure_instr_branch nq (swap_qbit qbit1 qbit2 qbit) cbit k b) as F.
    set (fun k b => Execute_measure_instr_branch nq qbit cbit k b) as F'.

    setoid_rewrite ValidProgramState_rewrite.
    unfold Execute_measure_instr, Execute_swap_instr.

    setoid_rewrite construct_foldF.
    setoid_rewrite ValidProgramState_construct_map_rewrite with
      (g := Execute_swap_instr_branch nq qbit1 qbit2).
    setoid_rewrite construct_foldF.
    setoid_rewrite ValidProgramState_construct_add_rewrite with
      (Hb := Hb) (Hm := Hm).
    
    setoid_rewrite ValidProgramState_map_add.
    setoid_rewrite ValidProgramState_fold_VstepF_add.

    cbv [VstepF VF].
    setoid_rewrite ValidProgramState_map_swap_merge.
    apply ValidProgramState_merge_Proper.

    + setoid_rewrite <- ValidProgramState_construct_map_rewrite.
      setoid_rewrite <- construct_foldF.
      setoid_rewrite <- ValidProgramState_construct_map_rewrite.
      setoid_rewrite <- ValidProgramState_rewrite.
      apply IH. apply Hm.
    + setoid_rewrite <- ValidProgramState_construct_map_rewrite.
      setoid_rewrite <- ValidProgramState_rewrite.
      apply Execute_measure_branch_swap.
      all: assumption.
    + intros ps1 ps2 Hps1 Hps2.
      apply Execute_swap_instr_map_merge.
      all: assumption.
    + rewrite PFacts.not_find_in_iff.
      rewrite <- ValidProgramState_construct_map_rewrite.
      rewrite <- PFacts.not_find_in_iff.
      rewrite ValidProgramState_in_iff.
      rewrite PFacts.not_find_in_iff.
      rewrite ValidProgramState_proj_construct.
      rewrite PFacts.map_o.
      rewrite PFacts.not_find_in_iff in Hnotin.
      rewrite Hnotin. reflexivity.
    + rewrite ValidProgramState_in_iff.
      rewrite PFacts.not_find_in_iff.
      rewrite ValidProgramState_proj_construct.
      rewrite <- PFacts.not_find_in_iff.
      apply Hnotin.
    Unshelve. (* Resolve validity setoid_rewrite made *)
    all: try apply Execute_measure_instr_valid.
    all: try apply Execute_swap_instr_valid.
    all: try apply Execute_measure_instr_valid.
    all: try apply Hvalid.
    all: try apply ProgramState_empty_valid.
    all: try apply Hm.
    all: try apply Execute_measure_instr_branch_valid.
    all: try apply Hb.
    all: intros b0 [Hvalid0 Hprob0].
    all: unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
    all: split.
    all: try apply den_valid_uop.
    all: try apply mat_swap_unitary.
    all: assumption.
Qed.

Lemma Commute_swap_if (qbit1 qbit2 cbit: nat) (cond: bool) (instr: Instruction):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 instr) }
  qasm{ instr; swap qbit1 qbit2 } ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 (IfInstr cbit cond instr)) }
  qasm{ $(IfInstr cbit cond instr); swap qbit1 qbit2 }.
Proof.
  intros Hq1 Hq2 Hinstr.
  unfold swap_qbit_instr, Instruction_valid_equiv in *.
  intros ps.
  apply ProgramState_ind with (P:= fun ps0 =>
    ProgramState_valid nq ps0 ->
    ProgramState_equiv nq
    (Execute_suppl nq _ ps0) (Execute_suppl nq _ ps0)
  ).
  - intros m0 m1 Heq H Hm1.
    assert (Hm0: ProgramState_valid nq m0). {
      eapply ProgramState_valid_equal.
      apply Hm1.
      apply ProgramState_equiv_equivalence.
      apply Heq.
    }
    apply ProgramState_equiv_equivalence with (y :=
      Execute_suppl nq qasm{ swap qbit1 qbit2; $(change_qbit_instr (swap_qbit qbit1 qbit2) (IfInstr cbit cond instr)) } m0
    ). {
      apply Execute_suppl_Proper.
      apply ProgramState_equiv_equivalence. apply Heq.
    }
    apply ProgramState_equiv_equivalence with (y :=
      Execute_suppl nq qasm{ $(IfInstr cbit cond instr); swap qbit1 qbit2 } m0
    ). {
      apply H. apply Hm0.
    }
    apply Execute_suppl_Proper. apply Heq.
  - intros Hempty cstate. simpl.
    unfold Execute_swap_instr.
    rewrite PProperties.fold_Empty.
    rewrite PFacts.map_o.
    rewrite PProperties.fold_Empty.
    rewrite PFacts.empty_o. reflexivity.
    all: try apply ProgramState_equiv_equivalence.
    apply PositiveMap.empty_1.
    unfold PositiveMap.Empty.
    intros k b.
    rewrite PFacts.find_mapsto_iff.
    rewrite PFacts.map_o.
    rewrite PFacts.empty_o.
    simpl. intros H. discriminate H.
  - intros k b m Hnotin IH Hvalid.
    simpl. unfold Execute_swap_instr.
    assert (Hb: Branch_valid nq b). {
      apply Hvalid with k.
      apply PFacts.find_mapsto_iff.
      apply PFacts.add_eq_o.
      reflexivity.
    }
    assert (Hm: ProgramState_valid nq m). {
      apply ProgramState_valid_add_inj with k b.
      apply Hnotin. apply Hvalid. 
    }

    set (F :=
      fun (cstate : PositiveMap.key) (b0 : Branch nq) =>
        if eqb (CState_read cbit cstate) cond
        then
          Execute_suppl nq
            (change_qbit_instr (swap_qbit qbit1 qbit2) instr)
            (PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq)))
        else
          PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq))).

    change
      (fun (cstate : PositiveMap.key)
          (b0 : Branch nq)
          (acc : ProgramState nq) =>
        ProgramState_merge nq acc
          (if eqb (CState_read cbit cstate) cond
            then
              Execute_suppl nq
                (change_qbit_instr (swap_qbit qbit1 qbit2) instr)
                (PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq)))
            else
              PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq))))
    with
      (stepF nq F).
    
    set (F' :=
      fun (cstate : PositiveMap.key) (b0 : Branch nq) =>
        if eqb (CState_read cbit cstate) cond
        then
          Execute_suppl nq instr
            (PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq)))
        else
          PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq))).

    change
      (fun (cstate : PositiveMap.key)
          (b0 : Branch nq)
          (acc : ProgramState nq) =>
        ProgramState_merge nq acc
          (if eqb (CState_read cbit cstate) cond
            then
              Execute_suppl nq instr
                (PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq)))
            else
              PositiveMap.add cstate b0 (PositiveMap.empty (Branch nq))))
    with
      (stepF nq F').
    
    assert (F_valid: forall k b, Branch_valid nq b -> ProgramState_valid nq (F k b)). {
      intros k' b' Hb'. unfold F.
      destruct (eqb (CState_read cbit k') cond);
      try apply Execute_suppl_valid.
      all: apply ProgramState_singleton_valid.
      all: apply Hb'.
    }
    assert (F'_valid: forall k b, Branch_valid nq b -> ProgramState_valid nq (F' k b)). {
      intros k' b' Hb'. unfold F'.
      destruct (eqb (CState_read cbit k') cond);
      try apply Execute_suppl_valid.
      all: apply ProgramState_singleton_valid.
      all: apply Hb'.
    }

    setoid_rewrite ValidProgramState_rewrite.
    setoid_rewrite ValidProgramState_construct_map_rewrite.
    setoid_rewrite construct_foldF.
    setoid_rewrite ValidProgramState_construct_map_rewrite.
    setoid_rewrite ValidProgramState_construct_add_rewrite.

    setoid_rewrite ValidProgramState_map_add.
    setoid_rewrite ValidProgramState_fold_VstepF_add.

    cbv [VstepF VF].
    setoid_rewrite ValidProgramState_map_swap_merge.
    apply ValidProgramState_merge_Proper.

    + setoid_rewrite <- ValidProgramState_construct_map_rewrite.
      setoid_rewrite <- construct_foldF.
      setoid_rewrite <- ValidProgramState_construct_map_rewrite.
      setoid_rewrite <- ValidProgramState_rewrite.
      apply IH. apply Hm.
    + setoid_rewrite <- ValidProgramState_construct_map_rewrite.
      setoid_rewrite <- ValidProgramState_rewrite.
      simpl. unfold F, F'.
      destruct (eqb (CState_read cbit k) cond); simpl.
      * apply ProgramState_equiv_equivalence with (y:=
          Execute_suppl nq (change_qbit_instr (swap_qbit qbit1 qbit2) instr)
          (PositiveMap.map (Execute_swap_instr_branch nq qbit1 qbit2)
          (PositiveMap.add k b (PositiveMap.empty (Branch nq))))
        ). {
          apply Execute_suppl_Proper.
          intro y.
          rewrite PFacts.map_o.
          destruct (PositiveMap.E.eq_dec k y).
          - subst. repeat rewrite PFacts.add_eq_o.
            all: reflexivity.
          - repeat rewrite PFacts.add_neq_o.
            rewrite PFacts.empty_o. reflexivity.
            all: assumption.
        }
        setoid_rewrite Execute_suppl_seq in Hinstr.
        simpl in Hinstr.
        apply Hinstr.
        apply ProgramState_singleton_valid.
        apply Hb.
      * intro y.
        rewrite PFacts.map_o.
        destruct (PositiveMap.E.eq_dec k y).
        subst. repeat rewrite PFacts.add_eq_o.
        all: try reflexivity.
        repeat rewrite PFacts.add_neq_o.
        rewrite PFacts.empty_o. reflexivity.
        all: assumption.
    + intros ps1 ps2 Hps1 Hps2.
      apply Execute_swap_instr_map_merge.
      all: assumption.
    + rewrite PFacts.not_find_in_iff.
      rewrite <- ValidProgramState_construct_map_rewrite.
      rewrite <- PFacts.not_find_in_iff.
      rewrite ValidProgramState_in_iff.
      rewrite PFacts.not_find_in_iff.
      rewrite ValidProgramState_proj_construct.
      rewrite PFacts.map_o.
      rewrite PFacts.not_find_in_iff in Hnotin.
      rewrite Hnotin. reflexivity.
    + rewrite ValidProgramState_in_iff.
      rewrite PFacts.not_find_in_iff.
      rewrite ValidProgramState_proj_construct.
      rewrite <- PFacts.not_find_in_iff.
      apply Hnotin.
    Unshelve. (* Resolve validity setoid_rewrite made *)
    all: simpl.
    all: try apply fold_stepF_valid.
    all: try apply Execute_swap_instr_valid.
    all: try apply fold_stepF_valid.
    all: try apply Hvalid.
    all: try apply ProgramState_empty_valid.
    all: try apply Hm.
    all: try apply F_valid.
    all: try apply F'_valid.
    all: try apply Hb.
    all: intros b0 [Hvalid0 Hprob0].
    all: unfold Execute_rotate_instr_branch, Branch_valid in *; simpl.
    all: split.
    all: try apply den_valid_uop.
    all: try apply mat_swap_unitary.
    all: assumption.
Qed.

Lemma Commute_swap_reset (qbit1 qbit2 qbit: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 qasm{ reset qbit }) }
  qasm{ reset qbit; swap qbit1 qbit2 }.
Proof.
  intros Hq1 Hq2.
  unfold swap_qbit_instr. simpl.
  intros ps Hvalid. simpl.
  unfold Execute_reset_instr, Execute_swap_instr.
  intros cstate.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl; try reflexivity.
  f_equal.
  unfold Execute_reset_instr_branch, Execute_swap_instr_branch.
  destruct b; simpl.
  f_equal.
  unfold den_reset.
  rewrite den_uop_add.
  f_equal.
  - repeat rewrite den_uop_Hermitian_fold.
    repeat rewrite den_uop_den_uop.
    all: try apply (proj2 (mat_proj0_projection _ _)).
    rewrite (mat_swap_proj0_commute _ Hq1 Hq2).
    reflexivity.
  - repeat rewrite den_uop_Hermitian_fold.
    repeat rewrite den_uop_den_uop.
    all: try apply (proj2 (mat_proj1_projection _ _)).
    f_equal.
    rewrite <- mat_swap_single_commute.
    repeat rewrite <- mat_mul_assoc. f_equal.
    all: try assumption.
    rewrite (mat_swap_proj1_commute _ Hq1 Hq2).
    reflexivity.
Qed.

Lemma Commute_swap_instr:
  forall (qbit1 qbit2: nat) (instr: Instruction),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 instr) }
  qasm{ instr; swap qbit1 qbit2 }.
Proof.
  intros qbit1 qbit2 instr Hq1 Hq2.
  apply Instruction_valid_equiv_implies_equiv.
  induction instr using Instruction_ind'.
  - intros ps Hvalid. simpl. reflexivity.
  - apply Commute_swap_rot.
    all: assumption.
  - apply Commute_swap_cnot.
    all: assumption.
  - apply Commute_swap_swap.
    all: assumption.
  - apply Commute_swap_measure.
    all: assumption.
  - induction is.
    + apply Instruction_valid_equiv_equivalence.
    + inversion H. subst.
      apply IHis in H3.
      unfold swap_qbit_instr. simpl.
      setoid_rewrite Instruction_valid_equiv_Seq_list_eq.
      change ((fix app (l m : list Instruction) {struct l} : list Instruction :=
        match l with
        | [] => m
        | a0 :: l1 => a0 :: app l1 m
        end) is [qasm{ swap qbit1 qbit2}])
      with (is ++ [qasm{ swap qbit1 qbit2}]).
      setoid_rewrite Instruction_valid_equiv_Seq_list_list_eq.
      setoid_rewrite Instruction_valid_equiv_Seq_singleton.
      setoid_rewrite <- H3.
      setoid_rewrite Instruction_valid_equiv_assoc.
      setoid_rewrite <- H2.
      setoid_reflexivity.
  - apply Commute_swap_if.
    all: assumption.
  - apply Commute_swap_reset.
    all: assumption.
Qed.

End COMMUTE.
