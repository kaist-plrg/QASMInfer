Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.

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

Lemma Execute_measure_branch_swap :
  forall (qbit1 qbit2 cbit: nat) (cstate: positive) (b: Branch nq),
  ProgramState_equiv nq
    (Execute_measure_instr_branch nq qbit2 cbit cstate
      (Execute_swap_instr_branch nq qbit1 qbit2 b))
    (Execute_swap_instr nq qbit1 qbit2
      (Execute_measure_instr_branch nq qbit1 cbit cstate b)).
Proof.
  intros qbit1 qbit2 cbit cstate b.
  unfold Execute_measure_instr_branch, Execute_swap_instr_branch, Execute_swap_instr.
  remember (CState_branch cbit cstate) as k.
  destruct k as [cstate0 cstate1].
  destruct b. simpl.
Admitted.

Lemma Commute_swap_measure (qbit1 qbit2 qbit: nat) (cbit: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_valid_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 qasm{ measure qbit -> cbit }) }
  qasm{ measure qbit -> cbit; swap qbit1 qbit2 }.
Proof.
  intros Hq1 Hq2.
  unfold swap_qbit_instr. simpl.
  intros ps Hvalid. simpl.
  unfold Execute_measure_instr, Execute_swap_instr.
  rewrite PositiveMap_fold_map.
  apply PProperties.fold_rec_weak.
  - intros m0 m0' a Heq Ha.
    rewrite Ha.
    eapply Execute_swap_instr_Proper.
    apply PositiveMap_fold_Proper_gen.
    + intros cstate branch ps1 ps2 Hps.
      apply ProgramState_merge_Proper.
      apply Hps. apply ProgramState_equiv_equivalence.
    + apply Heq.
    + apply ProgramState_equiv_equivalence.
  - intros cstate.
    rewrite PProperties.fold_Empty.
    rewrite PFacts.empty_o.
    rewrite PFacts.map_o.
    rewrite PFacts.empty_o.
    reflexivity.
    apply ProgramState_equiv_equivalence.
    apply PositiveMap.empty_1.
  - intros cstate' branch' ps' m Hnotin IH.
    rewrite PProperties.fold_add.
    + shelve.
    + apply ProgramState_equiv_equivalence.
    + intros c1 c2 Hc b1 b2 Hb ps1 ps2 Hps.
      rewrite Hc, Hb.
      apply ProgramState_merge_Proper.
      apply Hps. apply ProgramState_equiv_equivalence.
    + unfold PProperties.transpose_neqkey.
      intros k k' e e' a Hne. shelve.
    + apply Hnotin.
Admitted.

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
  - shelve. (* IF *)
  - shelve. (* RESET *)
Admitted.

End COMMUTE.
