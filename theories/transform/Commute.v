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

Definition change_qbit (qbit1 qbit2: nat) (tq: nat): nat :=
  match Nat.eq_dec tq qbit1 with
  | left _ => qbit2
  | right _ =>
      match Nat.eq_dec tq qbit2 with
      | left _ => qbit1
      | right _ => tq
      end
  end.

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
  change_qbit_instr (change_qbit qbit1 qbit2).

(* Sanity check of swap_qbit_instr *)
Lemma swap_swap_qbit:
  forall (qbit1 qbit2: nat) (tq: nat),
  change_qbit qbit1 qbit2
  (change_qbit qbit1 qbit2 tq) = tq.
Proof.
  intros q1 q2 tq.
  unfold change_qbit.
  destruct (Nat.eq_dec tq q1) as [H1|H1].
  - destruct (Nat.eq_dec q2 q1) as [H2|H2]; try lia.
    destruct (Nat.eq_dec q2 q2) as [H3|H3]; try lia.
  - destruct (Nat.eq_dec tq q2) as [H2|H2].
    + destruct (Nat.eq_dec q1 q1) as [H3|H3]; try lia.
    + destruct (Nat.eq_dec tq q1) as [H3|H3]; try lia.
      destruct (Nat.eq_dec tq q2) as [H4|H4]; try lia.
Qed.

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

Lemma swap_qbit_symm:
  forall (qbit1 qbit2: nat),
    change_qbit qbit1 qbit2 =
    change_qbit qbit2 qbit1.
Proof.
  intros qbit1 qbit2.
  apply functional_extensionality.
  intros tq.
  unfold change_qbit.
  destruct (Nat.eq_dec tq qbit1) as [H1|H1].
  - destruct (Nat.eq_dec tq qbit2) as [H2|H2]; try lia.
  - reflexivity.
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

Lemma QState_transform_equality:
  forall (lst1 lst2: list Instruction) (mlst1 mlst2: list (Matrix nq)),
  Matrix_of_list nq lst1 mlst1 ->
  Matrix_of_list nq lst2 mlst2 ->
  (exists lambda: R, List.fold_right (fun a b => b * a) mat_eye mlst1 =
  gphase lambda .* List.fold_right (fun a b => b * a) mat_eye mlst2) ->
  Instruction_equiv nq
  qasm{ seq[ lst1 ] }
  qasm{ seq[ lst2 ] }.
Proof.
  intros lst1 lst2 mlst1 mlst2 H1 H2 [lambda Heq] ps Hinv.
  rewrite (Matrix_of_list_id _ _ H1).
  rewrite (Matrix_of_list_id _ _ H2).
  rewrite Heq.
  intros cstate. f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  rewrite den_uop_gphase.
  reflexivity.
Qed.

Corollary QState_transform_equality':
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
  eapply QState_transform_equality; mat_of_single H.
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
  eapply QState_transform_equality; mat_of_single H.
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
  eapply QState_transform_equality; mat_of_single H.
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
  eapply QState_transform_equality; mat_of_single H.
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
  eapply QState_transform_equality; mat_of_single H.
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
  eapply QState_transform_equality; mat_of_single H.
  exists 0%R. cbn [fold_right].
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite Gate_matrix_H_X__eq__Z_H.
  unfold gphase. com_simpl. mat_simpl.
Qed.

Lemma Commute_single_indep (qbit1 qbit2: nat)
  (a1 b1 c1 a2 b2 c2: R):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  qbit1 <> qbit2 ->
  Instruction_equiv nq
  qasm{ U (a1, b1, c1) qbit1; U (a2, b2, c2) qbit2 }
  qasm{ U (a2, b2, c2) qbit2; U (a1, b1, c1) qbit1 }.
Proof.
  intros Hq1 Hq2 Hq ps Hvalid cstate.
  simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); try reflexivity.
  simpl. f_equal.
  unfold Execute_rotate_instr_branch.
  destruct b; simpl. f_equal.
  repeat rewrite den_uop_den_uop.
  f_equal.
  rewrite (mat_single_commute _ _ Hq1 Hq2 Hq).
  reflexivity.
Qed.

Lemma Commute_swap_symm (qbit1 qbit2: nat):
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ swap qbit1 qbit2 }
  qasm{ swap qbit2 qbit1 }.
Proof.
  intros Hq1 Hq2 ps Hvalid cstate.
  rewrite (Matrix_of_swap _ Hq1 Hq2).
  rewrite (Matrix_of_swap _ Hq2 Hq1).
  f_equal; f_equal.
  apply functional_extensionality.
  intros b.
  f_equal; f_equal.
  apply (mat_swap_symm Hq1 Hq2).
Qed.


End COMMUTE.