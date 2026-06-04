Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Commute.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section TRANSFORM.

Variable nq: nat.

(* Qbit index validity : prevents index out of bounds *)
Definition Qbit_index_valid (qbit: nat): Prop :=
  nq > qbit.

Lemma Transform_I: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ I qbit }
  NopInstr.
Proof.
  intros qbit H ps Hinv cstate.
  rewrite Matrix_of_I.
  cbn [Execute_suppl].
  rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); cbn [Datatypes.option_map].
  - f_equal.
    destruct b. f_equal.
    unfold den_uop.
    rewrite mat_eye_conjtrans.
    mat_simpl.
  - reflexivity.
Qed.

Lemma Transform_X_X: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ X qbit; X qbit }
  qasm{ I qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  rewrite mat_single_factorized.
  rewrite mat_Hermitian_unitary__involutory.
  apply mat_single_eye.
  apply Gate_X_matrix_Hermitian.
  apply Gate_X_matrix_unitary.
Qed.

Lemma Transform_Y_Y: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Y qbit; Y qbit }
  qasm{ I qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  rewrite mat_single_factorized.
  rewrite mat_Hermitian_unitary__involutory.
  apply mat_single_eye.
  apply Gate_Y_matrix_Hermitian.
  apply Gate_Y_matrix_unitary.
Qed.

Lemma Transform_Z_Z: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Z qbit; Z qbit }
  qasm{ I qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  rewrite mat_single_factorized.
  rewrite mat_Hermitian_unitary__involutory.
  apply mat_single_eye.
  apply Gate_Z_matrix_Hermitian.
  apply Gate_Z_matrix_unitary.
Qed.

Lemma Transform_H_H: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; H qbit }
  qasm{ I qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  rewrite mat_single_factorized.
  rewrite mat_Hermitian_unitary__involutory.
  apply mat_single_eye.
  apply Gate_H_matrix_Hermitian.
  apply Gate_H_matrix_unitary.
Qed.

Lemma Transform_P_P: forall (qbit: nat) (l1 l2: R),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ P (l1) qbit; P (l2) qbit }
  qasm{ P ((l1 + l2)%R) qbit }.
Proof.
  intros qbit l1 l2 H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  rewrite mat_single_factorized.
  f_equal.
  rewrite Gate_P_matrix_mul, Rplus_comm.
  reflexivity.
Qed.

Lemma Transform_P_periodic: forall (qbit: nat) (l: R),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ P (l) qbit }
  qasm{ P ((l + 2*PI)%R) qbit }.
Proof.
  intros qbit l H ps Hinv cstate.
  simpl.
  unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find cstate ps); simpl.
  - f_equal.
    unfold Execute_rotate_instr_branch.
    f_equal.
    rewrite Gate_P_matrix_periodic.
    rewrite (mat_single_scale _ _ H).
    apply den_uop_gphase.
  - reflexivity. 
Qed.

Corollary Transform_S_S: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ S qbit; S qbit }
  qasm{ Z qbit }.
Proof.
  intros qbit H.
  unfold Gate_S, Gate_Z.
  replace PI with (PI2 + PI2)%R by (unfold PI; field).
  apply (Transform_P_P qbit _ _ H).
Qed.

Corollary Transform_S_Sdg: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ S qbit; Sdg qbit }
  qasm{ I qbit }.
Proof.
  intros qbit H.
  unfold Gate_S, Gate_Sdg, Gate_I.
  replace 0%R with (PI2 + (- PI2))%R by field.
  apply (Transform_P_P qbit _ _ H).
Qed.

Corollary Transform_Sdg_S: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Sdg qbit; S qbit }
  qasm{ I qbit }.
Proof.
  intros qbit H.
  unfold Gate_S, Gate_Sdg, Gate_I.
  replace 0%R with ((- PI2) + PI2)%R by field.
  apply (Transform_P_P qbit _ _ H).
Qed.

Corollary Transform_Sdg_Sdg: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Sdg qbit; Sdg qbit }
  qasm{ Z qbit }.
Proof.
  intros qbit H.
  unfold Gate_S, Gate_Sdg, Gate_Z.
  apply Instruction_equiv_equivalence with (y := Gate_P ((-PI2) + (-PI2)) qbit).
  - apply (Transform_P_P qbit _ _ H).
  - replace PI with ((-PI) + 2*PI)%R by field.
    replace ((- PI2) + (-PI2))%R with (-PI)%R by (unfold PI; field).
    apply (Transform_P_periodic qbit _ H).
Qed.

Lemma Transform_X_Y: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ X qbit; Y qbit }
  qasm{ Z qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists (-PI2)%R.
  mat_simpl.
  rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_Y_X__eq__Z.
Qed.

Lemma Transform_Y_X: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Y qbit; X qbit }
  qasm{ Z qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists (PI2)%R.
  mat_simpl.
  rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_X_Y__eq__Z.
Qed.

Lemma Transform_Y_Z: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Y qbit; Z qbit }
  qasm{ X qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists (-PI2)%R.
  mat_simpl.
  rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_Z_Y__eq__X.
Qed.

Lemma Transform_Z_Y: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Z qbit; Y qbit }
  qasm{ X qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists (PI2)%R.
  mat_simpl.
  rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_Y_Z__eq__X.
Qed.

Lemma Transform_Z_X: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ Z qbit; X qbit }
  qasm{ Y qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists (-PI2)%R.
  mat_simpl.
  rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_X_Z__eq__Y.
Qed.

Lemma Transform_X_Z: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ X qbit; Z qbit }
  qasm{ Y qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists PI2%R.
  mat_simpl.
  rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_Z_X__eq__Y.
Qed.

Lemma Transform_H_X_H: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; X qbit; H qbit }
  qasm{ Z qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  repeat rewrite mat_single_factorized.
  f_equal.
  apply Gate_matrix_H_X_H__eq__Z.
Qed.

Lemma Transform_H_Y_H: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; Y qbit; H qbit }
  qasm{ Y qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists (PI)%R.
  mat_simpl.
  repeat rewrite mat_single_factorized.
  rewrite <- (mat_single_scale _ _ H).
  f_equal.
  apply Gate_matrix_H_Y_H__eq__Y.
Qed.

Lemma Transform_H_Z_H: forall (qbit: nat),
  Qbit_index_valid qbit ->
  Instruction_equiv nq
  qasm{ H qbit; Z qbit; H qbit }
  qasm{ X qbit }.
Proof.
  intros qbit H.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  repeat rewrite mat_single_factorized.
  f_equal.
  apply Gate_matrix_H_Z_H__eq__X.
Qed.

Lemma Transform_swap_swap: forall (qbit1 qbit2: nat),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ swap qbit1 qbit2; swap qbit1 qbit2 }
  qasm{ I qbit1 }.
Proof.
  intros qbit1 qbit2 Hq1 Hq2.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  apply mat_Hermitian_unitary__involutory.
  apply mat_swap_Hermitian.
  apply mat_swap_unitary.
Qed.

Lemma Transform_cnot_cnot: forall (qbit1 qbit2: nat),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ cx qbit1 qbit2; cx qbit1 qbit2 }
  qasm{ I qbit1 }.
Proof.
  intros qbit1 qbit2 Hq1 Hq2.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  apply mat_Hermitian_unitary__involutory.
  apply mat_cnot_Hermitian.
  apply mat_cnot_unitary.
Qed.

Lemma Transform_3cnot_swap: forall (qbit1 qbit2: nat),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ cx qbit1 qbit2; cx qbit2 qbit1; cx qbit1 qbit2 }
  qasm{ swap qbit1 qbit2 }.
Proof.
  intros qbit1 qbit2 Hq1 Hq2.
  eapply Instruction_equiv_of_seqs_from_matrix'; mat_of.
  cbn [fold_right]. exists 0%R.
  unfold gphase. com_simpl. mat_simpl.
  apply mat_3cnot_swap.
Qed.

Lemma Transform_swap_swap_insert:
  forall (qbit1 qbit2: nat) (instr: Instruction),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 instr); swap qbit1 qbit2 }
  qasm{ instr }.
Proof.
  intros qbit1 qbit2 instr Hq1 Hq2.
  setoid_rewrite Instruction_equiv_assoc.
  setoid_rewrite Commute_swap_instr.
  setoid_rewrite <- Instruction_equiv_assoc.
  setoid_rewrite Transform_swap_swap.
  setoid_rewrite Transform_I.
  setoid_rewrite Instruction_equiv_nop_end.
  setoid_reflexivity.
  all: assumption.
Qed.

Corollary Transform_swap_insert:
  forall (qbit1 qbit2: nat) (instr: Instruction),
  Qbit_index_valid qbit1 ->
  Qbit_index_valid qbit2 ->
  Instruction_behavioral_equiv nq
  qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 instr) }
  qasm{ instr }.
Proof.
  intros qbit1 qbit2 instr Hq1 Hq2.
  apply Instruction_behavioral_equiv_equivalence with (y:=qasm{ swap qbit1 qbit2; $(swap_qbit_instr qbit1 qbit2 instr); swap qbit1 qbit2 }).
  - apply Instruction_behavioral_equiv_rewrite_end.
    apply Instruction_behavioral_equiv_equivalence with (y:=qasm{ $(swap_qbit_instr qbit1 qbit2 instr); nop }).
    + apply Instruction_equiv_implies_behavioral_equiv.
      rewrite Instruction_equiv_nop_end.
      reflexivity.
    + apply Instruction_behavioral_equiv_rewrite_end.
      intros ps Hinv cstate. simpl.
      unfold Execute_swap_instr.
      repeat rewrite PFacts.map_o.
      destruct (PositiveMap.find cstate ps).
      * destruct b. reflexivity.
      * reflexivity.
  - apply Instruction_equiv_implies_behavioral_equiv.
    apply Transform_swap_swap_insert.
    all: assumption.
Qed.

(* Behavioral equivalence - insert quantum operation after all operations *)


End TRANSFORM.
