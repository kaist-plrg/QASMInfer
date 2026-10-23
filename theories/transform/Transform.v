Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Valid.
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
    angle_to_R_simpl.
    rewrite Gate_P_matrix_periodic.
    rewrite (mat_single_scale _ _ H).
    apply den_uop_gphase.
  - reflexivity. 
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

Lemma Transform_double_if:
  forall (cbit: nat) (cond: bool) (instr: Instruction),
  Instruction_equiv nq
  (IfInstr cbit cond (IfInstr cbit cond instr))
  (IfInstr cbit cond instr).
Proof.
  intros cbit cond instr ps.
  apply ProgramState_ind with (m:=ps).
  - intros m0 m1 Heq H Hm1.
    etransitivity. {
      apply Execute_suppl_Proper.
      symmetry. apply Heq.
    }
    etransitivity. {
      apply H.
      apply ProgramState_valid_equal with m1.
      apply Hm1.
      symmetry. apply Heq.
    }
    apply Execute_suppl_Proper. apply Heq.
  - reflexivity.
  - intros k b m Hnotin H Hvalid. simpl.
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

    rewrite ProgramState_fold_stepF_add.
    rewrite ProgramState_fold_stepF_add.
    unfold fold_step at 1 5.
    apply ProgramState_merge_Proper.
    all: try apply Execute_if_instr_branch_valid.
    all: try assumption.
    all: try apply ProgramState_empty_valid.
    + apply H. apply Hm.
    + destruct (eqb (CState_read cbit k) cond) eqn:E; try reflexivity.
      rewrite ProgramState_fold_stepF_add.
      all: try assumption.
      all: try apply ProgramState_empty_valid.
      * cbv [fold_step].
        rewrite <- ProgramState_merge_empty_l.
        rewrite E. reflexivity.
      * apply Execute_if_instr_branch_valid.
      * rewrite PFacts.not_find_in_iff.
        apply PFacts.empty_o.
    + intros k0 b0 Hb0.
      destruct (eqb (CState_read cbit k0) cond).
      apply ProgramState_fold_valid.
      apply ProgramState_singleton_valid. apply Hb0.
      apply ProgramState_empty_valid.
      intros k1 b1 ps' Hb1 Hps'.
      apply ProgramState_merge_valid. apply Hps'.
      apply Execute_if_instr_branch_valid. apply Hb1.
      apply ProgramState_singleton_valid. apply Hb0.
Qed.

Corollary Transform_double_if_true:
  forall (cbit: nat) (instr: Instruction),
  Instruction_equiv nq
  qasm{ if (cbit == 1) if (cbit == 1) instr }
  qasm{ if (cbit == 1) instr }.
Proof.
  intros; apply Transform_double_if.
Qed.

Corollary Transform_double_if_false:
  forall (cbit: nat) (instr: Instruction),
  Instruction_equiv nq
  qasm{ if (cbit == 0) if (cbit == 0) instr }
  qasm{ if (cbit == 0) instr }.
Proof.
  intros; apply Transform_double_if.
Qed.

Lemma Transform_double_if_nop:
  forall (cbit: nat) (cond: bool) (instr: Instruction),
  Instruction_equiv nq
  (IfInstr cbit cond (IfInstr cbit (negb cond) instr))
  NopInstr.
Proof.
  intros cbit cond instr ps.
  apply ProgramState_ind with (m:=ps).
  - intros m0 m1 Heq H Hm1.
    etransitivity. {
      apply Execute_suppl_Proper.
      symmetry. apply Heq.
    }
    etransitivity. {
      apply H.
      apply ProgramState_valid_equal with m1.
      apply Hm1.
      symmetry. apply Heq.
    }
    apply Execute_suppl_Proper. apply Heq.
  - reflexivity.
  - intros k b m Hnotin H Hvalid. simpl.
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

    rewrite ProgramState_fold_stepF_add.
    unfold fold_step at 1.
    rewrite ProgramState_merge_singleton_add with (k:=k) (b:=b) (ps:=m).
    apply ProgramState_merge_Proper.
    all: try assumption.
    all: try apply ProgramState_empty_valid.
    + apply H. apply Hm.
    + destruct (eqb (CState_read cbit k) cond) eqn:E1; try reflexivity.
      rewrite ProgramState_fold_stepF_add.
      all: try assumption.
      all: try apply ProgramState_empty_valid.
      * cbv [fold_step].
        rewrite <- ProgramState_merge_empty_l.
        destruct (eqb (CState_read cbit k) (negb cond)) eqn:E2.
        -- destruct (CState_read cbit k), cond; discriminate.
        -- reflexivity.
      * apply Execute_if_instr_branch_valid.
      * rewrite PFacts.not_find_in_iff.
        apply PFacts.empty_o.
    + intros k0 b0 Hb0.
      destruct (eqb (CState_read cbit k0) cond).
      apply ProgramState_fold_valid.
      apply ProgramState_singleton_valid. apply Hb0.
      apply ProgramState_empty_valid.
      intros k1 b1 ps' Hb1 Hps'.
      apply ProgramState_merge_valid. apply Hps'.
      apply Execute_if_instr_branch_valid. apply Hb1.
      apply ProgramState_singleton_valid. apply Hb0.
Qed.

Corollary Transform_if_nop_tf:
  forall (cbit: nat) (instr: Instruction),
  Instruction_equiv nq
  qasm{ if (cbit == 1) if (cbit == 0) instr }
  qasm{ nop }.
Proof.
  intros. apply Transform_double_if_nop.
Qed.

Corollary Transform_if_nop_ft:
  forall (cbit: nat) (instr: Instruction),
  Instruction_equiv nq
  qasm{ if (cbit == 0) if (cbit == 1) instr }
  qasm{ nop }.
Proof.
  intros. apply Transform_double_if_nop.
Qed.

Lemma Transform_double_reset:
  forall (qbit: nat),
  qbit < nq ->
  Instruction_equiv nq
  qasm{ reset qbit; reset qbit }
  qasm{ reset qbit }.
Proof.
  intros.
  intros ps Hps k.
  simpl. unfold Execute_reset_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find k ps); try reflexivity.
  simpl. f_equal.
  unfold Execute_reset_instr_branch.
  simpl. f_equal.
  apply den_reset_idempotent.
Qed.

(* Double measurement *)

(* Branching a classical state at a bit is idempotent: both resulting
   states branch to themselves again. *)
Lemma CState_branch_fixed:
  forall (idx: nat) (cstate: CState),
  let (c0, c1) := CState_branch idx cstate in
  CState_branch idx c0 = (c0, c1) /\ CState_branch idx c1 = (c0, c1).
Proof.
  induction idx as [| idx IH]; intros cstate.
  - destruct cstate; simpl; auto.
  - destruct cstate as [c | c |]; simpl.
    + specialize (IH c).
      destruct (CState_branch idx c) as [c0 c1].
      destruct IH as [H0 H1].
      simpl. rewrite H0, H1. auto.
    + specialize (IH c).
      destruct (CState_branch idx c) as [c0 c1].
      destruct IH as [H0 H1].
      simpl. rewrite H0, H1. auto.
    + specialize (IH 1%positive).
      destruct (CState_branch idx 1%positive) as [c0 c1].
      destruct IH as [H0 H1].
      simpl. rewrite H0, H1. auto.
Qed.

(* A density matrix is projected by [proj] when conjugating it with [proj]
   leaves it unchanged. *)
Definition den_projected (proj den: Matrix nq) : Prop :=
  proj * den * proj = den.

Lemma mat_mul_scale_r:
  forall (a: Complex) (A B: Matrix nq),
  A * (a .* B) = a .* (A * B).
Proof.
  intros a A B.
  rewrite <- mat_scale_mul_comm.
  apply mat_scale_mul_assoc.
Qed.

Lemma den_projected_measure:
  forall (proj den: Matrix nq),
  mat_projection proj ->
  den_projected proj (den_measure proj den).
Proof.
  intros proj den [Hp _].
  unfold den_projected, den_measure.
  rewrite mat_mul_scale_r, mat_scale_mul_assoc.
  f_equal.
  repeat rewrite mat_mul_assoc.
  rewrite Hp.
  rewrite <- (mat_mul_assoc _ proj proj).
  rewrite Hp.
  reflexivity.
Qed.

Lemma den_projected_mix:
  forall (proj A B: Matrix nq) (a b: Complex),
  den_projected proj A ->
  den_projected proj B ->
  den_projected proj (a .* A + b .* B).
Proof.
  intros proj A B a b HA HB.
  unfold den_projected in *.
  rewrite mat_mul_dist_l, mat_mul_dist_r.
  repeat rewrite mat_mul_scale_r.
  repeat rewrite mat_scale_mul_assoc.
  rewrite HA, HB.
  reflexivity.
Qed.

Lemma den_projected_prob_self:
  forall (proj den: Matrix nq),
  mat_projection proj ->
  den_projected proj den ->
  den_prob proj den = \tr den.
Proof.
  intros proj den [Hp _] Hden.
  unfold den_prob, den_projected in *.
  rewrite <- Hden at 1.
  rewrite <- mat_mul_assoc, Hp.
  rewrite Hden.
  reflexivity.
Qed.

Lemma den_projected_prob_perp:
  forall (proj proj' den: Matrix nq),
  proj * proj' = mat_0 ->
  den_projected proj den ->
  den_prob proj' den = 0.
Proof.
  intros proj proj' den Hperp Hden.
  unfold den_prob, den_projected in *.
  rewrite <- Hden.
  rewrite <- mat_mul_assoc, Hperp, mat_mul_0_r.
  apply mat_trace_0.
Qed.

Lemma com_inv_1: (/ 1 = 1)%com.
Proof.
  rewrite <- (com_mul_1_r (/ 1)).
  apply com_inv_mult.
  apply com_proj_neq_fst.
  simpl. lra.
Qed.

Lemma den_projected_measure_id:
  forall (proj den: Matrix nq),
  mat_projection proj ->
  den_valid den ->
  den_projected proj den ->
  den_measure proj den = den.
Proof.
  intros proj den Hproj Hvalid Hden.
  unfold den_measure.
  rewrite (den_projected_prob_self proj den Hproj Hden).
  rewrite (den_valid_normalized den Hvalid).
  rewrite Hden.
  rewrite com_inv_1.
  apply mat_scale_1.
Qed.

(* After a measurement of [qbit] into [cbit], every branch sits at a
   classical state that branching on [cbit] maps to itself, and its quantum
   state is already projected onto the outcome recorded in that bit. *)
Definition Branch_measured (qbit cbit: nat) (k: CState) (b: Branch nq) : Prop :=
  Branch_valid nq b /\
  ((fst (CState_branch cbit k) = k /\
    den_projected (mat_proj0 nq qbit) (B_qstate nq b)) \/
   (snd (CState_branch cbit k) = k /\
    den_projected (mat_proj1 nq qbit) (B_qstate nq b))).

Definition ProgramState_measured (qbit cbit: nat) (ps: ProgramState nq) : Prop :=
  forall k b, PositiveMap.MapsTo k b ps -> Branch_measured qbit cbit k b.

Lemma Branch_merge_measured:
  forall (qbit cbit: nat) (k: CState) (b0 b1: Branch nq),
  Branch_measured qbit cbit k b0 ->
  Branch_measured qbit cbit k b1 ->
  Branch_measured qbit cbit k (Branch_merge nq b0 b1).
Proof.
  intros qbit cbit k b0 b1 [Hv0 H0] [Hv1 H1].
  split.
  { apply Branch_merge_valid; assumption. }
  pose proof (CState_branch_different cbit k) as Hdiff.
  destruct (CState_branch cbit k) as [c0 c1].
  simpl in *.
  destruct H0 as [[Hk0 Hp0] | [Hk0 Hp0]], H1 as [[Hk1 Hp1] | [Hk1 Hp1]].
  - left. split; try assumption.
    apply den_projected_mix; assumption.
  - exfalso. apply Hdiff. congruence.
  - exfalso. apply Hdiff. congruence.
  - right. split; try assumption.
    apply den_projected_mix; assumption.
Qed.

Lemma ProgramState_merge_measured:
  forall (qbit cbit: nat) (ps0 ps1: ProgramState nq),
  ProgramState_measured qbit cbit ps0 ->
  ProgramState_measured qbit cbit ps1 ->
  ProgramState_measured qbit cbit (ProgramState_merge nq ps0 ps1).
Proof.
  intros qbit cbit ps0 ps1 H0 H1 k b Hmaps.
  rewrite PFacts.find_mapsto_iff in Hmaps.
  rewrite ProgramState_merge_o in Hmaps.
  destruct (PositiveMap.find k ps0) as [b0 |] eqn:E0,
           (PositiveMap.find k ps1) as [b1 |] eqn:E1;
  inversion Hmaps; subst.
  - apply Branch_merge_measured.
    + apply H0. apply PFacts.find_mapsto_iff. assumption.
    + apply H1. apply PFacts.find_mapsto_iff. assumption.
  - apply H0. apply PFacts.find_mapsto_iff. assumption.
  - apply H1. apply PFacts.find_mapsto_iff. assumption.
Qed.

Lemma Execute_measure_instr_branch_measured:
  forall (qbit cbit: nat) (k: CState) (b: Branch nq),
  Branch_valid nq b ->
  ProgramState_measured qbit cbit
    (Execute_measure_instr_branch nq qbit cbit k b).
Proof.
  intros qbit cbit k b Hb k' b' Hmaps.
  split.
  { apply (Execute_measure_instr_branch_valid nq qbit cbit k b Hb k' b' Hmaps). }
  revert Hmaps.
  unfold Execute_measure_instr_branch.
  pose proof (CState_branch_fixed cbit k) as Hfix.
  destruct (CState_branch cbit k) as [c0 c1].
  destruct Hfix as [Hf0 Hf1].
  destruct (Rgt_dec (com_real (den_prob_0 qbit (B_qstate nq b))) 0),
           (Rgt_dec (com_real (den_prob_1 qbit (B_qstate nq b))) 0);
  intros Hmaps.
  all: repeat (
    rewrite PFacts.add_mapsto_iff in Hmaps;
    destruct Hmaps as [[Hk Hb'] | [_ Hmaps]];
    [subst; rewrite ?Hf0, ?Hf1; simpl;
     first
       [ left; split; [reflexivity |
           apply den_projected_measure; apply mat_proj0_projection]
       | right; split; [reflexivity |
           apply den_projected_measure; apply mat_proj1_projection] ]
    | idtac ]).
  all: rewrite PFacts.empty_mapsto_iff in Hmaps; contradiction.
Qed.

Lemma Execute_measure_instr_measured:
  forall (qbit cbit: nat) (ps: ProgramState nq),
  ProgramState_valid nq ps ->
  ProgramState_measured qbit cbit (Execute_measure_instr nq qbit cbit ps).
Proof.
  intros qbit cbit ps Hps.
  unfold Execute_measure_instr.
  apply PProperties.fold_rec_nodep.
  - intros k b Hmaps.
    apply PFacts.empty_mapsto_iff in Hmaps.
    contradiction.
  - intros k b acc Hmaps Hacc.
    unfold fold_step.
    apply ProgramState_merge_measured.
    + assumption.
    + apply Execute_measure_instr_branch_measured.
      apply Hps with k.
      assumption.
Qed.

Lemma Execute_measure_instr_branch_measured_id:
  forall (qbit cbit: nat) (k: CState) (b: Branch nq),
  Branch_measured qbit cbit k b ->
  Execute_measure_instr_branch nq qbit cbit k b =
  PositiveMap.add k b (PositiveMap.empty (Branch nq)).
Proof.
  intros qbit cbit k [rho p] [[Hrho Hp] Hk].
  unfold Execute_measure_instr_branch.
  cbn [B_qstate B_prob] in *.
  destruct (CState_branch cbit k) as [c0 c1].
  simpl in Hk.
  destruct Hk as [[Hk Hproj] | [Hk Hproj]]; subst.
  - assert (H0: den_prob_0 qbit rho = 1).
    { unfold den_prob_0.
      rewrite (den_projected_prob_self _ _ (mat_proj0_projection nq qbit) Hproj).
      apply (den_valid_normalized rho Hrho). }
    assert (H1: den_prob_1 qbit rho = 0).
    { unfold den_prob_1.
      apply (den_projected_prob_perp (mat_proj0 nq qbit)).
      apply mat_proj_01_perp.
      assumption. }
    rewrite H0, H1.
    unfold com_real, RTC. simpl fst.
    destruct (Rgt_dec 1 0) as [_ | Hn]; [| exfalso; lra].
    destruct (Rgt_dec 0 0) as [Hn | _]; [exfalso; lra |].
    f_equal. f_equal.
    + apply den_projected_measure_id; try assumption.
      apply mat_proj0_projection.
    + lra.
  - assert (H0: den_prob_0 qbit rho = 0).
    { unfold den_prob_0.
      apply (den_projected_prob_perp (mat_proj1 nq qbit)).
      apply mat_proj_10_perp.
      assumption. }
    assert (H1: den_prob_1 qbit rho = 1).
    { unfold den_prob_1.
      rewrite (den_projected_prob_self _ _ (mat_proj1_projection nq qbit) Hproj).
      apply (den_valid_normalized rho Hrho). }
    rewrite H0, H1.
    unfold com_real, RTC. simpl fst.
    destruct (Rgt_dec 0 0) as [Hn | _]; [exfalso; lra |].
    destruct (Rgt_dec 1 0) as [_ | Hn]; [| exfalso; lra].
    f_equal. f_equal.
    + apply den_projected_measure_id; try assumption.
      apply mat_proj1_projection.
    + lra.
Qed.

Lemma Execute_measure_instr_measured_id:
  forall (qbit cbit: nat) (ps: ProgramState nq),
  ProgramState_valid nq ps ->
  ProgramState_measured qbit cbit ps ->
  ProgramState_equiv nq (Execute_measure_instr nq qbit cbit ps) ps.
Proof.
  intros qbit cbit ps Hps Hmeas.
  unfold Execute_measure_instr.
  enough (H:
    ProgramState_valid nq ps /\
    ProgramState_equiv nq
      (PositiveMap.fold
        (fold_step nq (Execute_measure_instr_branch nq qbit cbit))
        ps (PositiveMap.empty (Branch nq)))
      ps)
  by apply H.
  apply (PProperties.fold_rec_bis
    (P := fun m a => ProgramState_valid nq m /\ ProgramState_equiv nq a m)).
  - intros m m' a Heq [Hv Ha].
    split.
    + apply ProgramState_valid_equal with m; assumption.
    + etransitivity; eassumption.
  - split.
    + apply ProgramState_empty_valid.
    + reflexivity.
  - intros k b a m Hmaps Hnotin [Hv Ha].
    assert (Hb: Branch_valid nq b) by (apply Hps with k; assumption).
    split.
    + apply ProgramState_add_valid; assumption.
    + unfold fold_step.
      rewrite Execute_measure_instr_branch_measured_id
        by (apply Hmeas; assumption).
      etransitivity.
      { apply ProgramState_merge_Proper.
        - exact Ha.
        - reflexivity. }
      symmetry.
      apply ProgramState_merge_singleton_add; assumption.
Qed.

Lemma Transform_double_measure:
  forall (qbit cbit: nat),
  Instruction_equiv nq
  qasm{ measure qbit -> cbit; measure qbit -> cbit }
  qasm{ measure qbit -> cbit }.
Proof.
  intros qbit cbit ps Hps.
  etransitivity.
  { apply Execute_suppl_seq. }
  cbn [Execute_suppl].
  apply Execute_measure_instr_measured_id.
  - apply Execute_measure_instr_valid.
    assumption.
  - apply Execute_measure_instr_measured.
    assumption.
Qed.

(* Instruction_equiv rewrite inside If instruction *)
(* Written here since Equiv.v do not reference Valid.v; causes cyclic reference *)
Lemma Instruction_if_Proper:
  forall (cbit: nat) (cond: bool),
  Proper (Instruction_equiv nq ==> Instruction_equiv nq)
  (IfInstr cbit cond).
Proof.
  intros cbit cond instr1 instr2 Hinstr ps.
  apply ProgramState_ind with (m:=ps).
  - intros m0 m1 Heq H Hm1.
    etransitivity. {
      apply Execute_suppl_Proper.
      symmetry. apply Heq.
    }
    etransitivity. {
      apply H.
      apply ProgramState_valid_equal with m1.
      apply Hm1.
      symmetry. apply Heq.
    }
    apply Execute_suppl_Proper. apply Heq.
  - reflexivity.
  - intros k b m Hnotin H Hvalid. simpl.
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

    rewrite ProgramState_fold_stepF_add.
    rewrite ProgramState_fold_stepF_add.
    unfold fold_step at 1 3.
    apply ProgramState_merge_Proper.
    all: try apply Execute_if_instr_branch_valid.
    all: try assumption.
    all: try apply ProgramState_empty_valid.
    + apply H. apply Hm.
    + destruct (eqb (CState_read cbit k) cond); try reflexivity.
      apply Hinstr.
      apply ProgramState_singleton_valid.
      apply Hb.
Qed.

Corollary Instruction_if_instr_rewrite:
  forall (cbit: nat) (cond: bool) (instr1 instr2: Instruction),
  Instruction_equiv nq instr1 instr2 ->
  Instruction_equiv nq
  (IfInstr cbit cond instr1)
  (IfInstr cbit cond instr2).
Proof.
  apply Instruction_if_Proper.
Qed.

(* Behavioral equivalence - insert quantum operation after all operations *)
Lemma Transform_insert_rotate:
  forall (theta phi lambda: R) (qbit: nat),
  qbit < nq ->
  Instruction_behavioral_equiv nq
  qasm{ U (theta, phi, lambda) qbit }
  qasm{ nop }.
Proof.
  intros.
  intros ps Hps k.
  simpl. unfold Execute_rotate_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find k ps); reflexivity.
Qed.

Lemma Transform_insert_cnot:
  forall (qbit1 qbit2: nat),
  qbit1 < nq -> qbit2 < nq ->
  Instruction_behavioral_equiv nq
  qasm{ cx qbit1 qbit2 }
  qasm{ nop }.
Proof.
  intros.
  intros ps Hps k.
  simpl. unfold Execute_cnot_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find k ps); reflexivity.
Qed.

Lemma Transform_insert_swap:
  forall (qbit1 qbit2: nat),
  qbit1 < nq -> qbit2 < nq ->
  Instruction_behavioral_equiv nq
  qasm{ swap qbit1 qbit2 }
  qasm{ nop }.
Proof.
  intros.
  intros ps Hps k.
  simpl. unfold Execute_swap_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find k ps); reflexivity.
Qed.

Lemma Transform_insert_reset:
  forall (qbit: nat),
  qbit < nq ->
  Instruction_behavioral_equiv nq
  qasm{ reset qbit }
  qasm{ nop }.
Proof.
  intros.
  intros ps Hps k.
  simpl. unfold Execute_reset_instr.
  repeat rewrite PFacts.map_o.
  destruct (PositiveMap.find k ps); reflexivity.
Qed.

End TRANSFORM.
