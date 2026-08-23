Require Import QASMInfer.domega.DOmega.
Require Import QASMInfer.domega.DOmegaMatrix.
Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.All.
Require Import QASMInfer.rewrite.All.

From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
From Stdlib Require Import Reals.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

Import ListNotations.

Open Scope string_scope.
Open Scope nat_scope.

Section STANDARD_MULTI_GATE_SYNTAX.

Inductive StandardGate : Type :=
| Std_I
| Std_X
| Std_Y
| Std_Z
| Std_H
| Std_S
| Std_Sdg
| Std_T
| Std_Tdg
| Std_SX
| Std_SXdg.

Inductive StandardPatternGate : Type :=
| SPG_Std : StandardGate -> nat -> StandardPatternGate
| SPG_Cnot : nat -> nat -> StandardPatternGate
| SPG_Swap : nat -> nat -> StandardPatternGate.

Definition standard_gate_pattern
    (gate : StandardGate)
    (qbit_pattern : NatPattern)
    : InstructionPattern :=
  match gate with
  | Std_I => PRotate A0 A0 A0 qbit_pattern
  | Std_X => PRotate API A0 API qbit_pattern
  | Std_Y => PRotate API API2 API2 qbit_pattern
  | Std_Z => PRotate A0 A0 API qbit_pattern
  | Std_H => PRotate API2 A0 API qbit_pattern
  | Std_S => PRotate A0 A0 API2 qbit_pattern
  | Std_Sdg => PRotate A0 A0 ANPI2 qbit_pattern
  | Std_T => PRotate A0 A0 API4 qbit_pattern
  | Std_Tdg => PRotate A0 A0 ANPI4 qbit_pattern
  | Std_SX => PRotate API2 ANPI2 API2 qbit_pattern
  | Std_SXdg => PRotate API2 API2 ANPI2 qbit_pattern
  end.

Definition standard_pattern_gate_to_instruction_pattern
    (gate : StandardPatternGate)
    : InstructionPattern :=
  match gate with
  | SPG_Std gate qbit =>
      standard_gate_pattern gate (NatVar qbit)
  | SPG_Cnot control target =>
      PCnot (NatVar control) (NatVar target)
  | SPG_Swap qbit1 qbit2 =>
      PSwap (NatVar qbit1) (NatVar qbit2)
  end.

Definition standard_pattern_sequence_to_instruction_patterns
    (gates : list StandardPatternGate)
    : list InstructionPattern :=
  map standard_pattern_gate_to_instruction_pattern gates.

End STANDARD_MULTI_GATE_SYNTAX.

Section STANDARD_MULTI_DOMEGA_MATRICES.

Definition domega_matrix2
    (a b c d : DOmega)
    : DOmegaMatrix 1 :=
  domega_rec_mat
    (domega_bas_mat a)
    (domega_bas_mat b)
    (domega_bas_mat c)
    (domega_bas_mat d).

Definition standard_gate_domega_matrix
    (gate : StandardGate)
    : DOmegaMatrix 1 :=
  match gate with
  | Std_I =>
      domega_matrix_eye
  | Std_X =>
      domega_matrix2 domega_zero domega_one domega_one domega_zero
  | Std_Y =>
      domega_matrix2 domega_zero domega_minus_i domega_w2 domega_zero
  | Std_Z =>
      domega_matrix2 domega_one domega_zero domega_zero domega_minus_one
  | Std_H =>
      domega_matrix2
        domega_h_scalar domega_h_scalar
        domega_h_scalar (domega_neg domega_h_scalar)
  | Std_S =>
      domega_matrix2 domega_one domega_zero domega_zero domega_w2
  | Std_Sdg =>
      domega_matrix2 domega_one domega_zero domega_zero domega_minus_i
  | Std_T =>
      domega_matrix2 domega_one domega_zero domega_zero domega_w
  | Std_Tdg =>
      domega_matrix2 domega_one domega_zero domega_zero (domega_neg domega_w3)
  | Std_SX =>
      domega_matrix2
        domega_half_one_plus_i domega_half_one_minus_i
        domega_half_one_minus_i domega_half_one_plus_i
  | Std_SXdg =>
      domega_matrix2
        domega_half_one_minus_i domega_half_one_plus_i
        domega_half_one_plus_i domega_half_one_minus_i
  end.

End STANDARD_MULTI_DOMEGA_MATRICES.

Section STANDARD_MULTI_CHECKER.

Definition standard_pattern_gate_nqubits
    (gate : StandardPatternGate)
    : nat :=
  match gate with
  | SPG_Std _ qbit =>
      S qbit
  | SPG_Cnot control target =>
      S (Nat.max control target)
  | SPG_Swap qbit1 qbit2 =>
      S (Nat.max qbit1 qbit2)
  end.

Fixpoint standard_pattern_sequence_nqubits
    (gates : list StandardPatternGate)
    : nat :=
  match gates with
  | [] => 0
  | gate :: rest =>
      Nat.max
        (standard_pattern_gate_nqubits gate)
        (standard_pattern_sequence_nqubits rest)
  end.

Definition standard_pattern_rule_nqubits
    (lhs rhs : list StandardPatternGate)
    : nat :=
  Nat.max
    (standard_pattern_sequence_nqubits lhs)
    (standard_pattern_sequence_nqubits rhs).

Definition qbit_in_bounds (n qbit : nat) : bool :=
  Nat.ltb qbit n.

Definition qbit_pair_in_bounds (n qbit1 qbit2 : nat) : bool :=
  qbit_in_bounds n qbit1 && qbit_in_bounds n qbit2.

Definition standard_pattern_gate_matrix
    (n : nat)
    (gate : StandardPatternGate)
    : option (DOmegaMatrix n) :=
  match gate with
  | SPG_Std gate qbit =>
      if qbit_in_bounds n qbit
      then Some (domega_matrix_single n qbit (standard_gate_domega_matrix gate))
      else None
  | SPG_Cnot control target =>
      if Nat.eqb control target || negb (qbit_pair_in_bounds n control target)
      then None
      else Some (domega_matrix_cnot control target)
  | SPG_Swap qbit1 qbit2 =>
      if Nat.eqb qbit1 qbit2 || negb (qbit_pair_in_bounds n qbit1 qbit2)
      then None
      else Some (domega_matrix_swap qbit1 qbit2)
  end.

Fixpoint standard_pattern_sequence_matrix
    (n : nat)
    (gates : list StandardPatternGate)
    : option (DOmegaMatrix n) :=
  match gates with
  | [] =>
      Some domega_matrix_eye
  | gate :: rest =>
      let* gate_matrix := standard_pattern_gate_matrix n gate in
      let* rest_matrix := standard_pattern_sequence_matrix n rest in
      Some (domega_matrix_mul rest_matrix gate_matrix)
  end.

Definition standard_pattern_transform_validb
    (lhs rhs : list StandardPatternGate)
    : bool :=
  let n := standard_pattern_rule_nqubits lhs rhs in
  match
    standard_pattern_sequence_matrix n lhs,
    standard_pattern_sequence_matrix n rhs
  with
  | Some lhs_matrix, Some rhs_matrix =>
      domega_matrix_eq_up_to_phaseb lhs_matrix rhs_matrix
  | _, _ =>
      false
  end.

Definition standard_pattern_rule_validb
    (nq : nat)
    (lhs rhs : list StandardPatternGate)
    : bool :=
  (standard_pattern_rule_nqubits lhs rhs <=? nq)
  && standard_pattern_transform_validb lhs rhs.

Definition standard_pattern_rewrite_rule
    (lhs rhs : list StandardPatternGate)
    : RewriteRule :=
  {|
    rule_lhs := standard_pattern_sequence_to_instruction_patterns lhs;
    rule_rhs := standard_pattern_sequence_to_instruction_patterns rhs;
  |}.

Definition standard_pattern_rule_of_sequences
    (nq : nat)
    (name : string)
    (lhs rhs : list StandardPatternGate)
    : option TransformSpec :=
  if standard_pattern_rule_validb nq lhs rhs
  then Some (TransformSpec_simple_rule name (standard_pattern_rewrite_rule lhs rhs))
  else None.

End STANDARD_MULTI_CHECKER.

Section STANDARD_MULTI_PROOFS.

Definition standard_gate_instruction
    (gate : StandardGate)
    (qbit : nat)
    : Instruction :=
  match gate with
  | Std_I => Gate_I qbit
  | Std_X => Gate_X qbit
  | Std_Y => Gate_Y qbit
  | Std_Z => Gate_Z qbit
  | Std_H => Gate_H qbit
  | Std_S => Gate_S qbit
  | Std_Sdg => Gate_Sdg qbit
  | Std_T => Gate_T qbit
  | Std_Tdg => Gate_Tdg qbit
  | Std_SX => Gate_SX qbit
  | Std_SXdg => Gate_SXdg qbit
  end.

Definition standard_gate_complex_matrix
    (gate : StandardGate)
    : Matrix 1 :=
  complex_of_domega_matrix (standard_gate_domega_matrix gate).

Definition standard_pattern_gate_local_instruction
    (gate : StandardPatternGate)
    : Instruction :=
  match gate with
  | SPG_Std gate qbit =>
      standard_gate_instruction gate qbit
  | SPG_Cnot control target =>
      CnotInstr control target
  | SPG_Swap qbit1 qbit2 =>
      SwapInstr qbit1 qbit2
  end.

Definition standard_pattern_sequence_local_instructions
    (gates : list StandardPatternGate)
    : list Instruction :=
  map standard_pattern_gate_local_instruction gates.

Definition standard_pattern_gate_instruction
    (subst : PatternMap)
    (gate : StandardPatternGate)
    : option Instruction :=
  match gate with
  | SPG_Std gate qbit =>
      let* qbit' := NatMap.find qbit (pattern_qbit_map subst) in
      Some (standard_gate_instruction gate qbit')
  | SPG_Cnot control target =>
      let* control' := NatMap.find control (pattern_qbit_map subst) in
      let* target' := NatMap.find target (pattern_qbit_map subst) in
      Some (CnotInstr control' target')
  | SPG_Swap qbit1 qbit2 =>
      let* qbit1' := NatMap.find qbit1 (pattern_qbit_map subst) in
      let* qbit2' := NatMap.find qbit2 (pattern_qbit_map subst) in
      Some (SwapInstr qbit1' qbit2')
  end.

Fixpoint standard_pattern_sequence_instructions
    (subst : PatternMap)
    (gates : list StandardPatternGate)
    : option (list Instruction) :=
  match gates with
  | [] =>
      Some []
  | gate :: rest =>
      let* instr := standard_pattern_gate_instruction subst gate in
      let* instrs := standard_pattern_sequence_instructions subst rest in
      Some (instr :: instrs)
  end.

Lemma standard_pattern_gate_inst :
  forall subst gate,
    InstructionPattern_inst
      (standard_pattern_gate_to_instruction_pattern gate)
      subst =
    standard_pattern_gate_instruction subst gate.
Proof.
  intros subst [gate qbit | control target | qbit1 qbit2];
    simpl; try reflexivity.
  destruct gate; simpl; reflexivity.
Qed.

Lemma standard_pattern_sequence_inst :
  forall subst gates,
    InstructionPattern_inst_list
      (standard_pattern_sequence_to_instruction_patterns gates)
      subst =
    standard_pattern_sequence_instructions subst gates.
Proof.
  intros subst gates.
  induction gates as [| gate rest IH]; simpl.
  - reflexivity.
  - rewrite standard_pattern_gate_inst.
    destruct (standard_pattern_gate_instruction subst gate); simpl;
      try reflexivity.
    rewrite IH.
    reflexivity.
Qed.

Lemma Matrix_of_rotate_with_global_phase_multi :
  forall nq theta phi lambda qbit phase U,
    mat_rot (Angle_to_R theta) (Angle_to_R phi) (Angle_to_R lambda) =
    gphase phase .* U ->
    Matrix_of nq (RotateInstr theta phi lambda qbit)
      (mat_single nq qbit U).
Proof.
  intros nq theta phi lambda qbit phase U Hphase ps cstate.
  simpl.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal.
  rewrite Hphase.
  destruct (le_lt_dec nq qbit) as [Hout | Hin].
  - repeat rewrite (mat_single_out_of_bounds _ Hout).
    reflexivity.
  - rewrite (mat_single_scale _ _ Hin).
    rewrite den_uop_gphase.
    reflexivity.
Qed.

Lemma standard_gate_complex_matrix_I :
  standard_gate_complex_matrix Std_I = mat_eye.
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix.
  apply complex_of_domega_matrix_eye.
Qed.

Lemma standard_gate_complex_matrix_X :
  standard_gate_complex_matrix Std_X = Gate_X_matrix.
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix,
    domega_matrix2, Gate_X_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_complex_matrix_Y :
  standard_gate_complex_matrix Std_Y = Gate_Y_matrix.
Proof.
  change
    (complex_of_domega_matrix
       (domega_matrix2 domega_zero domega_minus_i domega_w2 domega_zero) =
     Gate_Y_matrix).
  unfold domega_matrix2, Gate_Y_matrix.
  simpl.
  rewrite complex_of_domega_zero, complex_of_domega_w2,
    complex_of_domega_neg_w2.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_complex_matrix_Z :
  standard_gate_complex_matrix Std_Z = Gate_Z_matrix.
Proof.
  change
    (complex_of_domega_matrix
       (domega_matrix2 domega_one domega_zero domega_zero domega_minus_one) =
     Gate_Z_matrix).
  unfold domega_matrix2, Gate_Z_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_neg_one.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_complex_matrix_H :
  standard_gate_complex_matrix Std_H = Gate_H_matrix.
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix,
    domega_matrix2, Gate_H_matrix.
  simpl.
  rewrite domega_h_scalar_to_complex.
  rewrite complex_of_domega_neg.
  rewrite domega_h_scalar_to_complex.
  repeat (f_equal; try lca).
Qed.

Definition phase_gate_matrix_multi (lambda : R) : Matrix 1 :=
  rec_mat
    (bas_mat Cone)
    (bas_mat Czero)
    (bas_mat Czero)
    (bas_mat (com_iexp lambda)).

Lemma phase_gate_matrix_gphase_multi :
  forall lambda,
    mat_rot 0 0 lambda =
    gphase (- lambda / 2) .* phase_gate_matrix_multi lambda.
Proof.
  intros lambda.
  unfold mat_rot, phase_gate_matrix_multi, gphase.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  repeat rewrite mat_mul_eye_l.
  unfold mat_rot_z.
  simpl.
  f_equal; f_equal; try lca.
  rewrite <- com_iexp_mul.
  replace (- lambda / 2 + lambda)%R with (lambda / 2)%R by field.
  reflexivity.
Qed.

Lemma standard_gate_complex_matrix_S :
  standard_gate_complex_matrix Std_S = phase_gate_matrix_multi PI2.
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix,
    domega_matrix2, phase_gate_matrix_multi.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_w2, com_iexp_pi2.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_complex_matrix_Sdg :
  standard_gate_complex_matrix Std_Sdg = phase_gate_matrix_multi (- PI2).
Proof.
  change
    (complex_of_domega_matrix
       (domega_matrix2 domega_one domega_zero domega_zero domega_minus_i) =
     phase_gate_matrix_multi (- PI2)).
  unfold domega_matrix2, phase_gate_matrix_multi.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_neg_w2, com_iexp_neg_pi2.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_complex_matrix_T :
  standard_gate_complex_matrix Std_T = phase_gate_matrix_multi (PI / 4).
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix,
    domega_matrix2, phase_gate_matrix_multi.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_w.
  unfold omega.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_complex_matrix_Tdg :
  standard_gate_complex_matrix Std_Tdg = phase_gate_matrix_multi (- PI / 4).
Proof.
  change
    (complex_of_domega_matrix
       (domega_matrix2 domega_one domega_zero domega_zero
          (domega_neg domega_w3)) =
     phase_gate_matrix_multi (- PI / 4)).
  unfold domega_matrix2, phase_gate_matrix_multi.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_neg_w3_exp.
  repeat (f_equal; try lca).
Qed.

Ltac close_sqrt2_field_multi :=
  apply com_proj_eq; simpl; field_simplify_eq;
  try solve [apply sqrt2_neq_0];
  try replace (sqrt 2 ^ 2)%R with 2%R by
    (simpl; rewrite Rmult_1_r; rewrite sqrt_sqrt; lra);
  lra.

Lemma standard_gate_complex_matrix_SX_gphase :
  mat_rot PI2 (- PI2) PI2 =
  gphase (- PI / 4) .* standard_gate_complex_matrix Std_SX.
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix,
    domega_matrix2.
  simpl.
  rewrite complex_of_domega_half_one_plus_i,
    complex_of_domega_half_one_minus_i.
  unfold mat_rot, mat_rot_y, mat_rot_z, gphase.
  simpl.
  replace (PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  replace (- PI2 / 2)%R with (- (PI / 4))%R by (unfold PI; field).
  replace (- - PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  replace (- PI / 4)%R with (-(PI / 4))%R by field.
  unfold com_iexp.
  rewrite !cos_neg, !sin_neg, !cos_PI4, !sin_PI4.
  repeat match goal with
  | |- rec_mat _ _ _ _ = rec_mat _ _ _ _ => f_equal
  | |- bas_mat _ = bas_mat _ => f_equal
  end.
  all: close_sqrt2_field_multi.
Qed.

Lemma standard_gate_complex_matrix_SXdg_gphase :
  mat_rot PI2 PI2 (- PI2) =
  gphase (PI / 4) .* standard_gate_complex_matrix Std_SXdg.
Proof.
  unfold standard_gate_complex_matrix, standard_gate_domega_matrix,
    domega_matrix2.
  simpl.
  rewrite complex_of_domega_half_one_plus_i,
    complex_of_domega_half_one_minus_i.
  unfold mat_rot, mat_rot_y, mat_rot_z, gphase.
  simpl.
  replace (PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  replace (- PI2 / 2)%R with (- (PI / 4))%R by (unfold PI; field).
  replace (- - PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  unfold com_iexp.
  rewrite !cos_neg, !sin_neg, !cos_PI4, !sin_PI4.
  repeat match goal with
  | |- rec_mat _ _ _ _ = rec_mat _ _ _ _ => f_equal
  | |- bas_mat _ = bas_mat _ => f_equal
  end.
  all: close_sqrt2_field_multi.
Qed.

Lemma Matrix_of_standard_gate_multi :
  forall nq gate qbit,
    Matrix_of nq (standard_gate_instruction gate qbit)
      (mat_single nq qbit (standard_gate_complex_matrix gate)).
Proof.
  intros nq gate qbit.
  destruct gate; simpl.
  - rewrite standard_gate_complex_matrix_I, mat_single_eye.
    apply Matrix_of_I.
  - rewrite standard_gate_complex_matrix_X.
    apply Matrix_of_X.
  - rewrite standard_gate_complex_matrix_Y.
    apply Matrix_of_Y.
  - rewrite standard_gate_complex_matrix_Z.
    apply Matrix_of_Z.
  - rewrite standard_gate_complex_matrix_H.
    apply Matrix_of_H.
  - eapply Matrix_of_rotate_with_global_phase_multi.
    angle_to_R_simpl.
    rewrite standard_gate_complex_matrix_S.
    apply phase_gate_matrix_gphase_multi.
  - eapply Matrix_of_rotate_with_global_phase_multi.
    angle_to_R_simpl.
    rewrite standard_gate_complex_matrix_Sdg.
    apply phase_gate_matrix_gphase_multi.
  - eapply Matrix_of_rotate_with_global_phase_multi.
    angle_to_R_simpl.
    rewrite standard_gate_complex_matrix_T.
    apply phase_gate_matrix_gphase_multi.
  - eapply Matrix_of_rotate_with_global_phase_multi.
    angle_to_R_simpl.
    replace (-(PI / 4))%R with (- PI / 4)%R by field.
    rewrite standard_gate_complex_matrix_Tdg.
    apply phase_gate_matrix_gphase_multi.
  - eapply Matrix_of_rotate_with_global_phase_multi.
    angle_to_R_simpl.
    apply standard_gate_complex_matrix_SX_gphase.
  - eapply Matrix_of_rotate_with_global_phase_multi.
    angle_to_R_simpl.
    apply standard_gate_complex_matrix_SXdg_gphase.
Qed.

Lemma swap_qbit_right :
  forall qbit1 qbit2,
    swap_qbit qbit1 qbit2 qbit2 = qbit1.
Proof.
  intros qbit1 qbit2.
  unfold swap_qbit.
  destruct (Nat.eq_dec qbit2 qbit1) as [Heq | Hneq].
  - subst. reflexivity.
  - destruct (Nat.eq_dec qbit2 qbit2) as [_ | Hcontra].
    + reflexivity.
    + contradiction.
Qed.

Lemma swap_qbit_left :
  forall qbit1 qbit2,
    swap_qbit qbit1 qbit2 qbit1 = qbit2.
Proof.
  intros qbit1 qbit2.
  unfold swap_qbit.
  destruct (Nat.eq_dec qbit1 qbit1) as [_ | Hcontra].
  - reflexivity.
  - contradiction.
Qed.

Lemma standard_gate_instruction_swap_to_local :
  forall nq gate local actual,
    Qbit_index_valid nq local ->
    Qbit_index_valid nq actual ->
    Instruction_equiv nq
      (standard_gate_instruction gate actual)
      qasm{ swap local actual;
            $(standard_gate_instruction gate local);
            swap local actual }.
Proof.
  intros nq gate local actual Hlocal Hactual.
  replace (standard_gate_instruction gate local) with
    (swap_qbit_instr local actual (standard_gate_instruction gate actual)).
  - rewrite Transform_swap_swap_insert.
    reflexivity.
    all: assumption.
  - destruct gate; unfold swap_qbit_instr, change_qbit_instr,
      standard_gate_instruction; simpl;
      rewrite swap_qbit_right; reflexivity.
Qed.

Definition qbit_swap_pair := (nat * nat)%type.

Fixpoint qbit_apply_swaps (swaps : list qbit_swap_pair) (qbit : nat)
    : nat :=
  match swaps with
  | [] =>
      qbit
  | (qbit1, qbit2) :: rest =>
      qbit_apply_swaps rest (swap_qbit qbit1 qbit2 qbit)
  end.

Fixpoint change_qbit_instr_swaps
    (swaps : list qbit_swap_pair)
    (instr : Instruction)
    : Instruction :=
  match swaps with
  | [] =>
      instr
  | (qbit1, qbit2) :: rest =>
      change_qbit_instr_swaps rest (swap_qbit_instr qbit1 qbit2 instr)
  end.

Definition qbit_pair_valid (nq : nat) (pair : qbit_swap_pair) : Prop :=
  Qbit_index_valid nq (fst pair) /\ Qbit_index_valid nq (snd pair).

Definition qbit_pair_swap_fst
    (qbit1 qbit2 : nat)
    (pair : qbit_swap_pair)
    : qbit_swap_pair :=
  (swap_qbit qbit1 qbit2 (fst pair), snd pair).

Fixpoint qbit_swaps_for_pairs_aux
    (fuel : nat)
    (pairs : list qbit_swap_pair)
    : list qbit_swap_pair :=
  match fuel, pairs with
  | O, _ =>
      []
  | S _, [] =>
      []
  | S fuel', (local, actual) :: rest =>
      (local, actual)
      :: qbit_swaps_for_pairs_aux fuel'
           (map (qbit_pair_swap_fst local actual) rest)
  end.

Definition qbit_swaps_for_pairs
    (pairs : list qbit_swap_pair)
    : list qbit_swap_pair :=
  qbit_swaps_for_pairs_aux (List.length pairs) pairs.

Lemma change_qbit_instr_compose :
  forall (fn1 fn2 : nat -> nat) instr,
    change_qbit_instr fn1 (change_qbit_instr fn2 instr) =
    change_qbit_instr (fun qbit => fn1 (fn2 qbit)) instr.
Proof.
  intros fn1 fn2 instr.
  induction instr using Instruction_ind'; simpl;
    try reflexivity;
    try (f_equal; assumption).
  - f_equal.
    induction is as [| instr instrs IHinstrs].
    + reflexivity.
    + simpl.
      inversion H; subst.
      rewrite H2.
      rewrite IHinstrs; [reflexivity | assumption].
Qed.

Lemma change_qbit_instr_id :
  forall instr,
    change_qbit_instr (fun qbit => qbit) instr = instr.
Proof.
  intro instr.
  induction instr using Instruction_ind'; simpl;
    try reflexivity;
    try (f_equal; assumption).
  f_equal.
  induction is as [| instr instrs IHinstrs].
  - reflexivity.
  - simpl.
    inversion H; subst.
    rewrite H2.
    rewrite IHinstrs; [reflexivity | assumption].
Qed.

Lemma change_qbit_instr_swaps_eq :
  forall swaps instr,
    change_qbit_instr_swaps swaps instr =
    change_qbit_instr (qbit_apply_swaps swaps) instr.
Proof.
  induction swaps as [| [qbit1 qbit2] rest IH]; intros instr.
  - simpl.
    symmetry.
    apply change_qbit_instr_id.
  - simpl.
    rewrite IH.
    unfold swap_qbit_instr.
    rewrite change_qbit_instr_compose.
    reflexivity.
Qed.

Lemma qbit_apply_swaps_change_qbit_instr_swaps_standard_gate :
  forall swaps gate qbit,
    change_qbit_instr_swaps swaps (standard_gate_instruction gate qbit) =
    standard_gate_instruction gate (qbit_apply_swaps swaps qbit).
Proof.
  intros swaps gate qbit.
  rewrite change_qbit_instr_swaps_eq.
  destruct gate; reflexivity.
Qed.

Lemma qbit_apply_swaps_change_qbit_instr_swaps_cnot :
  forall swaps control target,
    change_qbit_instr_swaps swaps (CnotInstr control target) =
    CnotInstr
      (qbit_apply_swaps swaps control)
      (qbit_apply_swaps swaps target).
Proof.
  intros swaps control target.
  rewrite change_qbit_instr_swaps_eq.
  reflexivity.
Qed.

Lemma qbit_apply_swaps_change_qbit_instr_swaps_swap :
  forall swaps qbit1 qbit2,
    change_qbit_instr_swaps swaps (SwapInstr qbit1 qbit2) =
    SwapInstr
      (qbit_apply_swaps swaps qbit1)
      (qbit_apply_swaps swaps qbit2).
Proof.
  intros swaps qbit1 qbit2.
  rewrite change_qbit_instr_swaps_eq.
  reflexivity.
Qed.

Lemma change_qbit_instr_swaps_equiv :
  forall nq swaps instr1 instr2,
    Forall (qbit_pair_valid nq) swaps ->
    Instruction_equiv nq instr1 instr2 ->
    Instruction_equiv nq
      (change_qbit_instr_swaps swaps instr1)
      (change_qbit_instr_swaps swaps instr2).
Proof.
  intros nq swaps.
  induction swaps as [| [qbit1 qbit2] rest IH];
    intros instr1 instr2 Hvalid Hequiv.
  - exact Hequiv.
  - inversion Hvalid as [| ? ? Hpair Hrest]; subst.
    apply IH; [exact Hrest |].
    destruct Hpair as [Hqbit1 Hqbit2].
    assert (Hwrap1 :
      Instruction_equiv nq
        qasm{ swap qbit1 qbit2; $(instr1); swap qbit1 qbit2 }
        (swap_qbit_instr qbit1 qbit2 instr1)).
    {
      rewrite <- (swap_swap_instr qbit1 qbit2 instr1) at 1.
      apply Transform_swap_swap_insert; assumption.
    }
    assert (Hwrap2 :
      Instruction_equiv nq
        qasm{ swap qbit1 qbit2; $(instr2); swap qbit1 qbit2 }
        (swap_qbit_instr qbit1 qbit2 instr2)).
    {
      rewrite <- (swap_swap_instr qbit1 qbit2 instr2) at 1.
      apply Transform_swap_swap_insert; assumption.
    }
    symmetry in Hwrap1.
    etransitivity; [exact Hwrap1 |].
    etransitivity.
    + apply Instruction_equiv_rewrite.
      exact Hequiv.
    + exact Hwrap2.
Qed.

Definition standard_pattern_gate_qbits
    (gate : StandardPatternGate)
    : list nat :=
  match gate with
  | SPG_Std _ qbit =>
      [qbit]
  | SPG_Cnot control target =>
      [control; target]
  | SPG_Swap qbit1 qbit2 =>
      [qbit1; qbit2]
  end.

Definition standard_pattern_sequence_qbits
    (gates : list StandardPatternGate)
    : list nat :=
  List.concat (map standard_pattern_gate_qbits gates).

Fixpoint qbit_pairs_of_vars
    (subst : PatternMap)
    (vars : list nat)
    : option (list qbit_swap_pair) :=
  match vars with
  | [] =>
      Some []
  | var :: rest =>
      let* actual := NatMap.find var (pattern_qbit_map subst) in
      let* pairs := qbit_pairs_of_vars subst rest in
      Some ((var, actual) :: pairs)
  end.

Definition qbit_swaps_for_standard_sequence
    (subst : PatternMap)
    (gates : list StandardPatternGate)
    : option (list qbit_swap_pair) :=
  let vars := nodup Nat.eq_dec (standard_pattern_sequence_qbits gates) in
  let* pairs := qbit_pairs_of_vars subst vars in
  Some (qbit_swaps_for_pairs pairs).

Lemma standard_pattern_gate_qbits_to_instruction_patterns :
  forall gate,
    InstructionPattern_qbit_vars
      (standard_pattern_gate_to_instruction_pattern gate) =
    standard_pattern_gate_qbits gate.
Proof.
  intros [gate qbit | control target | qbit1 qbit2];
    simpl; try reflexivity.
  destruct gate; reflexivity.
Qed.

Lemma standard_pattern_sequence_qbits_to_instruction_patterns :
  forall gates,
    InstructionPattern_list_qbit_vars
      (standard_pattern_sequence_to_instruction_patterns gates) =
    standard_pattern_sequence_qbits gates.
Proof.
  intros gates.
  unfold InstructionPattern_list_qbit_vars,
    standard_pattern_sequence_to_instruction_patterns,
    standard_pattern_sequence_qbits.
  induction gates as [| gate rest IH]; simpl.
  - reflexivity.
  - rewrite standard_pattern_gate_qbits_to_instruction_patterns.
    rewrite IH.
    reflexivity.
Qed.

Lemma standard_pattern_gate_qbit_bound :
  forall gate qbit,
    In qbit (standard_pattern_gate_qbits gate) ->
    qbit < standard_pattern_gate_nqubits gate.
Proof.
  intros [gate target | control target | qbit1 qbit2] qbit Hin;
    simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]; subst; try contradiction
    end;
    lia.
Qed.

Lemma standard_pattern_sequence_qbit_bound :
  forall gates qbit,
    In qbit (standard_pattern_sequence_qbits gates) ->
    qbit < standard_pattern_sequence_nqubits gates.
Proof.
  induction gates as [| gate rest IH]; intros qbit Hin.
  - simpl in Hin. contradiction.
  - unfold standard_pattern_sequence_qbits in Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + simpl.
      pose proof (standard_pattern_gate_qbit_bound gate qbit Hin).
      lia.
    + simpl.
      specialize (IH qbit Hin).
      lia.
Qed.

Lemma standard_pattern_rule_lhs_qbit_bound :
  forall lhs rhs qbit,
    In qbit (standard_pattern_sequence_qbits lhs) ->
    qbit < standard_pattern_rule_nqubits lhs rhs.
Proof.
  intros lhs rhs qbit Hin.
  unfold standard_pattern_rule_nqubits.
  pose proof (standard_pattern_sequence_qbit_bound lhs qbit Hin).
  lia.
Qed.

Lemma standard_pattern_rule_rhs_qbit_bound :
  forall lhs rhs qbit,
    In qbit (standard_pattern_sequence_qbits rhs) ->
    qbit < standard_pattern_rule_nqubits lhs rhs.
Proof.
  intros lhs rhs qbit Hin.
  unfold standard_pattern_rule_nqubits.
  pose proof (standard_pattern_sequence_qbit_bound rhs qbit Hin).
  lia.
Qed.

Definition qbit_pair_avoids (qbit : nat) (pair : qbit_swap_pair) : Prop :=
  fst pair <> qbit /\ snd pair <> qbit.

Lemma swap_qbit_eq_iff :
  forall qbit1 qbit2 qbit result,
    swap_qbit qbit1 qbit2 qbit = result ->
    qbit = swap_qbit qbit1 qbit2 result.
Proof.
  intros qbit1 qbit2 qbit result H.
  rewrite <- H.
  rewrite swap_swap_qbit.
  reflexivity.
Qed.

Lemma swap_qbit_neq :
  forall qbit1 qbit2 qbit result,
    qbit <> result ->
    qbit1 <> result ->
    qbit2 <> result ->
    swap_qbit qbit1 qbit2 qbit <> result.
Proof.
  intros qbit1 qbit2 qbit result Hqbit Hqbit1 Hqbit2 Heq.
  apply swap_qbit_eq_iff in Heq.
  unfold swap_qbit in Heq.
  destruct (Nat.eq_dec result qbit1) as [Hres1 | Hres1];
    [subst; contradiction |].
  destruct (Nat.eq_dec result qbit2) as [Hres2 | Hres2];
    [subst; contradiction |].
  contradiction.
Qed.

Lemma qbit_pair_swap_fst_avoids :
  forall qbit qbit1 qbit2 pair,
    qbit_pair_avoids qbit (qbit1, qbit2) ->
    qbit_pair_avoids qbit pair ->
    qbit_pair_avoids qbit (qbit_pair_swap_fst qbit1 qbit2 pair).
Proof.
  intros qbit qbit1 qbit2 [local actual] Hswap Hpair.
  unfold qbit_pair_avoids, qbit_pair_swap_fst in *.
  simpl in *.
  destruct Hswap as [Hqbit1 Hqbit2].
  destruct Hpair as [Hlocal Hactual].
  split.
  - apply swap_qbit_neq; assumption.
  - exact Hactual.
Qed.

Lemma qbit_apply_swaps_avoids :
  forall swaps qbit,
    Forall (qbit_pair_avoids qbit) swaps ->
    qbit_apply_swaps swaps qbit = qbit.
Proof.
  induction swaps as [| [qbit1 qbit2] rest IH]; intros qbit Havoid.
  - reflexivity.
  - inversion Havoid as [| ? ? Hhead Hrest]; subst.
    simpl.
    unfold qbit_pair_avoids in Hhead.
    simpl in Hhead.
    destruct Hhead as [Hqbit1 Hqbit2].
    unfold swap_qbit.
    destruct (Nat.eq_dec qbit qbit1) as [Heq1 | Heq1];
      [subst; contradiction |].
    destruct (Nat.eq_dec qbit qbit2) as [Heq2 | Heq2];
      [subst; contradiction |].
    apply IH.
    exact Hrest.
Qed.

Lemma qbit_swaps_for_pairs_aux_avoids :
  forall fuel pairs qbit,
    Forall (qbit_pair_avoids qbit) pairs ->
    Forall
      (qbit_pair_avoids qbit)
      (qbit_swaps_for_pairs_aux fuel pairs).
Proof.
  induction fuel as [| fuel IH]; intros pairs qbit Havoid.
  - simpl. constructor.
  - destruct pairs as [| [local actual] rest].
    + constructor.
    + simpl.
      inversion Havoid as [| ? ? Hhead Hrest]; subst.
      constructor.
      * exact Hhead.
      * apply IH.
        apply Forall_forall.
        intros pair Hin.
        apply in_map_iff in Hin as [[local' actual'] [Hpair Hin]].
        subst.
        apply qbit_pair_swap_fst_avoids.
        -- exact Hhead.
        -- rewrite Forall_forall in Hrest.
           apply Hrest.
           exact Hin.
Qed.

Lemma qbit_apply_swaps_for_pairs_aux_avoids :
  forall fuel pairs qbit,
    Forall (qbit_pair_avoids qbit) pairs ->
    qbit_apply_swaps (qbit_swaps_for_pairs_aux fuel pairs) qbit = qbit.
Proof.
  intros fuel pairs qbit Havoid.
  apply qbit_apply_swaps_avoids.
  apply qbit_swaps_for_pairs_aux_avoids.
  exact Havoid.
Qed.

Lemma NoDup_map_swap_qbit :
  forall qbit1 qbit2 qbits,
    NoDup qbits ->
    NoDup (map (swap_qbit qbit1 qbit2) qbits).
Proof.
  intros qbit1 qbit2 qbits Hnodup.
  induction Hnodup as [| qbit qbits Hnotin Hnodup IH].
  - constructor.
  - simpl.
    constructor.
    + intros Hin.
      apply in_map_iff in Hin as [qbit' [Heq Hin]].
      apply Hnotin.
      apply swap_qbit_eq_iff in Heq.
      subst.
      rewrite swap_swap_qbit in Hin.
      exact Hin.
    + exact IH.
Qed.

Lemma qbit_swaps_for_pairs_aux_valid :
  forall nq fuel pairs,
    Forall (qbit_pair_valid nq) pairs ->
    Forall
      (qbit_pair_valid nq)
      (qbit_swaps_for_pairs_aux fuel pairs).
Proof.
  induction fuel as [| fuel IH]; intros pairs Hvalid.
  - constructor.
  - destruct pairs as [| [local actual] rest].
    + constructor.
    + simpl.
      inversion Hvalid as [| ? ? Hhead Hrest]; subst.
      constructor.
      * exact Hhead.
      * apply IH.
        apply Forall_forall.
        intros [local' actual'] Hin.
        apply in_map_iff in Hin as [[rest_local rest_actual] [Hpair Hin]].
        inversion Hpair; subst; clear Hpair.
        rewrite Forall_forall in Hrest.
        specialize (Hrest _ Hin).
        unfold qbit_pair_valid in *.
        simpl in *.
        destruct Hhead as [Hlocal Hactual].
        destruct Hrest as [Hrest_local Hrest_actual].
        split.
        -- apply swap_qbit_bound; assumption.
        -- exact Hrest_actual.
Qed.

Lemma qbit_swaps_for_pairs_valid :
  forall nq pairs,
    Forall (qbit_pair_valid nq) pairs ->
    Forall (qbit_pair_valid nq) (qbit_swaps_for_pairs pairs).
Proof.
  intros nq pairs Hvalid.
  unfold qbit_swaps_for_pairs.
  apply qbit_swaps_for_pairs_aux_valid.
  exact Hvalid.
Qed.

Lemma qbit_pair_swap_fst_fsts :
  forall qbit1 qbit2 pairs,
    map fst (map (qbit_pair_swap_fst qbit1 qbit2) pairs) =
    map (swap_qbit qbit1 qbit2) (map fst pairs).
Proof.
  intros qbit1 qbit2 pairs.
  induction pairs as [| [local actual] rest IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma qbit_pair_swap_fst_snds :
  forall qbit1 qbit2 pairs,
    map snd (map (qbit_pair_swap_fst qbit1 qbit2) pairs) =
    map snd pairs.
Proof.
  intros qbit1 qbit2 pairs.
  induction pairs as [| [local actual] rest IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma qbit_swaps_for_pairs_aux_realize :
  forall fuel pairs local actual,
    fuel = List.length pairs ->
    NoDup (map fst pairs) ->
    NoDup (map snd pairs) ->
    In (local, actual) pairs ->
    qbit_apply_swaps
      (qbit_swaps_for_pairs_aux fuel pairs)
      local =
    actual.
Proof.
  induction fuel as [| fuel IH];
    intros pairs local actual Hfuel Hnodup_fst Hnodup_snd Hin.
  - destruct pairs; simpl in *; try discriminate.
    contradiction.
  - destruct pairs as [| [head_local head_actual] rest].
    + contradiction.
    + simpl in Hfuel.
      inversion Hfuel; subst; clear Hfuel.
      simpl in Hin.
      simpl in Hnodup_fst.
      simpl in Hnodup_snd.
      inversion Hnodup_fst as [| ? ? Hhead_fst_notin Hrest_fst_nodup];
        subst; clear Hnodup_fst.
      inversion Hnodup_snd as [| ? ? Hhead_snd_notin Hrest_snd_nodup];
        subst; clear Hnodup_snd.
      destruct Hin as [Hin | Hin].
      * inversion Hin; subst; clear Hin.
        simpl.
        rewrite swap_qbit_left.
        apply qbit_apply_swaps_for_pairs_aux_avoids.
        apply Forall_forall.
        intros [rest_local rest_actual] Hrest_pair.
        apply in_map_iff in Hrest_pair
          as [[orig_local orig_actual] [Hpair Horig_in]].
        inversion Hpair; subst; clear Hpair.
        unfold qbit_pair_avoids, qbit_pair_swap_fst.
        simpl.
        split.
        -- intros Hcontra.
           apply swap_qbit_eq_iff in Hcontra.
           rewrite swap_qbit_right in Hcontra.
           subst.
           apply Hhead_fst_notin.
           apply in_map with (f := fst) in Horig_in.
           exact Horig_in.
        -- intros Hcontra.
           subst.
           apply Hhead_snd_notin.
           apply in_map with (f := snd) in Horig_in.
           exact Horig_in.
      * simpl.
        eapply IH.
        -- rewrite length_map. reflexivity.
        -- rewrite qbit_pair_swap_fst_fsts.
           apply NoDup_map_swap_qbit.
           exact Hrest_fst_nodup.
        -- rewrite qbit_pair_swap_fst_snds.
           exact Hrest_snd_nodup.
        -- change
             (In
               (qbit_pair_swap_fst head_local head_actual (local, actual))
               (map (qbit_pair_swap_fst head_local head_actual) rest)).
           apply in_map.
           exact Hin.
Qed.

Lemma qbit_swaps_for_pairs_realize :
  forall pairs local actual,
    NoDup (map fst pairs) ->
    NoDup (map snd pairs) ->
    In (local, actual) pairs ->
    qbit_apply_swaps (qbit_swaps_for_pairs pairs) local = actual.
Proof.
  intros pairs local actual Hnodup_fst Hnodup_snd Hin.
  unfold qbit_swaps_for_pairs.
  eapply qbit_swaps_for_pairs_aux_realize; eauto.
Qed.

Lemma qbit_pairs_of_vars_fsts :
  forall subst vars pairs,
    qbit_pairs_of_vars subst vars = Some pairs ->
    map fst pairs = vars.
Proof.
  intros subst vars.
  induction vars as [| var rest IH]; intros pairs Hpairs.
  - simpl in Hpairs.
    inversion Hpairs; reflexivity.
  - simpl in Hpairs.
    destruct (NatMap.find var (pattern_qbit_map subst)) as [actual |]
      eqn:Hfind; try discriminate.
    destruct (qbit_pairs_of_vars subst rest) as [rest_pairs |]
      eqn:Hrest; try discriminate.
    inversion Hpairs; subst; clear Hpairs.
    simpl.
    rewrite (IH rest_pairs eq_refl).
    reflexivity.
Qed.

Lemma qbit_pairs_of_vars_find_in :
  forall subst vars pairs var actual,
    qbit_pairs_of_vars subst vars = Some pairs ->
    In var vars ->
    NatMap.find var (pattern_qbit_map subst) = Some actual ->
    In (var, actual) pairs.
Proof.
  intros subst vars.
  induction vars as [| head rest IH];
    intros pairs var actual Hpairs Hin Hfind.
  - contradiction.
  - simpl in Hpairs.
    destruct (NatMap.find head (pattern_qbit_map subst)) as [head_actual |]
      eqn:Hhead; try discriminate.
    destruct (qbit_pairs_of_vars subst rest) as [rest_pairs |]
      eqn:Hrest; try discriminate.
    inversion Hpairs; subst; clear Hpairs.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + subst.
      rewrite Hhead in Hfind.
      inversion Hfind; subst.
      simpl.
      left.
      reflexivity.
    + simpl.
      right.
      eapply IH; [exact eq_refl | exact Hin | exact Hfind].
Qed.

Lemma qbit_pairs_of_vars_find_exists :
  forall subst vars pairs var,
    qbit_pairs_of_vars subst vars = Some pairs ->
    In var vars ->
    exists actual,
      NatMap.find var (pattern_qbit_map subst) = Some actual /\
      In (var, actual) pairs.
Proof.
  intros subst vars.
  induction vars as [| head rest IH];
    intros pairs var Hpairs Hin.
  - contradiction.
  - simpl in Hpairs.
    destruct (NatMap.find head (pattern_qbit_map subst)) as [head_actual |]
      eqn:Hhead; try discriminate.
    destruct (qbit_pairs_of_vars subst rest) as [rest_pairs |]
      eqn:Hrest; try discriminate.
    inversion Hpairs; subst; clear Hpairs.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + subst.
      exists head_actual.
      split; [exact Hhead | simpl; left; reflexivity].
    + destruct (IH rest_pairs var eq_refl Hin) as [actual [Hfind Hpair]].
      exists actual.
      split; [exact Hfind | simpl; right; exact Hpair].
Qed.

Lemma qbit_pairs_of_vars_pair_find :
  forall subst vars pairs var actual,
    qbit_pairs_of_vars subst vars = Some pairs ->
    In (var, actual) pairs ->
    NatMap.find var (pattern_qbit_map subst) = Some actual.
Proof.
  intros subst vars.
  induction vars as [| head rest IH];
    intros pairs var actual Hpairs Hin.
  - simpl in Hpairs.
    inversion Hpairs; subst.
    contradiction.
  - simpl in Hpairs.
    destruct (NatMap.find head (pattern_qbit_map subst)) as [head_actual |]
      eqn:Hhead; try discriminate.
    destruct (qbit_pairs_of_vars subst rest) as [rest_pairs |]
      eqn:Hrest; try discriminate.
    inversion Hpairs; subst; clear Hpairs.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      exact Hhead.
    + eapply IH.
      * exact eq_refl.
      * exact Hin.
Qed.

Lemma qbit_pairs_of_vars_snds_nodup :
  forall subst vars pairs,
    PatternMap_distinct subst ->
    NoDup vars ->
    qbit_pairs_of_vars subst vars = Some pairs ->
    NoDup (map snd pairs).
Proof.
  intros subst vars.
  induction vars as [| var rest IH]; intros pairs Hdistinct Hnodup Hpairs.
  - simpl in Hpairs.
    inversion Hpairs; subst.
    constructor.
  - simpl in Hpairs.
    destruct (NatMap.find var (pattern_qbit_map subst)) as [actual |]
      eqn:Hfind; try discriminate.
    destruct (qbit_pairs_of_vars subst rest) as [rest_pairs |]
      eqn:Hrest; try discriminate.
    inversion Hpairs; subst; clear Hpairs.
    simpl.
    inversion Hnodup as [| ? ? Hnotin Hrest_nodup]; subst.
    constructor.
    + intros Hin_actual.
      apply in_map_iff in Hin_actual
        as [[rest_var rest_actual] [Hactual_eq Hpair_in]].
      simpl in Hactual_eq.
      subst rest_actual.
      assert (Hrest_find :
        NatMap.find rest_var (pattern_qbit_map subst) = Some actual).
      {
        eapply qbit_pairs_of_vars_pair_find.
        - exact Hrest.
        - exact Hpair_in.
      }
      assert (Hvar_eq : rest_var = var).
      {
        eapply (proj1 Hdistinct).
        - exact Hrest_find.
        - exact Hfind.
      }
      subst rest_var.
      apply Hnotin.
      apply in_map with (f := fst) in Hpair_in.
      rewrite (qbit_pairs_of_vars_fsts subst rest rest_pairs Hrest)
        in Hpair_in.
      exact Hpair_in.
    + eapply IH; eauto.
Qed.

Lemma qbit_pairs_of_vars_valid :
  forall nq subst vars pairs,
    (forall var actual,
      In var vars ->
      NatMap.find var (pattern_qbit_map subst) = Some actual ->
      Qbit_index_valid nq var /\ Qbit_index_valid nq actual) ->
    qbit_pairs_of_vars subst vars = Some pairs ->
    Forall (qbit_pair_valid nq) pairs.
Proof.
  intros nq subst vars.
  induction vars as [| var rest IH]; intros pairs Hvalid Hpairs.
  - simpl in Hpairs.
    inversion Hpairs; subst.
    constructor.
  - simpl in Hpairs.
    destruct (NatMap.find var (pattern_qbit_map subst)) as [actual |]
      eqn:Hfind; try discriminate.
    destruct (qbit_pairs_of_vars subst rest) as [rest_pairs |]
      eqn:Hrest; try discriminate.
    inversion Hpairs; subst; clear Hpairs.
    constructor.
    + unfold qbit_pair_valid.
      simpl.
      apply Hvalid.
      * simpl; left; reflexivity.
      * exact Hfind.
    + eapply IH.
      * intros rest_var rest_actual Hin Hfind_rest.
        apply Hvalid.
        -- simpl; right; exact Hin.
        -- exact Hfind_rest.
      * exact eq_refl.
Qed.

Lemma standard_pattern_gate_instruction_change_swaps :
  forall subst swaps gate instr,
    (forall qbit actual,
      In qbit (standard_pattern_gate_qbits gate) ->
      NatMap.find qbit (pattern_qbit_map subst) = Some actual ->
      qbit_apply_swaps swaps qbit = actual) ->
    standard_pattern_gate_instruction subst gate = Some instr ->
    instr =
    change_qbit_instr_swaps swaps
      (standard_pattern_gate_local_instruction gate).
Proof.
  intros subst swaps [gate qbit | control target | qbit1 qbit2] instr Hreal Hinst.
  - simpl in Hinst.
    destruct (NatMap.find qbit (pattern_qbit_map subst)) as [actual |]
      eqn:Hfind; try discriminate.
    inversion Hinst; subst; clear Hinst.
    change
      (standard_gate_instruction gate actual =
       change_qbit_instr_swaps swaps (standard_gate_instruction gate qbit)).
    rewrite qbit_apply_swaps_change_qbit_instr_swaps_standard_gate.
    rewrite (Hreal qbit actual); [reflexivity | simpl; auto | exact Hfind].
  - simpl in Hinst.
    destruct (NatMap.find control (pattern_qbit_map subst)) as [control' |]
      eqn:Hcontrol; try discriminate.
    destruct (NatMap.find target (pattern_qbit_map subst)) as [target' |]
      eqn:Htarget; try discriminate.
    inversion Hinst; subst; clear Hinst.
    change
      (CnotInstr control' target' =
       change_qbit_instr_swaps swaps (CnotInstr control target)).
    rewrite qbit_apply_swaps_change_qbit_instr_swaps_cnot.
    rewrite (Hreal control control');
      [| simpl; auto | exact Hcontrol].
    rewrite (Hreal target target');
      [reflexivity | simpl; auto | exact Htarget].
  - simpl in Hinst.
    destruct (NatMap.find qbit1 (pattern_qbit_map subst)) as [qbit1' |]
      eqn:Hqbit1; try discriminate.
    destruct (NatMap.find qbit2 (pattern_qbit_map subst)) as [qbit2' |]
      eqn:Hqbit2; try discriminate.
    inversion Hinst; subst; clear Hinst.
    change
      (SwapInstr qbit1' qbit2' =
       change_qbit_instr_swaps swaps (SwapInstr qbit1 qbit2)).
    rewrite qbit_apply_swaps_change_qbit_instr_swaps_swap.
    rewrite (Hreal qbit1 qbit1');
      [| simpl; auto | exact Hqbit1].
    rewrite (Hreal qbit2 qbit2');
      [reflexivity | simpl; auto | exact Hqbit2].
Qed.

Lemma standard_pattern_sequence_instructions_change_swaps :
  forall subst swaps gates instrs,
    (forall qbit actual,
      In qbit (standard_pattern_sequence_qbits gates) ->
      NatMap.find qbit (pattern_qbit_map subst) = Some actual ->
      qbit_apply_swaps swaps qbit = actual) ->
    standard_pattern_sequence_instructions subst gates = Some instrs ->
    instrs =
    map
      (change_qbit_instr_swaps swaps)
      (standard_pattern_sequence_local_instructions gates).
Proof.
  intros subst swaps gates.
  induction gates as [| gate rest IH]; intros instrs Hreal Hinst.
  - simpl in Hinst.
    inversion Hinst; reflexivity.
  - simpl in Hinst.
    destruct (standard_pattern_gate_instruction subst gate) as [instr |]
      eqn:Hgate; try discriminate.
    destruct (standard_pattern_sequence_instructions subst rest) as [rest_instrs |]
      eqn:Hrest; try discriminate.
    inversion Hinst; subst; clear Hinst.
    simpl.
    f_equal.
    + eapply standard_pattern_gate_instruction_change_swaps.
      * intros qbit actual Hin Hfind.
        apply Hreal.
        -- unfold standard_pattern_sequence_qbits.
           simpl.
           apply in_or_app.
           left.
           exact Hin.
        -- exact Hfind.
      * exact Hgate.
    + eapply IH.
      * intros qbit actual Hin Hfind.
        apply Hreal.
        -- unfold standard_pattern_sequence_qbits.
           simpl.
           apply in_or_app.
           right.
           exact Hin.
        -- exact Hfind.
      * exact eq_refl.
Qed.

Lemma standard_pattern_sequence_find_valid :
  forall nq subst gates instrs qbit,
    standard_pattern_sequence_instructions subst gates = Some instrs ->
    Instruction_list_qbits_valid nq instrs ->
    In qbit (standard_pattern_sequence_qbits gates) ->
    exists actual,
      NatMap.find qbit (pattern_qbit_map subst) = Some actual /\
      Qbit_index_valid nq actual.
Proof.
  intros nq subst gates.
  induction gates as [| gate rest IH]; intros instrs qbit Hinst Hvalid Hin.
  - simpl in Hin. contradiction.
  - simpl in Hinst.
    destruct (standard_pattern_gate_instruction subst gate) as [instr |]
      eqn:Hgate; try discriminate.
    destruct (standard_pattern_sequence_instructions subst rest) as [rest_instrs |]
      eqn:Hrest; try discriminate.
    inversion Hinst; subst; clear Hinst.
    inversion Hvalid as [| ? ? Hgate_valid Hrest_valid]; subst.
    unfold standard_pattern_sequence_qbits in Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + destruct gate as [gate gate_qbit | control target | qbit1 qbit2].
      * simpl in Hgate.
        destruct (NatMap.find gate_qbit (pattern_qbit_map subst)) as [actual |]
          eqn:Hfind; try discriminate.
        inversion Hgate; subst; clear Hgate.
        simpl in Hin.
        destruct Hin as [Hin | Hin]; [subst | contradiction].
        destruct gate; simpl in Hgate_valid;
          inversion Hgate_valid; subst;
          exists actual; split; try exact Hfind; assumption.
      * simpl in Hgate.
        destruct (NatMap.find control (pattern_qbit_map subst)) as [control' |]
          eqn:Hcontrol; try discriminate.
        destruct (NatMap.find target (pattern_qbit_map subst)) as [target' |]
          eqn:Htarget; try discriminate.
        inversion Hgate; subst; clear Hgate.
        simpl in Hin.
        inversion Hgate_valid; subst.
        destruct Hin as [Hin | [Hin | Hin]]; subst; try contradiction.
        -- exists control'.
           split.
           ++ exact Hcontrol.
           ++ match goal with
              | H : Qbit_index_valid nq control' |- _ => exact H
              end.
        -- exists target'.
           split.
           ++ exact Htarget.
           ++ match goal with
              | H : Qbit_index_valid nq target' |- _ => exact H
              end.
      * simpl in Hgate.
        destruct (NatMap.find qbit1 (pattern_qbit_map subst)) as [qbit1' |]
          eqn:Hqbit1; try discriminate.
        destruct (NatMap.find qbit2 (pattern_qbit_map subst)) as [qbit2' |]
          eqn:Hqbit2; try discriminate.
        inversion Hgate; subst; clear Hgate.
        simpl in Hin.
        inversion Hgate_valid; subst.
        destruct Hin as [Hin | [Hin | Hin]]; subst; try contradiction.
        -- exists qbit1'.
           split.
           ++ exact Hqbit1.
           ++ match goal with
              | H : Qbit_index_valid nq qbit1' |- _ => exact H
              end.
        -- exists qbit2'.
           split.
           ++ exact Hqbit2.
           ++ match goal with
              | H : Qbit_index_valid nq qbit2' |- _ => exact H
              end.
    + eapply IH; eauto.
Qed.

Lemma qbit_pairs_of_vars_complete :
  forall subst vars,
    (forall var,
      In var vars ->
      exists actual,
        NatMap.find var (pattern_qbit_map subst) = Some actual) ->
    exists pairs,
      qbit_pairs_of_vars subst vars = Some pairs.
Proof.
  intros subst vars.
  induction vars as [| var rest IH]; intros Hcomplete.
  - exists [].
    reflexivity.
  - destruct (Hcomplete var) as [actual Hfind].
    + simpl; left; reflexivity.
    + destruct IH as [rest_pairs Hrest].
      * intros rest_var Hin.
        apply Hcomplete.
        simpl; right; exact Hin.
      * simpl.
        rewrite Hfind.
        rewrite Hrest.
        exists ((var, actual) :: rest_pairs).
        reflexivity.
Qed.

Lemma standard_pattern_rule_safe_qbits :
  forall lhs rhs,
    RewriteRule_safe (standard_pattern_rewrite_rule lhs rhs) ->
    list_subset
      (standard_pattern_sequence_qbits rhs)
      (standard_pattern_sequence_qbits lhs).
Proof.
  intros lhs rhs Hsafe.
  unfold RewriteRule_safe, standard_pattern_rewrite_rule in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [Hqbits _].
  rewrite <- standard_pattern_sequence_qbits_to_instruction_patterns.
  rewrite <- standard_pattern_sequence_qbits_to_instruction_patterns.
  exact Hqbits.
Qed.

Lemma change_qbit_instr_swaps_seq :
  forall swaps instrs,
    change_qbit_instr_swaps swaps (SeqInstr instrs) =
    SeqInstr (map (change_qbit_instr_swaps swaps) instrs).
Proof.
  intros swaps instrs.
  rewrite change_qbit_instr_swaps_eq.
  simpl.
  f_equal.
  induction instrs as [| instr rest IH].
  - reflexivity.
  - simpl.
    rewrite <- change_qbit_instr_swaps_eq.
    rewrite IH.
    reflexivity.
Qed.

Definition standard_pattern_gate_complex_matrix
    (nq : nat)
    (gate : StandardPatternGate)
    : Matrix nq :=
  match gate with
  | SPG_Std gate qbit =>
      mat_single nq qbit (standard_gate_complex_matrix gate)
  | SPG_Cnot control target =>
      mat_cnot control target
  | SPG_Swap qbit1 qbit2 =>
      mat_swap qbit1 qbit2
  end.

Fixpoint standard_pattern_sequence_complex_matrices
    (nq : nat)
    (gates : list StandardPatternGate)
    : list (Matrix nq) :=
  match gates with
  | [] =>
      []
  | gate :: rest =>
      standard_pattern_gate_complex_matrix nq gate
      :: standard_pattern_sequence_complex_matrices nq rest
  end.

Lemma Matrix_of_standard_pattern_sequence_local :
  forall nq gates,
    Matrix_of_list nq
      (standard_pattern_sequence_local_instructions gates)
      (standard_pattern_sequence_complex_matrices nq gates).
Proof.
  induction gates as [| gate rest IH]; simpl.
  - apply nil_mat.
  - destruct gate as [gate qbit | control target | qbit1 qbit2]; simpl; apply cons_mat.
    + apply Matrix_of_standard_gate_multi.
    + apply IH.
    + apply Matrix_of_cnot.
    + apply IH.
    + apply Matrix_of_swap.
    + apply IH.
Qed.

Lemma standard_pattern_sequence_matrix_sound_same_dimension :
  forall nq gates matrix,
    standard_pattern_sequence_matrix nq gates = Some matrix ->
    fold_right
      (fun mat acc => mat_mul acc mat)
      mat_eye
      (standard_pattern_sequence_complex_matrices nq gates) =
    complex_of_domega_matrix matrix.
Proof.
  induction gates as [| gate rest IH]; intros matrix Hmatrix.
  - simpl in Hmatrix.
    inversion Hmatrix; subst; clear Hmatrix.
    rewrite complex_of_domega_matrix_eye.
    reflexivity.
  - destruct gate as [gate qbit | control target | qbit1 qbit2].
    + simpl in Hmatrix.
      destruct (qbit_in_bounds nq qbit) eqn:Hbound; try discriminate.
      destruct (standard_pattern_sequence_matrix nq rest) as [rest_matrix|]
        eqn:Hrest; try discriminate.
      inversion Hmatrix; subst; clear Hmatrix.
      simpl.
      rewrite (IH rest_matrix eq_refl).
      rewrite complex_of_domega_matrix_mul.
      rewrite complex_of_domega_matrix_single.
      reflexivity.
    + simpl in Hmatrix.
      destruct
        (Nat.eqb control target || negb (qbit_pair_in_bounds nq control target))
        eqn:Hinvalid; try discriminate.
      destruct (standard_pattern_sequence_matrix nq rest) as [rest_matrix|]
        eqn:Hrest; try discriminate.
      inversion Hmatrix; subst; clear Hmatrix.
      simpl.
      rewrite (IH rest_matrix eq_refl).
      rewrite complex_of_domega_matrix_mul.
      rewrite complex_of_domega_matrix_cnot.
      reflexivity.
    + simpl in Hmatrix.
      destruct
        (Nat.eqb qbit1 qbit2 || negb (qbit_pair_in_bounds nq qbit1 qbit2))
        eqn:Hinvalid; try discriminate.
      destruct (standard_pattern_sequence_matrix nq rest) as [rest_matrix|]
        eqn:Hrest; try discriminate.
      inversion Hmatrix; subst; clear Hmatrix.
      simpl.
      rewrite (IH rest_matrix eq_refl).
      rewrite complex_of_domega_matrix_mul.
      rewrite complex_of_domega_matrix_swap.
      reflexivity.
Qed.

Lemma standard_pattern_gate_complex_matrix_extend_right :
  forall n extra gate matrix,
    standard_pattern_gate_matrix n gate = Some matrix ->
    standard_pattern_gate_complex_matrix (n + extra) gate =
    standard_pattern_gate_complex_matrix n gate ⊗ @mat_eye extra.
Proof.
  intros n extra [gate qbit | control target | qbit1 qbit2] matrix Hmatrix.
  - simpl in Hmatrix.
    destruct (qbit_in_bounds n qbit) eqn:Hbound; try discriminate.
    apply Nat.ltb_lt in Hbound.
    simpl.
    apply mat_single_break_left.
    exact Hbound.
  - simpl in Hmatrix.
    destruct
      (Nat.eqb control target || negb (qbit_pair_in_bounds n control target))
      eqn:Hinvalid; try discriminate.
    apply Bool.orb_false_iff in Hinvalid as [Hneq Hbounds].
    apply Nat.eqb_neq in Hneq.
    apply Bool.negb_false_iff in Hbounds.
    unfold qbit_pair_in_bounds, qbit_in_bounds in Hbounds.
    apply Bool.andb_true_iff in Hbounds as [Hcontrol Htarget].
    apply Nat.ltb_lt in Hcontrol.
    apply Nat.ltb_lt in Htarget.
    simpl.
    apply mat_cnot_extend_right; assumption.
  - simpl in Hmatrix.
    destruct
      (Nat.eqb qbit1 qbit2 || negb (qbit_pair_in_bounds n qbit1 qbit2))
      eqn:Hinvalid; try discriminate.
    apply Bool.orb_false_iff in Hinvalid as [Hneq Hbounds].
    apply Nat.eqb_neq in Hneq.
    apply Bool.negb_false_iff in Hbounds.
    unfold qbit_pair_in_bounds, qbit_in_bounds in Hbounds.
    apply Bool.andb_true_iff in Hbounds as [Hqbit1 Hqbit2].
    apply Nat.ltb_lt in Hqbit1.
    apply Nat.ltb_lt in Hqbit2.
    simpl.
    apply mat_swap_extend_right; assumption.
Qed.

Lemma standard_pattern_sequence_complex_matrices_extend_right :
  forall n extra gates matrix,
    standard_pattern_sequence_matrix n gates = Some matrix ->
    fold_right
      (fun mat acc => mat_mul acc mat)
      mat_eye
      (standard_pattern_sequence_complex_matrices (n + extra) gates) =
    fold_right
      (fun mat acc => mat_mul acc mat)
      mat_eye
      (standard_pattern_sequence_complex_matrices n gates)
    ⊗ @mat_eye extra.
Proof.
  induction gates as [| gate rest IH]; intros matrix Hmatrix.
  - simpl.
    symmetry.
    apply tprod_eye_eye.
  - simpl in Hmatrix.
    destruct (standard_pattern_gate_matrix n gate) as [gate_matrix |]
      eqn:Hgate; try discriminate.
    destruct (standard_pattern_sequence_matrix n rest) as [rest_matrix |]
      eqn:Hrest; try discriminate.
    inversion Hmatrix; subst; clear Hmatrix.
    simpl.
    rewrite (standard_pattern_gate_complex_matrix_extend_right
      n extra gate gate_matrix Hgate).
    rewrite (IH rest_matrix eq_refl).
    rewrite tprod_mul.
    mat_simpl.
Qed.

Lemma standard_pattern_transform_validb_matrix_list_sound_bound :
  forall nq lhs rhs,
    standard_pattern_transform_validb lhs rhs = true ->
    standard_pattern_rule_nqubits lhs rhs <= nq ->
    exists lambda,
      fold_right
        (fun mat acc => mat_mul acc mat)
        mat_eye
        (standard_pattern_sequence_complex_matrices nq lhs) =
      mat_scale
        (gphase lambda)
        (fold_right
           (fun mat acc => mat_mul acc mat)
           mat_eye
           (standard_pattern_sequence_complex_matrices nq rhs)).
Proof.
  intros nq lhs rhs Hvalid Hbound.
  unfold standard_pattern_transform_validb in Hvalid.
  set (n0 := standard_pattern_rule_nqubits lhs rhs) in *.
  destruct (standard_pattern_sequence_matrix n0 lhs) as [lhs_matrix |]
    eqn:Hlhs; try discriminate.
  destruct (standard_pattern_sequence_matrix n0 rhs) as [rhs_matrix |]
    eqn:Hrhs; try discriminate.
  apply domega_matrix_eq_up_to_phaseb_sound in Hvalid
    as [phase [Hphase_in Hphase_eq]].
  destruct (domega_phase_gphase phase Hphase_in) as [lambda Hlambda].
  exists lambda.
  replace nq with (n0 + (nq - n0)) by lia.
  rewrite (standard_pattern_sequence_complex_matrices_extend_right
    n0 (nq - n0) lhs lhs_matrix).
  2: exact Hlhs.
  rewrite (standard_pattern_sequence_complex_matrices_extend_right
    n0 (nq - n0) rhs rhs_matrix).
  2: exact Hrhs.
  rewrite (standard_pattern_sequence_matrix_sound_same_dimension
    n0 lhs lhs_matrix Hlhs).
  rewrite (standard_pattern_sequence_matrix_sound_same_dimension
    n0 rhs rhs_matrix Hrhs).
  rewrite Hphase_eq.
  rewrite <- tprod_scale_assoc.
  rewrite Hlambda.
  reflexivity.
Qed.

Lemma standard_pattern_local_transform_sound :
  forall nq lhs rhs,
    standard_pattern_transform_validb lhs rhs = true ->
    standard_pattern_rule_nqubits lhs rhs <= nq ->
    Instruction_equiv nq
      (SeqInstr (standard_pattern_sequence_local_instructions lhs))
      (SeqInstr (standard_pattern_sequence_local_instructions rhs)).
Proof.
  intros nq lhs rhs Hvalid Hbound.
  eapply Instruction_equiv_of_seqs_from_matrix.
  - apply Matrix_of_standard_pattern_sequence_local.
  - apply Matrix_of_standard_pattern_sequence_local.
  - eapply standard_pattern_transform_validb_matrix_list_sound_bound; eauto.
Qed.

Lemma standard_pattern_sequence_instantiated_swap_sound :
  forall nq subst lhs rhs lhs_instrs rhs_instrs,
    standard_pattern_transform_validb lhs rhs = true ->
    standard_pattern_rule_nqubits lhs rhs <= nq ->
    RewriteRule_safe (standard_pattern_rewrite_rule lhs rhs) ->
    PatternMap_distinct subst ->
    standard_pattern_sequence_instructions subst lhs = Some lhs_instrs ->
    standard_pattern_sequence_instructions subst rhs = Some rhs_instrs ->
    Instruction_list_qbits_valid nq lhs_instrs ->
    Instruction_equiv nq
      (SeqInstr lhs_instrs)
      (SeqInstr rhs_instrs).
Proof.
  intros nq subst lhs rhs lhs_instrs rhs_instrs Hpattern Hbound Hsafe Hdistinct Hlhs Hrhs Hvalid.
  set (lhs_vars := nodup Nat.eq_dec (standard_pattern_sequence_qbits lhs)).
  assert (Hcomplete :
    forall var,
      In var lhs_vars ->
      exists actual,
        NatMap.find var (pattern_qbit_map subst) = Some actual).
  {
    intros var Hin.
    subst lhs_vars.
    apply nodup_In in Hin.
    destruct (standard_pattern_sequence_find_valid
      nq subst lhs lhs_instrs var Hlhs Hvalid Hin)
      as [actual [Hfind _]].
    exists actual.
    exact Hfind.
  }
  destruct (qbit_pairs_of_vars_complete subst lhs_vars Hcomplete)
    as [pairs Hpairs].
  set (swaps := qbit_swaps_for_pairs pairs).
  assert (Hfst_pairs : map fst pairs = lhs_vars).
  {
    eapply qbit_pairs_of_vars_fsts.
    exact Hpairs.
  }
  assert (Hnodup_fst : NoDup (map fst pairs)).
  {
    rewrite Hfst_pairs.
    subst lhs_vars.
    apply NoDup_nodup.
  }
  assert (Hnodup_snd : NoDup (map snd pairs)).
  {
    eapply qbit_pairs_of_vars_snds_nodup.
    - exact Hdistinct.
    - subst lhs_vars.
      apply NoDup_nodup.
    - exact Hpairs.
  }
  assert (Hpairs_valid : Forall (qbit_pair_valid nq) pairs).
  {
    eapply qbit_pairs_of_vars_valid.
    - intros var actual Hin Hfind.
      subst lhs_vars.
      apply nodup_In in Hin.
      split.
      + unfold Qbit_index_valid.
        pose proof (standard_pattern_rule_lhs_qbit_bound lhs rhs var Hin).
        lia.
      + destruct (standard_pattern_sequence_find_valid
          nq subst lhs lhs_instrs var Hlhs Hvalid Hin)
          as [actual' [Hfind' Hactual_valid]].
        rewrite Hfind in Hfind'.
        inversion Hfind'; subst.
        exact Hactual_valid.
    - exact Hpairs.
  }
  assert (Hswaps_valid : Forall (qbit_pair_valid nq) swaps).
  {
    subst swaps.
    apply qbit_swaps_for_pairs_valid.
    exact Hpairs_valid.
  }
  assert (Hreal_lhs :
    forall qbit actual,
      In qbit (standard_pattern_sequence_qbits lhs) ->
      NatMap.find qbit (pattern_qbit_map subst) = Some actual ->
      qbit_apply_swaps swaps qbit = actual).
  {
    intros qbit actual Hin Hfind.
    subst swaps.
    eapply qbit_swaps_for_pairs_realize; eauto.
    eapply qbit_pairs_of_vars_find_in.
    - exact Hpairs.
    - subst lhs_vars.
      apply nodup_In.
      exact Hin.
    - exact Hfind.
  }
  assert (Hrhs_subset :
    list_subset
      (standard_pattern_sequence_qbits rhs)
      (standard_pattern_sequence_qbits lhs)).
  {
    apply standard_pattern_rule_safe_qbits.
    exact Hsafe.
  }
  assert (Hreal_rhs :
    forall qbit actual,
      In qbit (standard_pattern_sequence_qbits rhs) ->
      NatMap.find qbit (pattern_qbit_map subst) = Some actual ->
      qbit_apply_swaps swaps qbit = actual).
  {
    intros qbit actual Hin Hfind.
    apply Hreal_lhs.
    - apply Hrhs_subset.
      exact Hin.
    - exact Hfind.
  }
  rewrite (standard_pattern_sequence_instructions_change_swaps
    subst swaps lhs lhs_instrs Hreal_lhs Hlhs).
  rewrite (standard_pattern_sequence_instructions_change_swaps
    subst swaps rhs rhs_instrs Hreal_rhs Hrhs).
  rewrite <- change_qbit_instr_swaps_seq.
  rewrite <- change_qbit_instr_swaps_seq.
  apply change_qbit_instr_swaps_equiv.
  - exact Hswaps_valid.
  - apply standard_pattern_local_transform_sound; assumption.
Qed.

Theorem standard_pattern_rule_of_sequences_sound :
  forall nq name lhs rhs spec,
    standard_pattern_rule_of_sequences nq name lhs rhs = Some spec ->
    TransformSpecValid nq spec.
Proof.
  intros nq name lhs rhs spec H.
  unfold standard_pattern_rule_of_sequences in H.
  unfold standard_pattern_rule_validb in H.
  destruct ((standard_pattern_rule_nqubits lhs rhs <=? nq)
    && standard_pattern_transform_validb lhs rhs) eqn:Hrule_valid;
    try discriminate.
  apply andb_true_iff in Hrule_valid as [Hbound Hvalid].
  apply Nat.leb_le in Hbound.
  inversion H; subst; clear H.
  intros param.
  simpl.
  intros rule Hrule subst lhs' rhs' Hrule_safe Hsubst_distinct Hlhs Hrhs Hinstr.
  simpl in *.
  destruct param; try discriminate; simpl in *.
  inversion Hrule. destruct rule. inversion H0.
  subst. simpl in *.
  rewrite standard_pattern_sequence_inst in Hlhs.
  rewrite standard_pattern_sequence_inst in Hrhs.
  eapply standard_pattern_sequence_instantiated_swap_sound; eauto.
Qed.

End STANDARD_MULTI_PROOFS.

Section STANDARD_MULTI_EXAMPLES.

Example standard_pattern_valid_h_h :
  standard_pattern_transform_validb
    [SPG_Std Std_H 0; SPG_Std Std_H 0]
    [SPG_Std Std_I 0] =
  true.
Proof.
  reflexivity.
Qed.

Example standard_pattern_rule_valid_h_h :
  standard_pattern_rule_validb
    1
    [SPG_Std Std_H 0; SPG_Std Std_H 0]
    [SPG_Std Std_I 0] =
  true.
Proof.
  reflexivity.
Qed.

Example standard_pattern_rule_reject_h_h_too_small :
  standard_pattern_rule_validb
    0
    [SPG_Std Std_H 0; SPG_Std Std_H 0]
    [SPG_Std Std_I 0] =
  false.
Proof.
  reflexivity.
Qed.

Example standard_pattern_valid_x_x :
  standard_pattern_transform_validb
    [SPG_Std Std_X 0; SPG_Std Std_X 0]
    [SPG_Std Std_I 0] =
  true.
Proof.
  reflexivity.
Qed.

Example standard_pattern_valid_swap_to_3cnot :
  standard_pattern_transform_validb
    [SPG_Swap 0 1]
    [SPG_Cnot 0 1; SPG_Cnot 1 0; SPG_Cnot 0 1] =
  true.
Proof.
  reflexivity.
Qed.

Example standard_pattern_reject_cnot_same_operand :
  standard_pattern_transform_validb
    [SPG_Cnot 0 0]
    [SPG_Std Std_I 0] =
  false.
Proof.
  reflexivity.
Qed.

Example standard_pattern_reject_swap_same_operand :
  standard_pattern_transform_validb
    [SPG_Swap 0 0]
    [SPG_Std Std_I 0] =
  false.
Proof.
  reflexivity.
Qed.

Example standard_pattern_reject_non_equivalent :
  standard_pattern_transform_validb
    [SPG_Std Std_X 0]
    [SPG_Std Std_I 0] =
  false.
Proof.
  reflexivity.
Qed.

Example standard_pattern_rule_h_h_sound :
  forall nq spec,
    standard_pattern_rule_of_sequences
      nq
      "H_H"
      [SPG_Std Std_H 0; SPG_Std Std_H 0]
      [SPG_Std Std_I 0] =
    Some spec ->
    TransformSpecValid nq spec.
Proof.
  intros nq spec H.
  eapply (standard_pattern_rule_of_sequences_sound
    nq "H_H"
    [SPG_Std Std_H 0; SPG_Std Std_H 0]
    [SPG_Std Std_I 0]
    spec).
  exact H.
Qed.

Example standard_pattern_rule_swap_to_3cnot_sound :
  forall nq spec,
    standard_pattern_rule_of_sequences
      nq
      "swap_to_3cnot"
      [SPG_Swap 0 1]
      [SPG_Cnot 0 1; SPG_Cnot 1 0; SPG_Cnot 0 1] =
    Some spec ->
    TransformSpecValid nq spec.
Proof.
  intros nq spec H.
  eapply (standard_pattern_rule_of_sequences_sound
    nq "swap_to_3cnot"
    [SPG_Swap 0 1]
    [SPG_Cnot 0 1; SPG_Cnot 1 0; SPG_Cnot 0 1]
    spec).
  exact H.
Qed.

End STANDARD_MULTI_EXAMPLES.
