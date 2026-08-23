Require Import QASMInfer.domega.DOmega.
Require Import QASMInfer.domega.DOmegaMatrix.
Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.All.

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

Definition standard_pattern_rewrite_rule
    (lhs rhs : list StandardPatternGate)
    : RewriteRule :=
  {|
    rule_lhs := standard_pattern_sequence_to_instruction_patterns lhs;
    rule_rhs := standard_pattern_sequence_to_instruction_patterns rhs;
  |}.

Definition standard_pattern_rule_of_sequences
    (name : string)
    (lhs rhs : list StandardPatternGate)
    : option TransformSpec :=
  if standard_pattern_transform_validb lhs rhs
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

Fixpoint standard_pattern_sequence_complex_matrices
    (nq : nat)
    (gates : list StandardPatternGate)
    : list (Matrix nq) :=
  match gates with
  | [] =>
      []
  | SPG_Std gate qbit :: rest =>
      mat_single nq qbit (standard_gate_complex_matrix gate)
      :: standard_pattern_sequence_complex_matrices nq rest
  | SPG_Cnot control target :: rest =>
      mat_cnot control target
      :: standard_pattern_sequence_complex_matrices nq rest
  | SPG_Swap qbit1 qbit2 :: rest =>
      mat_swap qbit1 qbit2
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
Admitted.

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
    RewriteRule_safe (standard_pattern_rewrite_rule lhs rhs) ->
    PatternMap_distinct subst ->
    standard_pattern_sequence_instructions subst lhs = Some lhs_instrs ->
    standard_pattern_sequence_instructions subst rhs = Some rhs_instrs ->
    Instruction_list_qbits_valid nq lhs_instrs ->
    Instruction_equiv nq
      (SeqInstr lhs_instrs)
      (SeqInstr rhs_instrs).
Proof.
Admitted.

Theorem standard_pattern_rule_of_sequences_sound :
  forall nq name lhs rhs spec,
    standard_pattern_rule_of_sequences name lhs rhs = Some spec ->
    TransformSpecValid nq spec.
Proof.
  intros.
  unfold standard_pattern_rule_of_sequences in H.
  destruct (standard_pattern_transform_validb lhs rhs) eqn:Hvalid; try discriminate.
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
      "H_H"
      [SPG_Std Std_H 0; SPG_Std Std_H 0]
      [SPG_Std Std_I 0] =
    Some spec ->
    TransformSpecValid nq spec.
Proof.
  intros.
  eapply standard_pattern_rule_of_sequences_sound.
  exact H.
Qed.

Example standard_pattern_rule_swap_to_3cnot_sound :
  forall nq spec,
    standard_pattern_rule_of_sequences
      "swap_to_3cnot"
      [SPG_Swap 0 1]
      [SPG_Cnot 0 1; SPG_Cnot 1 0; SPG_Cnot 0 1] =
    Some spec ->
    TransformSpecValid nq spec.
Proof.
  intros.
  eapply standard_pattern_rule_of_sequences_sound.
  exact H.
Qed.

End STANDARD_MULTI_EXAMPLES.
