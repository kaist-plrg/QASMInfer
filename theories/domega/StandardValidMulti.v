Require Import QASMInfer.domega.DOmega.
Require Import QASMInfer.domega.DOmegaMatrix.
Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.All.

From Stdlib Require Import Bool.
From Stdlib Require Import List.
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

Definition domega_half : DOmega :=
  domega_make 1%Z 0%Z 0%Z 0%Z 1.

Definition domega_minus_one : DOmega :=
  domega_neg domega_one.

Definition domega_minus_i : DOmega :=
  domega_neg domega_w2.

Definition domega_h_scalar : DOmega :=
  domega_make 0%Z 1%Z 0%Z (-1)%Z 1.

Definition domega_half_one_plus_i : DOmega :=
  domega_make 1%Z 0%Z 1%Z 0%Z 1.

Definition domega_half_one_minus_i : DOmega :=
  domega_make 1%Z 0%Z (-1)%Z 0%Z 1.

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

Lemma complex_of_standard_pattern_gate_matrix :
  forall n gate matrix,
    standard_pattern_gate_matrix n gate = Some matrix ->
    exists complex_matrix,
      complex_of_domega_matrix matrix = complex_matrix.
Proof.
  intros.
  eexists.
  reflexivity.
Qed.

Lemma complex_of_standard_pattern_sequence_matrix :
  forall n gates matrix,
    standard_pattern_sequence_matrix n gates = Some matrix ->
    exists complex_matrix,
      complex_of_domega_matrix matrix = complex_matrix.
Proof.
  intros.
  eexists.
  reflexivity.
Qed.

Theorem standard_pattern_rule_of_sequences_sound :
  forall nq name lhs rhs spec,
    standard_pattern_rule_of_sequences name lhs rhs = Some spec ->
    TransformSpecValid nq spec.
Proof.
Admitted.

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

End STANDARD_MULTI_EXAMPLES.
