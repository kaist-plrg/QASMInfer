Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.All.
Require Import QASMInfer.rewrite.RewriteFunction.
Require Import QASMInfer.rewrite.Spec.
Require Import QASMInfer.rewrite.Validity.

From Stdlib Require Import String.
From Stdlib Require Import List.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Import List.ListNotations.
Open Scope list_scope.

Section TRANSFORM_FUNCTIONS.

Variable nq: nat.

Definition Pat_I (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate A0 A0 A0 qbit_pattern.

Definition Rule_Insert_I (qbit: nat) : RewriteRule :=
  {|
    rule_lhs := [];
    rule_rhs := [Pat_I (NatExact qbit)]
  |}.

Definition Rule_Insert_Swap (qbit1 qbit2: nat) : RewriteRule :=
  {|
    rule_lhs := [];
    rule_rhs := [PSwap (NatExact qbit1) (NatExact qbit2)]
  |}.

Definition Rule_Insert_Cnot_Cnot (qbit1 qbit2: nat) : RewriteRule :=
  {|
    rule_lhs := [];
    rule_rhs :=
      [PCnot (NatExact qbit1) (NatExact qbit2);
       PCnot (NatExact qbit1) (NatExact qbit2)]
  |}.

Definition Rule_Swap_To_3Cnot : RewriteRule :=
  {|
    rule_lhs := [PSwap (NatVar 0) (NatVar 1)];
    rule_rhs :=
      [PCnot (NatVar 0) (NatVar 1);
       PCnot (NatVar 1) (NatVar 0);
       PCnot (NatVar 0) (NatVar 1)]
  |}.

Definition Rule_Double_If (cond : bool) : RewriteRule :=
  {|
    rule_lhs :=
      [PIf (NatVar 0) cond
        [PInstrVar 0]];
    rule_rhs :=
      [PIf (NatVar 0) cond
        [PIf (NatVar 0) cond
          [PInstrVar 0]]]
  |}.

Definition Rule_Double_If_True : RewriteRule :=
  Rule_Double_If true.

Definition Rule_Double_If_False : RewriteRule :=
  Rule_Double_If false.

Definition Rule_Insert_Contradictory_If
    (outer_cond : bool)
    (cbit : nat)
    (instr : Instruction)
    : RewriteRule :=
  {|
    rule_lhs := [];
    rule_rhs :=
      [PIf (NatExact cbit) outer_cond
        [PIf (NatExact cbit) (negb outer_cond)
          [PInstrExact instr]]]
  |}.

Definition Rule_Double_Reset : RewriteRule :=
  {|
    rule_lhs := [PReset (NatVar 0)];
    rule_rhs := [
      PReset (NatVar 0);
      PReset (NatVar 0)
    ]
  |}.

Definition Transform_simple_rule (rule: RewriteRule) : TransformParameter -> option RewriteRule :=
  fun param =>
    match param with
    | Param_None => Some rule
    | _ => None
    end.

Definition TransformSpec_simple_rule (name: string) (rule: RewriteRule) : TransformSpec :=
  {|
    transform_name := name;
    transform_rule := Transform_simple_rule rule;
    transform_postprocess := fun _ instr => instr;
    transform_strategy := TransformDeep;
    transform_param_kind := ParamKind_None;
  |}.

Definition TransformSpec_Insert_I : TransformSpec :=
  {|
    transform_name := "Insert_I";
    transform_rule := fun param =>
      match param with
      | Param_qbit1 qbit =>
          if (qbit <? nq)
          then Some (Rule_Insert_I qbit)
          else None
      | _ => None
      end;
    transform_postprocess := fun _ instr => instr;
    transform_strategy := TransformDeep;
    transform_param_kind := ParamKind_qbit1;
  |}.

Definition TransformSpec_Insert_Swap : TransformSpec :=
  {|
    transform_name := "Insert_Swap";
    transform_rule := fun param =>
      match param with
      | Param_qbit2 qbit1 qbit2 =>
          if (qbit1 <? nq) && (qbit2 <? nq)
          then Some (Rule_Insert_Swap qbit1 qbit2)
          else None
      | _ => None
      end;
    transform_postprocess := fun param instr =>
      match param with
      | Param_qbit2 qbit1 qbit2 =>
          swap_qbit_instr qbit1 qbit2 instr
      | _ =>
          instr
      end;
    transform_strategy := TransformTopLevel;
    transform_param_kind := ParamKind_qbit2;
  |}.

Definition TransformSpec_Insert_Cnot_Cnot : TransformSpec :=
  {|
    transform_name := "Insert_Cnot_Cnot";
    transform_rule := fun param =>
      match param with
      | Param_qbit2 qbit1 qbit2 =>
          if (qbit1 <? nq) && (qbit2 <? nq)
          then Some (Rule_Insert_Cnot_Cnot qbit1 qbit2)
          else None
      | _ => None
      end;
    transform_postprocess := fun _ instr => instr;
    transform_strategy := TransformDeep;
    transform_param_kind := ParamKind_qbit2;
  |}.

Definition TransformSpec_Swap_To_3Cnot : TransformSpec :=
  TransformSpec_simple_rule "Swap_To_3Cnot" Rule_Swap_To_3Cnot.

Definition TransformSpec_Insert_Contradictory_If
    (name : string)
    (outer_cond : bool)
    : TransformSpec :=
  {|
    transform_name := name;
    transform_rule := fun param =>
      match param with
      | Param_cbit_instr cbit instr =>
          if Instruction_qbits_validb nq instr
          then Some (Rule_Insert_Contradictory_If outer_cond cbit instr)
          else None
      | _ => None
      end;
    transform_postprocess := fun _ instr => instr;
    transform_strategy := TransformDeep;
    transform_param_kind := ParamKind_cbit_instr;
  |}.

Definition TransformSpec_Insert_Contradictory_If_False : TransformSpec :=
  TransformSpec_Insert_Contradictory_If "Insert_If_FT" false.

Definition TransformSpec_Insert_Contradictory_If_True : TransformSpec :=
  TransformSpec_Insert_Contradictory_If "Insert_If_TF" true.

Definition Transform_spec_list : list TransformSpec :=
  [
    TransformSpec_Insert_I;
    TransformSpec_Insert_Swap;
    TransformSpec_Insert_Cnot_Cnot;
    TransformSpec_Swap_To_3Cnot;
    TransformSpec_Insert_Contradictory_If_False;
    TransformSpec_Insert_Contradictory_If_True;
    TransformSpec_simple_rule "Double_If_True" Rule_Double_If_True;
    TransformSpec_simple_rule "Double_If_False" Rule_Double_If_False;
    TransformSpec_simple_rule "Double_Reset" Rule_Double_Reset
  ].

Lemma TransformSpec_Insert_I_valid :
  TransformSpecValid nq TransformSpec_Insert_I.
Proof.
  unfold TransformSpecValid, TransformSpec_Insert_I.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  destruct (qbit <? nq) eqn:Hqbit; simpl.
  - intros rule Hrule subst lhs rhs _ _ Hlhs Hrhs _.
    cbn [transform_rule] in Hrule.
    rewrite Hqbit in Hrule.
    injection Hrule as <-.
    apply Nat.ltb_lt in Hqbit.
    simpl in Hlhs, Hrhs.
    injection Hlhs as <-.
    injection Hrhs as <-.
    symmetry.
    apply Transform_I.
    assumption.
  - intros rule Hrule.
    cbn [transform_rule] in Hrule.
    rewrite Hqbit in Hrule.
    discriminate.
Qed.

Lemma TransformSpec_Insert_Swap_valid :
  TransformSpecValid nq TransformSpec_Insert_Swap.
Proof.
  unfold TransformSpecValid, TransformSpec_Insert_Swap.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  destruct ((qbit1 <? nq) && (qbit2 <? nq)) eqn:Hqbits; simpl.
  - intros rule Hrule subst lhs rhs suffix _ _ Hlhs Hrhs Hvalid.
    cbn [transform_rule] in Hrule.
    rewrite Hqbits in Hrule.
    injection Hrule as <-.
    apply andb_true_iff in Hqbits as [Hqbit1 Hqbit2].
    apply Nat.ltb_lt in Hqbit1.
    apply Nat.ltb_lt in Hqbit2.
    simpl in Hlhs, Hrhs.
    injection Hlhs as <-.
    injection Hrhs as <-.
    simpl.
    symmetry.
    apply Transform_swap_insert with (instr := SeqInstr suffix).
    all: assumption.
  - intros rule Hrule.
    cbn [transform_rule] in Hrule.
    rewrite Hqbits in Hrule.
    discriminate.
Qed.

Lemma TransformSpec_Insert_Cnot_Cnot_valid :
  TransformSpecValid nq TransformSpec_Insert_Cnot_Cnot.
Proof.
  unfold
    TransformSpecValid,
    TransformSpec_Insert_Cnot_Cnot.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  destruct ((qbit1 <? nq) && (qbit2 <? nq)) eqn:Hqbits; simpl.
  - intros rule Hrule map lhs rhs _ _ Hlhs Hrhs _.
    cbn [transform_rule] in Hrule.
    rewrite Hqbits in Hrule.
    injection Hrule as <-.
    apply andb_true_iff in Hqbits as [Hqbit1 Hqbit2].
    apply Nat.ltb_lt in Hqbit1.
    apply Nat.ltb_lt in Hqbit2.
    simpl in Hlhs, Hrhs.
    inversion Hlhs; subst; clear Hlhs.
    inversion Hrhs; subst; clear Hrhs.
    symmetry.
    transitivity qasm{ I qbit1 }.
    + transitivity qasm{ cx qbit1 qbit2; cx qbit1 qbit2 }.
      * rewrite Instruction_equiv_Seq_list_eq. reflexivity.
      * apply Transform_cnot_cnot; assumption.
    + transitivity NopInstr.
      * apply Transform_I.
        assumption.
      * intros ps Hps. reflexivity.
  - intros rule Hrule.
    cbn [transform_rule] in Hrule.
    rewrite Hqbits in Hrule.
    discriminate.
Qed.

Lemma TransformSpec_Swap_To_3Cnot_valid :
  TransformSpecValid nq TransformSpec_Swap_To_3Cnot.
Proof.
  unfold
    TransformSpecValid,
    TransformSpec_Swap_To_3Cnot,
    TransformSpec_simple_rule,
    Transform_simple_rule.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  intros rule Hrule map lhs rhs _ _ Hlhs Hrhs Hvalid.
  injection Hrule as <-.
  simpl in Hlhs, Hrhs.
  destruct (NatMap.find 0%nat (pattern_qbit_map map)) as [qbit1 |];
  try discriminate.
  destruct (NatMap.find 1%nat (pattern_qbit_map map)) as [qbit2 |];
  try discriminate.
  inversion Hlhs; subst; clear Hlhs.
  inversion Hrhs; subst; clear Hrhs.
  inversion Hvalid as [| ? ? Hswap_valid Hnil_valid]; subst.
  inversion Hswap_valid; subst.
  symmetry.
  transitivity qasm{ cx qbit1 qbit2; cx qbit2 qbit1; cx qbit1 qbit2 }.
  - repeat rewrite Instruction_equiv_Seq_list_eq. reflexivity.
  - transitivity qasm{ swap qbit1 qbit2 }.
    + apply Transform_3cnot_swap; assumption.
    + symmetry.
      apply Instruction_equiv_Seq_singleton.
Qed.

Lemma TransformSpec_Insert_Contradictory_If_valid :
  forall name outer_cond,
  TransformSpecValid nq
    (TransformSpec_Insert_Contradictory_If name outer_cond).
Proof.
  intros name outer_cond.
  unfold TransformSpecValid, TransformSpec_Insert_Contradictory_If.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  destruct (Instruction_qbits_validb nq instr) eqn:Hinstr; simpl.
  - intros rule Hrule map lhs rhs _ _ Hlhs Hrhs _.
    cbn [transform_rule] in Hrule.
    rewrite Hinstr in Hrule.
    injection Hrule as <-.
    simpl in Hlhs, Hrhs.
    injection Hlhs as <-.
    injection Hrhs as <-.
    symmetry.
    rewrite Instruction_equiv_Seq_singleton.
    destruct outer_cond; simpl.
    + apply Transform_if_nop_tf.
    + apply Transform_if_nop_ft.
  - intros rule Hrule.
    cbn [transform_rule] in Hrule.
    rewrite Hinstr in Hrule.
    discriminate.
Qed.

Lemma TransformSpec_Insert_Contradictory_If_False_valid :
  TransformSpecValid nq TransformSpec_Insert_Contradictory_If_False.
Proof.
  apply TransformSpec_Insert_Contradictory_If_valid.
Qed.

Lemma TransformSpec_Insert_Contradictory_If_True_valid :
  TransformSpecValid nq TransformSpec_Insert_Contradictory_If_True.
Proof.
  apply TransformSpec_Insert_Contradictory_If_valid.
Qed.

Lemma TransformSpec_Double_If_valid :
  forall name cond,
  TransformSpecValid nq
    (TransformSpec_simple_rule name (Rule_Double_If cond)).
Proof.
  intros name cond.
  unfold TransformSpecValid, TransformSpec_simple_rule, Transform_simple_rule.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  intros rule Hrule subst lhs rhs _ _ Hlhs Hrhs _.
  injection Hrule as <-.
  unfold Rule_Double_If in Hlhs, Hrhs.
  simpl in Hlhs, Hrhs.
  destruct (NatMap.find 0%nat (pattern_cbit_map subst)) as [cbit |];
  try discriminate.
  destruct (NatMap.find 0%nat (pattern_instr_map subst)) as [instr |];
  try discriminate.
  injection Hlhs as <-.
  injection Hrhs as <-.
  repeat rewrite Instruction_equiv_Seq_singleton.
  symmetry.
  apply Transform_double_if.
Qed.

Lemma TransformSpec_Double_If_True_valid :
  TransformSpecValid nq
    (TransformSpec_simple_rule "Double_If_True" Rule_Double_If_True).
Proof.
  apply TransformSpec_Double_If_valid.
Qed.

Lemma TransformSpec_Double_If_False_valid :
  TransformSpecValid nq
    (TransformSpec_simple_rule "Double_If_False" Rule_Double_If_False).
Proof.
  apply TransformSpec_Double_If_valid.
Qed.

Lemma TransformSpec_Double_Reset_valid :
  TransformSpecValid nq
    (TransformSpec_simple_rule "Double_Reset" Rule_Double_Reset).
Proof.
  unfold TransformSpecValid, TransformSpec_simple_rule, Transform_simple_rule.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2 | cbit instr]; simpl.
  all: try (intros rule Hrule; discriminate).
  intros rule Hrule subst lhs rhs _ _ Hlhs Hrhs Hvalid.
  injection Hrule as <-.
  unfold Rule_Double_Reset in Hlhs, Hrhs.
  simpl in Hlhs, Hrhs.
  destruct (NatMap.find 0%nat (pattern_qbit_map subst)) as [qbit |];
  try discriminate.
  injection Hlhs as <-.
  injection Hrhs as <-.
  repeat rewrite Instruction_equiv_Seq_singleton.
  symmetry.
  apply Transform_double_reset.
  inversion Hvalid; subst. inversion H1; subst.
  assumption.
Qed.

Theorem Transform_spec_list_valid :
  Forall (TransformSpecValid nq) Transform_spec_list.
Proof.
  repeat constructor.
  - apply TransformSpec_Insert_I_valid.
  - apply TransformSpec_Insert_Swap_valid.
  - apply TransformSpec_Insert_Cnot_Cnot_valid.
  - apply TransformSpec_Swap_To_3Cnot_valid.
  - apply TransformSpec_Insert_Contradictory_If_False_valid.
  - apply TransformSpec_Insert_Contradictory_If_True_valid.
  - apply TransformSpec_Double_If_True_valid.
  - apply TransformSpec_Double_If_False_valid.
  - apply TransformSpec_Double_Reset_valid.
Qed.

End TRANSFORM_FUNCTIONS.
