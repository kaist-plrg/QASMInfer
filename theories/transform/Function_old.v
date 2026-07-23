Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Valid.
Require Import QASMInfer.transform.Commute.
Require Import QASMInfer.transform.Transform.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

From Stdlib Require Import
  FSets.FMapAVL
  Structures.OrderedTypeEx.

Module NatMap := FMapAVL.Make Nat_as_OT.
Module NatMapFacts := WFacts_fun NatMap.E NatMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Import List.ListNotations.

Section FLATTEN_FUNCTION.

Fixpoint flatten_core (instr : Instruction) : Instruction :=
  match instr with
  | SeqInstr instrs =>
      fold_right
        (fun instr acc =>
           qasm_seq (flatten_core instr) acc)
        (SeqInstr [])
        instrs
  | IfInstr c b body =>
      IfInstr c b (flatten_core body)
  | _ =>
      instr
  end.

Lemma Instruction_equiv_flatten:
  forall (nq: nat) (instr: Instruction),
  Instruction_equiv nq
  instr
  (flatten_core instr).
Proof.
  intros nq.
  apply Instruction_ind'; simpl; intros; try reflexivity.
  - induction is; try reflexivity; simpl.
    inversion H; subst.
    rewrite Instruction_equiv_Seq_list_eq.
    transitivity (qasm{ ($(flatten_core a)); seq[ is ]}). {
      apply Instruction_equiv_rewrite_start.
      apply H2.
    }
    apply Instruction_equiv_rewrite_end.
    apply IHis.
    apply H3.
  - apply Instruction_if_Proper.
    apply H.
Qed.

End FLATTEN_FUNCTION.

Section PATTERN.

Definition R_eqb (x y: R): bool :=
  if Req_EM_T x y then true else false.

Definition PatternMap : Type := NatMap.t nat.

Definition PatternMap_empty : PatternMap := NatMap.empty _.

Definition PatternMap_bind (variable value : nat) (map : PatternMap)
    : option PatternMap :=
  match NatMap.find variable map with
  | None =>
      Some (NatMap.add variable value map)
  | Some old_value =>
      if Nat.eqb old_value value
      then Some map
      else None
  end.

Definition PatternMap_extends
    (map1 map2 : PatternMap)
    : Prop :=
  forall variable value,
    NatMap.find variable map1 = Some value ->
    NatMap.find variable map2 = Some value.

Inductive NatPattern: Type :=
  | NatVar: nat -> NatPattern.

Definition NatPattern_match (pattern : NatPattern) (value : nat) (map : PatternMap)
    : option PatternMap :=
  match pattern with
  | NatVar variable =>
      PatternMap_bind variable value map
  end.

Definition NatPattern_inst
    (pattern : NatPattern)
    (subst : PatternMap)
    : option nat :=
  match pattern with
  | NatVar variable =>
      NatMap.find variable subst
  end.

Inductive InstructionPattern: Type :=
  | PNop: InstructionPattern
  | PRotate: R -> R -> R -> NatPattern -> InstructionPattern 
  | PCnot: NatPattern -> NatPattern -> InstructionPattern 
  | PSwap: NatPattern -> NatPattern -> InstructionPattern 
  | PMeasure: NatPattern -> NatPattern -> InstructionPattern 
  | PReset: NatPattern -> InstructionPattern.

Definition InstructionPattern_match
    (pattern : InstructionPattern)
    (instr : Instruction)
    (map : PatternMap)
    : option PatternMap :=
  match pattern, instr with
  | PNop, NopInstr => Some map
  | PRotate theta' phi' lambda' qbit_pattern,
    RotateInstr theta phi lambda qbit =>
      if R_eqb theta theta' then
        if R_eqb phi phi' then
          if R_eqb lambda lambda' then
            NatPattern_match qbit_pattern qbit map
          else
            None
        else
          None
      else
        None
  | PCnot control_pattern target_pattern,
    CnotInstr control target =>
      match NatPattern_match control_pattern control map with
      | Some map' =>
          NatPattern_match target_pattern target map'
      | None =>
          None
      end
  | PSwap qbit1_pattern qbit2_pattern,
    SwapInstr qbit1 qbit2 =>
      match NatPattern_match qbit1_pattern qbit1 map with
      | Some map' =>
          NatPattern_match qbit2_pattern qbit2 map'
      | None =>
          None
      end
  | PMeasure qbit_pattern cbit_pattern,
    MeasureInstr qbit cbit =>
      match NatPattern_match qbit_pattern qbit map with
      | Some map' =>
          NatPattern_match cbit_pattern cbit map'
      | None =>
          None
      end
  | PReset qbit_pattern,
    ResetInstr qbit =>
      NatPattern_match qbit_pattern qbit map
  | _, _ =>
      None
  end.

Fixpoint InstructionPattern_match_list
    (patterns : list InstructionPattern)
    (instrs : list Instruction)
    (map : PatternMap)
    : option PatternMap :=
  match patterns, instrs with
  | [], _ => Some map
  | _, [] => None
  | pattern :: pattern_rest, instr :: instr_rest =>
    match InstructionPattern_match pattern instr map with
    | Some map' =>
      InstructionPattern_match_list pattern_rest instr_rest map'
    | None => None
    end
  end.

Definition InstructionPattern_inst
    (pattern : InstructionPattern)
    (map : PatternMap)
    : option Instruction :=
  match pattern with
  | PNop => Some NopInstr
  | PRotate theta phi lambda qbit_pattern =>
      match NatPattern_inst qbit_pattern map with
      | Some qbit =>
          Some (RotateInstr theta phi lambda qbit)
      | None =>
          None
      end
  | PCnot control_pattern target_pattern =>
      match NatPattern_inst control_pattern map,
            NatPattern_inst target_pattern map with
      | Some control, Some target =>
          Some (CnotInstr control target)
      | _, _ => None
      end
  | PSwap qbit1_pattern qbit2_pattern =>
      match NatPattern_inst qbit1_pattern map,
            NatPattern_inst qbit2_pattern map with
      | Some qbit1, Some qbit2 =>
          Some (SwapInstr qbit1 qbit2)
      | _, _ => None
      end
  | PMeasure qbit_pattern cbit_pattern =>
      match NatPattern_inst qbit_pattern map,
            NatPattern_inst cbit_pattern map with
      | Some qbit, Some cbit =>
          Some (MeasureInstr qbit cbit)
      | _, _ => None
      end
  | PReset qbit_pattern =>
      match NatPattern_inst qbit_pattern map with
      | Some qbit =>
          Some (ResetInstr qbit)
      | None =>
          None
      end
  end.

Fixpoint InstructionPattern_inst_list
    (patterns : list InstructionPattern)
    (map: PatternMap)
    {struct patterns}
    : option (list Instruction) :=
  match patterns with
  | [] => Some []
  | pattern :: pattern_rest =>
      match InstructionPattern_inst pattern map,
            InstructionPattern_inst_list pattern_rest map with
      | Some instr, Some instrs =>
        Some (instr :: instrs)
      | _, _ => None
      end
  end.

Record RewriteRule : Type := {
  rule_lhs : list InstructionPattern;
  rule_rhs : list InstructionPattern
}.

Record RewriteResult : Type := {
  RewriteResult_consumed : nat;
  RewriteResult_replacement : list Instruction
}.

(* Apply rule at the first place *)
Definition RewriteRule_apply
    (rule : RewriteRule)
    (instrs : list Instruction)
    : option RewriteResult :=
  match InstructionPattern_match_list (rule_lhs rule) instrs PatternMap_empty with
  | Some subst =>
    match InstructionPattern_inst_list (rule_rhs rule) subst with
    | Some replacement =>
        Some {|
          RewriteResult_consumed := length (rule_lhs rule);
          RewriteResult_replacement := replacement
        |}
    | None => None
    end
  | None => None
  end.

Fixpoint RewriteRule_apply_nth_list
    (rule : RewriteRule)
    (instrs : list Instruction)
    (occurrence : nat)
    : list Instruction :=
  match RewriteRule_apply rule instrs with
  | Some result =>
      match occurrence with
      | O =>
        RewriteResult_replacement result
        ++ skipn (RewriteResult_consumed result) instrs
      | S occurrence' =>
        match instrs with
        | current :: rest =>
            current :: RewriteRule_apply_nth_list rule rest occurrence'
        | [] => []
        end
      end
  | None =>
    match instrs with
    | current :: rest =>
        current :: RewriteRule_apply_nth_list rule rest occurrence
    | [] => []
    end
  end.

Definition Instruction_list_simp
    (instrs : list Instruction)
    : Instruction :=
  match instrs with
  | [] =>
      NopInstr
  | [instr] =>
      instr
  | _ =>
      SeqInstr instrs
  end.

Fixpoint RewriteRule_apply_nth
    (rule : RewriteRule)
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  match instr with
  | SeqInstr instrs =>
      SeqInstr
        (RewriteRule_apply_nth_list rule instrs occurrence)
  | IfInstr cbit expected body =>
      IfInstr
        cbit
        expected
        (RewriteRule_apply_nth rule body occurrence)
  | _ =>
      Instruction_list_simp
        (RewriteRule_apply_nth_list rule [instr] occurrence)
  end.

Definition Pat_I
    (qbit_pattern : NatPattern)
    : InstructionPattern :=
  PRotate 0 0 0 qbit_pattern.

Definition Pat_X
    (qbit_pattern : NatPattern)
    : InstructionPattern :=
  PRotate PI 0 PI qbit_pattern.

Definition Pat_Y
    (qbit_pattern : NatPattern)
    : InstructionPattern :=
  PRotate PI PI2 PI2 qbit_pattern.

Variable nq: nat.

Inductive Instruction_qbits_valid : Instruction -> Prop :=
  | IQV_Nop :
    Instruction_qbits_valid NopInstr
  | IQV_Rotate :
    forall theta phi lambda qbit,
      Qbit_index_valid nq qbit ->
      Instruction_qbits_valid
        (RotateInstr theta phi lambda qbit)
  | IQV_Cnot :
    forall control target,
      Qbit_index_valid nq control ->
      Qbit_index_valid nq target ->
      Instruction_qbits_valid
        (CnotInstr control target)
  | IQV_Swap :
    forall qbit1 qbit2,
      Qbit_index_valid nq qbit1 ->
      Qbit_index_valid nq qbit2 ->
      Instruction_qbits_valid
        (SwapInstr qbit1 qbit2)
  | IQV_Measure :
    forall qbit cbit,
      Qbit_index_valid nq qbit ->
      Instruction_qbits_valid
        (MeasureInstr qbit cbit)
  | IQV_Seq :
    forall instrs,
      Instruction_list_qbits_valid instrs ->
      Instruction_qbits_valid
        (SeqInstr instrs)
  | IQV_If :
    forall cbit expected body,
      Instruction_qbits_valid body ->
      Instruction_qbits_valid
        (IfInstr cbit expected body)
  | IQV_Reset :
    forall qbit,
      Qbit_index_valid nq qbit ->
      Instruction_qbits_valid
        (ResetInstr qbit)

with Instruction_list_qbits_valid
    : list Instruction -> Prop :=
  | IQVL_nil :
    Instruction_list_qbits_valid []
  | IQVL_cons :
    forall instr instrs,
      Instruction_qbits_valid instr ->
      Instruction_list_qbits_valid instrs ->
      Instruction_list_qbits_valid
        (instr :: instrs).

Definition PatternRuleValid
    (rule : RewriteRule)
    : Prop :=
  forall map lhs rhs,
    InstructionPattern_inst_list
      (rule_lhs rule)
      map
    = Some lhs ->
    InstructionPattern_inst_list
      (rule_rhs rule)
      map
    = Some rhs ->
    Instruction_list_qbits_valid lhs ->
    Instruction_equiv nq
      (SeqInstr lhs)
      (SeqInstr rhs).

Definition RewriteRuleValid
    (rule : RewriteRule)
    : Prop :=
  forall instrs result,
    Instruction_list_qbits_valid instrs ->
    RewriteRule_apply rule instrs = Some result ->
    Instruction_equiv nq
      (SeqInstr instrs)
      (SeqInstr (RewriteResult_replacement result
       ++ skipn (RewriteResult_consumed result) instrs)).


(* ================================================================ *)
(* Proof                                                            *)
(* ================================================================ *)
Lemma R_eqb_eq :
  forall x y,
    R_eqb x y = true ->
    x = y.
Proof.
  intros x y Heq.
  unfold R_eqb in Heq.
  destruct (Req_EM_T x y) as [Hxy | Hxy].
  - exact Hxy.
  - discriminate.
Qed.

Lemma PatternMap_extends_refl :
  forall map,
    PatternMap_extends map map.
Proof.
  unfold PatternMap_extends.
  auto.
Qed.

Lemma PatternMap_extends_trans :
  forall map1 map2 map3,
    PatternMap_extends map1 map2 ->
    PatternMap_extends map2 map3 ->
    PatternMap_extends map1 map3.
Proof.
  unfold PatternMap_extends.
  intros map1 map2 map3 H12 H23 variable value Hfind.
  apply H23.
  apply H12.
  exact Hfind.
Qed.

Lemma PatternMap_bind_extends :
  forall variable value map map',
    PatternMap_bind variable value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros variable value map map' Hbind.
  unfold PatternMap_bind in Hbind.
  destruct
    (NatMap.find variable map)
    as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq.
    + inversion Hbind.
      subst map'.
      apply PatternMap_extends_refl.
    + discriminate.
  - inversion Hbind.
    subst map'.
    unfold PatternMap_extends.
    intros key old Hkey.
    destruct (Nat.eq_dec key variable) as [Heq | Hneq].
    + subst key.
      rewrite Hfind in Hkey.
      discriminate.
    + rewrite NatMapFacts.add_neq_o.
      * exact Hkey.
      * lia.
Qed.

Lemma PatternMap_bind_find :
  forall variable value map map',
    PatternMap_bind variable value map = Some map' ->
    NatMap.find variable map' = Some value.
Proof.
  intros variable value map map' Hbind.
  unfold PatternMap_bind in Hbind.
  destruct
    (NatMap.find variable map)
    as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      subst old_value.
      inversion Hbind.
      subst map'.
      exact Hfind.
    + discriminate.
  - inversion Hbind.
    subst map'.
    apply NatMapFacts.add_eq_o.
    reflexivity.
Qed.

Lemma NatPattern_match_extends :
  forall pattern value map map',
    NatPattern_match pattern value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern as [variable].
  simpl in Hmatch.
  eapply PatternMap_bind_extends.
  exact Hmatch.
Qed.

Lemma NatPattern_match_sound :
  forall pattern value map map',
    NatPattern_match pattern value map = Some map' ->
    NatPattern_inst pattern map' = Some value.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern as [variable].
  simpl in *.
  apply PatternMap_bind_find in Hmatch.
  exact Hmatch.
Qed.

Lemma NatPattern_inst_extends :
  forall pattern map1 map2 value,
    PatternMap_extends map1 map2 ->
    NatPattern_inst pattern map1 = Some value ->
    NatPattern_inst pattern map2 = Some value.
Proof.
  intros pattern map1 map2 value Hextends Hinst.
  destruct pattern as [variable].
  simpl in *.
  apply Hextends with (variable := variable).
  exact Hinst.
Qed.

Lemma InstructionPattern_inst_extends :
  forall pattern map1 map2 instr,
    PatternMap_extends map1 map2 ->
    InstructionPattern_inst pattern map1 = Some instr ->
    InstructionPattern_inst pattern map2 = Some instr.
Proof.
  intros pattern map1 map2 instr Hextends Hinst.
  destruct pattern; simpl in *.
  - inversion Hinst.
    reflexivity.
  - destruct (NatPattern_inst n map1)
      as [qbit |] eqn:Hqbit;
      try discriminate.
    inversion Hinst.
    subst instr.
    pose proof
      (NatPattern_inst_extends
         n map1 map2 qbit
         Hextends Hqbit)
      as Hqbit'.
    rewrite Hqbit'.
    reflexivity.
  - destruct (NatPattern_inst n map1)
      as [control |] eqn:Hcontrol;
      try discriminate.
    destruct (NatPattern_inst n0 map1)
      as [target |] eqn:Htarget;
      try discriminate.
    inversion Hinst.
    subst instr.
    pose proof
      (NatPattern_inst_extends
         n map1 map2 control
         Hextends Hcontrol)
      as Hcontrol'.
    pose proof
      (NatPattern_inst_extends
         n0 map1 map2 target
         Hextends Htarget)
      as Htarget'.
    rewrite Hcontrol', Htarget'.
    reflexivity.
  - destruct (NatPattern_inst n map1)
      as [qbit1 |] eqn:Hqbit1;
      try discriminate.
    destruct (NatPattern_inst n0 map1)
      as [qbit2 |] eqn:Hqbit2;
      try discriminate.
    inversion Hinst.
    subst instr.
    rewrite
      (NatPattern_inst_extends
         n map1 map2 qbit1
         Hextends Hqbit1).
    rewrite
      (NatPattern_inst_extends
         n0 map1 map2 qbit2
         Hextends Hqbit2).
    reflexivity.
  - destruct (NatPattern_inst n map1)
      as [qbit |] eqn:Hqbit;
      try discriminate.
    destruct (NatPattern_inst n0 map1)
      as [cbit |] eqn:Hcbit;
      try discriminate.
    inversion Hinst.
    subst instr.
    rewrite
      (NatPattern_inst_extends
         n map1 map2 qbit
         Hextends Hqbit).
    rewrite
      (NatPattern_inst_extends
         n0 map1 map2 cbit
         Hextends Hcbit).
    reflexivity.
  - destruct (NatPattern_inst n map1)
      as [qbit |] eqn:Hqbit;
      try discriminate.
    inversion Hinst.
    subst instr.
    rewrite
      (NatPattern_inst_extends
         n map1 map2 qbit
         Hextends Hqbit).
    reflexivity.
Qed.

Lemma InstructionPattern_match_extends :
  forall pattern instr map map',
    InstructionPattern_match pattern instr map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros pattern instr map map' Hmatch.
  destruct pattern as
    [ (* PNop *)
    | expected_theta expected_phi expected_lambda qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern ].
  - destruct instr;
      simpl in Hmatch;
      try discriminate.
    inversion Hmatch.
    subst map'.
    apply PatternMap_extends_refl.
  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.
    destruct (R_eqb theta expected_theta)
      eqn:Htheta;
      try discriminate.
    destruct (R_eqb phi expected_phi)
      eqn:Hphi;
      try discriminate.
    destruct (R_eqb lambda expected_lambda)
      eqn:Hlambda;
      try discriminate.
    eapply NatPattern_match_extends.
    exact Hmatch.
  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct
      (NatPattern_match
         control_pattern control map)
      as [map1 |] eqn:Hcontrol;
      try discriminate.

    pose proof
      (NatPattern_match_extends
         control_pattern
         control
         map
         map1
         Hcontrol)
      as H01.

    pose proof
      (NatPattern_match_extends
         target_pattern
         target
         map1
         map'
         Hmatch)
      as H12.

    eapply PatternMap_extends_trans.
    + exact H01.
    + exact H12.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct
      (NatPattern_match
         qbit1_pattern qbit1 map)
      as [map1 |] eqn:Hqbit1;
      try discriminate.

    pose proof
      (NatPattern_match_extends
         qbit1_pattern
         qbit1
         map
         map1
         Hqbit1)
      as H01.

    pose proof
      (NatPattern_match_extends
         qbit2_pattern
         qbit2
         map1
         map'
         Hmatch)
      as H12.

    eapply PatternMap_extends_trans.
    + exact H01.
    + exact H12.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct
      (NatPattern_match
         qbit_pattern qbit map)
      as [map1 |] eqn:Hqbit;
      try discriminate.

    pose proof
      (NatPattern_match_extends
         qbit_pattern
         qbit
         map
         map1
         Hqbit)
      as H01.

    pose proof
      (NatPattern_match_extends
         cbit_pattern
         cbit
         map1
         map'
         Hmatch)
      as H12.

    eapply PatternMap_extends_trans.
    + exact H01.
    + exact H12.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    eapply NatPattern_match_extends.
    exact Hmatch.
Qed.

Lemma InstructionPattern_match_sound :
  forall pattern instr map map',
    InstructionPattern_match pattern instr map = Some map' ->
    InstructionPattern_inst pattern map' = Some instr.
Proof.
  intros pattern instr map map' Hmatch.

  destruct pattern as
    [ (* PNop *)
    | expected_theta expected_phi expected_lambda qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern ].

  - destruct instr;
      simpl in Hmatch;
      try discriminate.

    inversion Hmatch.
    reflexivity.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct (R_eqb theta expected_theta)
      eqn:Htheta;
      try discriminate.

    destruct (R_eqb phi expected_phi)
      eqn:Hphi;
      try discriminate.

    destruct (R_eqb lambda expected_lambda)
      eqn:Hlambda;
      try discriminate.

    apply R_eqb_eq in Htheta.
    apply R_eqb_eq in Hphi.
    apply R_eqb_eq in Hlambda.

    subst expected_theta.
    subst expected_phi.
    subst expected_lambda.

    pose proof
      (NatPattern_match_sound
         qbit_pattern
         qbit
         map
         map'
         Hmatch)
      as Hqbit.

    simpl.
    rewrite Hqbit.
    reflexivity.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct
      (NatPattern_match
         control_pattern control map)
      as [map1 |] eqn:Hcontrol_match;
      try discriminate.

    pose proof
      (NatPattern_match_sound
         control_pattern
         control
         map
         map1
         Hcontrol_match)
      as Hcontrol_inst_map1.

    pose proof
      (NatPattern_match_extends
         target_pattern
         target
         map1
         map'
         Hmatch)
      as Hextends.

    pose proof
      (NatPattern_inst_extends
         control_pattern
         map1
         map'
         control
         Hextends
         Hcontrol_inst_map1)
      as Hcontrol_inst.

    pose proof
      (NatPattern_match_sound
         target_pattern
         target
         map1
         map'
         Hmatch)
      as Htarget_inst.

    simpl.
    rewrite Hcontrol_inst.
    rewrite Htarget_inst.
    reflexivity.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct
      (NatPattern_match
         qbit1_pattern qbit1 map)
      as [map1 |] eqn:Hqbit1_match;
      try discriminate.

    pose proof
      (NatPattern_match_sound
         qbit1_pattern
         qbit1
         map
         map1
         Hqbit1_match)
      as Hqbit1_inst_map1.

    pose proof
      (NatPattern_match_extends
         qbit2_pattern
         qbit2
         map1
         map'
         Hmatch)
      as Hextends.

    pose proof
      (NatPattern_inst_extends
         qbit1_pattern
         map1
         map'
         qbit1
         Hextends
         Hqbit1_inst_map1)
      as Hqbit1_inst.

    pose proof
      (NatPattern_match_sound
         qbit2_pattern
         qbit2
         map1
         map'
         Hmatch)
      as Hqbit2_inst.

    simpl.
    rewrite Hqbit1_inst.
    rewrite Hqbit2_inst.
    reflexivity.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    destruct
      (NatPattern_match
         qbit_pattern qbit map)
      as [map1 |] eqn:Hqbit_match;
      try discriminate.

    pose proof
      (NatPattern_match_sound
         qbit_pattern
         qbit
         map
         map1
         Hqbit_match)
      as Hqbit_inst_map1.

    pose proof
      (NatPattern_match_extends
         cbit_pattern
         cbit
         map1
         map'
         Hmatch)
      as Hextends.

    pose proof
      (NatPattern_inst_extends
         qbit_pattern
         map1
         map'
         qbit
         Hextends
         Hqbit_inst_map1)
      as Hqbit_inst.

    pose proof
      (NatPattern_match_sound
         cbit_pattern
         cbit
         map1
         map'
         Hmatch)
      as Hcbit_inst.

    simpl.
    rewrite Hqbit_inst.
    rewrite Hcbit_inst.
    reflexivity.

  - destruct instr as
      [ | theta phi lambda qbit
        | control target
        | qbit1 qbit2
        | qbit cbit
        | instrs
        | cbit expected body
        | qbit ];
      simpl in Hmatch;
      try discriminate.

    pose proof
      (NatPattern_match_sound
         qbit_pattern
         qbit
         map
         map'
         Hmatch)
      as Hqbit_inst.

    simpl.
    rewrite Hqbit_inst.
    reflexivity.
Qed.

Lemma InstructionPattern_match_list_extends :
  forall patterns instrs map map',
    InstructionPattern_match_list
      patterns instrs map = Some map' ->
    PatternMap_extends map map'.
Proof.
  induction patterns as
    [| pattern patterns IH].

  - intros instrs map map' Hmatch.

    simpl in Hmatch.
    inversion Hmatch.
    subst map'.

    apply PatternMap_extends_refl.

  - intros instrs map map' Hmatch.

    destruct instrs as [| instr instrs].
    + simpl in Hmatch.
      discriminate.

    + simpl in Hmatch.

      destruct
        (InstructionPattern_match
           pattern instr map)
        as [map1 |] eqn:Hhead;
        try discriminate.

      pose proof
        (InstructionPattern_match_extends
           pattern
           instr
           map
           map1
           Hhead)
        as H01.

      pose proof
        (IH instrs map1 map' Hmatch)
        as H12.

      eapply PatternMap_extends_trans.
      * exact H01.
      * exact H12.
Qed.

Lemma InstructionPattern_match_list_decompose :
  forall patterns instrs map map',
    InstructionPattern_match_list
      patterns instrs map = Some map' ->
    exists matched suffix,
      instrs = matched ++ suffix
      /\
      InstructionPattern_inst_list
        patterns map' = Some matched
      /\
      length matched = length patterns.
Proof.
  induction patterns as [| pattern patterns IH].
  - intros instrs map map' Hmatch.
    simpl in Hmatch.
    inversion Hmatch.
    subst map'.

    exists [], instrs.
    repeat split; reflexivity.

  - intros instrs map map' Hmatch.

    destruct instrs as [| instr instrs].
    + simpl in Hmatch.
      discriminate.

    + simpl in Hmatch.

      destruct
        (InstructionPattern_match pattern instr map)
        as [map1 |] eqn:Hhead.
      2: discriminate.

      destruct
        (IH instrs map1 map' Hmatch)
        as
          (matched & suffix
           & Hinstrs
           & Htail_inst
           & Hlength).

      pose proof
        (InstructionPattern_match_sound
           pattern instr map map1 Hhead)
        as Hhead_inst.

      pose proof
        (InstructionPattern_match_list_extends
           patterns instrs map1 map' Hmatch)
        as Hextends.

      pose proof
        (InstructionPattern_inst_extends
           pattern map1 map' instr
           Hextends Hhead_inst)
        as Hhead_inst'.

      exists (instr :: matched), suffix.

      split.
      * simpl.
        rewrite Hinstrs.
        reflexivity.

      * split.
        -- simpl.
           rewrite Hhead_inst'.
           rewrite Htail_inst.
           reflexivity.

        -- simpl.
           f_equal.
           exact Hlength.
Qed.

Lemma RewriteRule_apply_decompose :
  forall rule instrs result,
    RewriteRule_apply rule instrs = Some result ->
    exists map lhs rhs suffix,
      instrs = lhs ++ suffix
      /\
      InstructionPattern_inst_list
        (rule_lhs rule) map = Some lhs
      /\
      InstructionPattern_inst_list
        (rule_rhs rule) map = Some rhs
      /\
      RewriteResult_consumed result = length lhs
      /\
      RewriteResult_replacement result = rhs.
Proof.
  intros rule instrs result Happly.
  unfold RewriteRule_apply in Happly.

  destruct
    (InstructionPattern_match_list (rule_lhs rule) instrs PatternMap_empty)
    as [map |] eqn:Hmatch; try discriminate.

  destruct
    (InstructionPattern_inst_list (rule_rhs rule) map)
    as [rhs |] eqn:Hrhs; try discriminate.

  inversion Happly.
  subst result.
  clear Happly.

  destruct
    (InstructionPattern_match_list_decompose
       (rule_lhs rule)
       instrs
       PatternMap_empty
       map
       Hmatch)
    as
      (lhs & suffix
       & Hinstrs
       & Hlhs
       & Hlength).

  exists map, lhs, rhs, suffix.

  repeat split.
  - exact Hinstrs.
  - exact Hlhs.
  - exact Hrhs.
  - simpl.
    symmetry.
    exact Hlength.
Qed.

Lemma Instruction_list_qbits_valid_app_inv :
  forall lhs rhs,
    Instruction_list_qbits_valid (lhs ++ rhs) ->
    Instruction_list_qbits_valid lhs
    /\
    Instruction_list_qbits_valid rhs.
Proof.
  induction lhs as [| instr lhs IH].

  - intros rhs Hvalid.

    split.
    + constructor.
    + exact Hvalid.

  - intros rhs Hvalid.

    change
      (Instruction_list_qbits_valid
         (instr :: (lhs ++ rhs)))
      in Hvalid.

    inversion Hvalid as
      [| instr' rest' Hinstr Hrest];
      subst.

    destruct
      (IH rhs Hrest)
      as [Hlhs Hrhs].

    split.
    + constructor.
      * exact Hinstr.
      * exact Hlhs.

    + exact Hrhs.
Qed.

Lemma skipn_prefix_length :
  forall (A : Type)
         (lhs rhs : list A),
    skipn (length lhs) (lhs ++ rhs) = rhs.
Proof.
  intros A lhs.

  induction lhs as [| value lhs IH].

  - intros rhs.
    reflexivity.

  - intros rhs.
    simpl.
    apply IH.
Qed.

Theorem PatternRuleValid_implies_RewriteRuleValid :
  forall rule,
    PatternRuleValid rule ->
    RewriteRuleValid rule.
Proof.
  intros rule Hpattern.
  unfold RewriteRuleValid.

  intros instrs result Hvalid Happly.

  destruct
    (RewriteRule_apply_decompose
       rule instrs result Happly)
    as
      (map & lhs & rhs & suffix
       & Hinstrs
       & Hlhs
       & Hrhs
       & Hconsumed
       & Hreplacement).

  subst instrs.

  destruct
    (Instruction_list_qbits_valid_app_inv
       lhs suffix Hvalid)
    as [Hlhs_valid Hsuffix_valid].

  pose proof
    (Hpattern
       map lhs rhs
       Hlhs Hrhs Hlhs_valid)
    as Hlocal.

  rewrite Hconsumed.
  rewrite Hreplacement.
  rewrite skipn_prefix_length.

  repeat rewrite Instruction_equiv_Seq_list_list_eq.
  apply Instruction_equiv_rewrite_start.
  exact Hlocal.
Qed.

Theorem RewriteRule_apply_nth_list_sound:
  forall rule,
    RewriteRuleValid rule ->
    forall instrs occurrence,
      Instruction_list_qbits_valid instrs ->
      Instruction_equiv nq
        (SeqInstr instrs)
        (SeqInstr (RewriteRule_apply_nth_list rule instrs occurrence)).
Proof.
  intros rule Hrule.

  induction instrs as [| current rest IH].
  - intros occurrence Hvalid.
    simpl.
    destruct (RewriteRule_apply rule []) as [result |] eqn:Happly; try reflexivity.
    destruct occurrence; try reflexivity.
    apply Hrule.
    apply Hvalid.
    apply Happly.
  - intros occurrence Hvalid.
    inversion Hvalid as
      [| current' rest' Hcurrent Hrest];
      subst.
    simpl.
    destruct (RewriteRule_apply rule (current :: rest))
      as [result |] eqn:Happly.
    + destruct occurrence as [| occurrence'].
      * apply Hrule; assumption.
      * repeat rewrite Instruction_equiv_Seq_list_eq.
        apply Instruction_equiv_rewrite_end.
        apply IH.
        apply Hrest.
    + repeat rewrite Instruction_equiv_Seq_list_eq.
      apply Instruction_equiv_rewrite_end.
      apply IH.
      apply Hrest.
Qed.

Lemma Instruction_list_simp_eq:
  forall (instrs : list Instruction),
  Instruction_equiv nq
  (Instruction_list_simp instrs)
  (SeqInstr instrs).
Proof.
  intros.
  destruct instrs; simpl.
  - intros ps Hps. reflexivity.
  - destruct instrs; simpl; try reflexivity.
    rewrite Instruction_equiv_Seq_singleton.
    reflexivity.
Qed.

Lemma RewriteRule_apply_nth_sound:
  forall rule,
    RewriteRuleValid rule ->
    forall instr occurrence,
      Instruction_qbits_valid instr ->
      Instruction_equiv nq
        instr
        (RewriteRule_apply_nth rule instr occurrence).
Proof.
  intros rule Hrule.
  intros instr occurrence Hvalid.
  induction instr; cbv [RewriteRule_apply_nth].
  all: try (
    rewrite Instruction_list_simp_eq;
    rewrite <- RewriteRule_apply_nth_list_sound;
    try assumption;
    try (rewrite Instruction_equiv_Seq_singleton; reflexivity);
    constructor; try assumption; constructor).
  - apply RewriteRule_apply_nth_list_sound.
    apply Hrule.
    induction l; inversion Hvalid.
    + constructor.
    + assumption.
  - apply Instruction_if_Proper.
    apply IHinstr.
    inversion Hvalid.
    assumption.
Qed.

End PATTERN.

Section TRANSFORM_FUNCTIONS.

Variable nq: nat.

Definition Rule_I_to_XX : RewriteRule :=
  {|
    rule_lhs :=
      [Pat_I (NatVar 0)];

    rule_rhs :=
      [Pat_X (NatVar 0);
       Pat_X (NatVar 0)]
  |}.

Definition Function_I_XX
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  RewriteRule_apply_nth Rule_I_to_XX instr occurrence.

Definition Rule_I_to_YY : RewriteRule :=
  {|
    rule_lhs :=
      [Pat_I (NatVar 0)];

    rule_rhs :=
      [Pat_Y (NatVar 0);
       Pat_Y (NatVar 0)]
  |}.

Definition Function_I_YY
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  RewriteRule_apply_nth Rule_I_to_YY instr occurrence.

Definition Transform_functions : list (Instruction -> nat -> Instruction) :=
  [
    Function_I_XX;
    Function_I_YY
  ].

Theorem Transform_functions_valid:
  forall (instr: Instruction) (occurrence: nat),
  Instruction_qbits_valid nq instr ->
  Forall (fun f => Instruction_equiv nq instr (f instr occurrence)) Transform_functions.
Proof.
  intros.
  repeat apply Forall_cons; try apply Forall_nil.
  all: apply RewriteRule_apply_nth_sound; try assumption.
  all: apply PatternRuleValid_implies_RewriteRuleValid.
  all: intros map lhs rhs Hlhs Hrhs Hvalid; simpl in Hlhs, Hrhs.
  all: destruct (NatMap.find 0%nat map)
    as [qbit |] eqn:Hqbit;
    try discriminate.
  all: inversion Hlhs; subst lhs.
  all: inversion Hrhs; subst rhs.
  all: symmetry.
  1: apply Transform_X_X.
  2: apply Transform_Y_Y.
  all: inversion Hvalid as [| h rt Hinstr Hrest]; subst.
  all: inversion Hinstr; subst.
  all: assumption.
Qed.

End TRANSFORM_FUNCTIONS.
