Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Valid.
Require Import QASMInfer.transform.Commute.
Require Import QASMInfer.transform.Transform.

From Stdlib Require Import String.
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
  | NatExact: nat -> NatPattern
  | NatVar: nat -> NatPattern.

Definition NatPattern_match (pattern : NatPattern) (value : nat) (map : PatternMap)
    : option PatternMap :=
  match pattern with
  | NatExact expected =>
      if Nat.eqb expected value
      then Some map
      else None
  | NatVar variable =>
      PatternMap_bind variable value map
  end.

Definition NatPattern_inst
    (pattern : NatPattern)
    (subst : PatternMap)
    : option nat :=
  match pattern with
  | NatExact value => Some value
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

(* ================================================================ *)
(* Deep rewrite traversal                                           *)
(* ================================================================ *)

(*
  Search order:

    1. a rule occurrence beginning at the current list position;
    2. the subtree rooted at the current instruction;
    3. the remaining sibling instructions.

  RewriteContinue n means that no rewrite has yet been performed
  and n more matching occurrences must be skipped.  RewriteDone
  means that the requested occurrence has been rewritten.

  Termination is purely structural:

    - RewriteRule_apply_nth_result recursively visits only the body
      of an IfInstr or an element of a SeqInstr list;
    - its local rewrite_list function recursively visits only the tail
      of the remaining instruction list.

  Both recursive calls are checked structurally; no well-founded recursion
  command or generated termination proof is used.
*)

Fixpoint RewriteRule_match_count_list
    (rule : RewriteRule) (instrs : list Instruction) : nat :=
  match instrs with
  | [] =>
      match RewriteRule_apply rule [] with
      | Some _ => 1
      | None => 0
      end
  | _ :: rest =>
      match RewriteRule_apply rule instrs with
      | Some _ =>
          S (RewriteRule_match_count_list rule rest)

      | None =>
          RewriteRule_match_count_list rule rest
      end
  end.

Fixpoint RewriteRule_match_count
    (rule : RewriteRule) (instr : Instruction) : nat :=
  match instr with
  | SeqInstr instrs =>
      RewriteRule_match_count_list rule instrs
  | IfInstr _ _ body =>
      RewriteRule_match_count rule body
  | _ =>
      RewriteRule_match_count_list rule [instr]
  end.

Inductive RewriteStatus : Type :=
  | RewriteDone
  | RewriteContinue : nat -> RewriteStatus.

Fixpoint RewriteRule_apply_nth_list_result
    (rule : RewriteRule)
    (rewrite_instr : Instruction -> nat -> Instruction * RewriteStatus)
    (remaining : list Instruction)
    (remaining_occurrence : nat)
    {struct remaining}
    : list Instruction * RewriteStatus :=
  match remaining with
  | [] =>
      ([], RewriteContinue remaining_occurrence)
  | current :: rest =>
      (* First try a rule whose lhs starts at this list position. *)
      match RewriteRule_apply rule remaining with
      | Some result =>
          match remaining_occurrence with
          | O =>
              ( RewriteResult_replacement result
                ++ skipn
                     (RewriteResult_consumed result)
                     remaining,
                RewriteDone
              )
          | S occurrence' =>
              (*
                Preserve the original overlapping-match behavior:
                after skipping this match, advance by one instruction.
              *)
              let '(rest', status) :=
                RewriteRule_apply_nth_list_result
                  rule rewrite_instr rest occurrence'
              in
              (current :: rest', status)
          end
      | None =>
          (*
            No match starts here. Search current's subtree first;
            if it contains no requested occurrence, continue with rest.
          *)
          let '(current', current_status) :=
            rewrite_instr current remaining_occurrence
          in
          match current_status with
          | RewriteDone =>
              (current' :: rest, RewriteDone)

          | RewriteContinue occurrence' =>
              let '(rest', rest_status) :=
                RewriteRule_apply_nth_list_result
                  rule rewrite_instr rest occurrence'
              in
              (current' :: rest', rest_status)
          end
      end
  end
.

Fixpoint RewriteRule_apply_nth_result
    (rule : RewriteRule)
    (instr : Instruction)
    (occurrence : nat)
    {struct instr}
    : Instruction * RewriteStatus :=
  match instr with
  | SeqInstr instrs =>
      let '(instrs', status) :=
        RewriteRule_apply_nth_list_result
          rule (RewriteRule_apply_nth_result rule) instrs occurrence
      in
      (SeqInstr instrs', status)
  | IfInstr cbit expected body =>
      let '(body', status) :=
        RewriteRule_apply_nth_result rule body occurrence
      in
      (IfInstr cbit expected body', status)
  | _ =>
      (* Atomic instruction: test the singleton list at this position. *)
      match RewriteRule_apply rule [instr] with
      | Some result =>
          match occurrence with
          | O =>
              ( Instruction_list_simp
                  (RewriteResult_replacement result
                   ++ skipn
                        (RewriteResult_consumed result)
                        [instr]),
                RewriteDone
              )
          | S occurrence' =>
              (instr, RewriteContinue occurrence')
          end
      | None =>
          (instr, RewriteContinue occurrence)
      end
  end.

Definition RewriteRule_apply_nth
    (rule : RewriteRule)
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  fst (RewriteRule_apply_nth_result rule instr occurrence).

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

Inductive TransformParameter : Type :=
  | Param_None : TransformParameter
  | Param_qbit1 : nat -> TransformParameter
  | Param_qbit2 : nat -> nat -> TransformParameter.

Record TransformSpec : Type := {
  transform_name : string;
  transform_rule : TransformParameter -> option RewriteRule;
  param_count : nat; (* Parameter count of TransformParameter; to inform OCaml implementation *)
}.

Definition TransformSpec_count
    (spec : TransformSpec)
    (param : TransformParameter)
    (instr : Instruction)
    : nat :=
  match transform_rule spec param with
  | Some rule =>
      RewriteRule_match_count rule instr
  | None =>
      0
  end.

Definition TransformSpec_apply
    (spec : TransformSpec)
    (param : TransformParameter)
    (instr : Instruction)
    (occurrence : nat)
    : option Instruction :=
  match transform_rule spec param with
  | Some rule =>
      Some (RewriteRule_apply_nth rule instr occurrence)
  | None =>
      None
  end.

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
  destruct (NatMap.find variable map) as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq; try discriminate.
    inversion Hbind; subst.
    apply PatternMap_extends_refl.
  - inversion Hbind; subst.
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
  destruct (NatMap.find variable map) as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq; try discriminate.
    apply Nat.eqb_eq in Heq.
    inversion Hbind; subst.
    apply Hfind.
  - inversion Hbind; subst.
    apply NatMapFacts.add_eq_o.
    reflexivity.
Qed.

Lemma NatPattern_match_extends :
  forall pattern value map map',
    NatPattern_match pattern value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern; simpl in *.
  - destruct (Nat.eqb n value); try discriminate.
    inversion Hmatch; subst.
    apply PatternMap_extends_refl.
  - eapply PatternMap_bind_extends.
    apply Hmatch.
Qed.

Lemma NatPattern_match_sound :
  forall pattern value map map',
    NatPattern_match pattern value map = Some map' ->
    NatPattern_inst pattern map' = Some value.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern; simpl in *.
  - destruct (Nat.eqb n value) eqn:E; try discriminate.
    f_equal.
    apply Nat.eqb_eq.
    apply E.
  - apply PatternMap_bind_find in Hmatch.
    exact Hmatch.
Qed.

Lemma NatPattern_inst_extends :
  forall pattern map1 map2 value,
    PatternMap_extends map1 map2 ->
    NatPattern_inst pattern map1 = Some value ->
    NatPattern_inst pattern map2 = Some value.
Proof.
  intros pattern map1 map2 value Hextends Hinst.
  destruct pattern; simpl in *.
  - apply Hinst.
  - apply Hextends.
    apply Hinst.
Qed.

Lemma InstructionPattern_inst_extends :
  forall pattern map1 map2 instr,
    PatternMap_extends map1 map2 ->
    InstructionPattern_inst pattern map1 = Some instr ->
    InstructionPattern_inst pattern map2 = Some instr.
Proof.
  intros pattern map1 map2 instr Hextends Hinst.
  destruct pattern; simpl in *.
  - assumption.
  - destruct (NatPattern_inst n map1) as [qbit |] eqn:Hqbit; try discriminate.
    rewrite NatPattern_inst_extends with (map1 := map1) (value := qbit).
    all: assumption.
  - destruct (NatPattern_inst n map1) as [control |] eqn:Hcontrol; try discriminate.
    destruct (NatPattern_inst n0 map1) as [target |] eqn:Htarget; try discriminate.
    rewrite NatPattern_inst_extends with (map1 := map1) (value := control).
    rewrite NatPattern_inst_extends with (map1 := map1) (value := target).
    all: assumption.
  - destruct (NatPattern_inst n map1) as [qbit1 |] eqn:Hqbit1; try discriminate.
    destruct (NatPattern_inst n0 map1) as [qbit2 |] eqn:Hqbit2; try discriminate.
    rewrite NatPattern_inst_extends with (map1 := map1) (value := qbit1).
    rewrite NatPattern_inst_extends with (map1 := map1) (value := qbit2).
    all: assumption.
  - destruct (NatPattern_inst n map1) as [qbit |] eqn:Hqbit; try discriminate.
    destruct (NatPattern_inst n0 map1) as [cbit |] eqn:Hcbit; try discriminate.
    rewrite NatPattern_inst_extends with (map1 := map1) (value := qbit).
    rewrite NatPattern_inst_extends with (map1 := map1) (value := cbit).
    all: assumption.
  - destruct (NatPattern_inst n map1) as [qbit |] eqn:Hqbit; try discriminate.
    rewrite NatPattern_inst_extends with (map1 := map1) (value := qbit).
    all: assumption.
Qed.

Lemma InstructionPattern_match_extends :
  forall pattern instr map map',
    InstructionPattern_match pattern instr map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros pattern instr map map' Hmatch.
  destruct pattern as [
    | theta' phi' lambda' qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern
  ], instr as [
    | theta phi lambda qbit
    | control target
    | qbit1 qbit2
    | qbit cbit
    | instrs
    | cbit expected body
    | qbit
  ]; try discriminate; inversion Hmatch; subst.
  - apply PatternMap_extends_refl.
  - destruct (R_eqb theta theta');
    destruct (R_eqb phi phi');
    destruct (R_eqb lambda lambda'); try discriminate.
    apply NatPattern_match_extends with qbit_pattern qbit.
    assumption.
  - destruct (NatPattern_match control_pattern control map) eqn:H; try discriminate.
    apply PatternMap_extends_trans with p.
    + apply NatPattern_match_extends with control_pattern control.
      assumption.
    + apply NatPattern_match_extends with target_pattern target.
      assumption.
  - destruct (NatPattern_match qbit1_pattern qbit1 map) eqn:H; try discriminate.
    apply PatternMap_extends_trans with p.
    + apply NatPattern_match_extends with qbit1_pattern qbit1.
      assumption.
    + apply NatPattern_match_extends with qbit2_pattern qbit2.
      assumption.
  - destruct (NatPattern_match qbit_pattern qbit map) eqn:H; try discriminate.
    apply PatternMap_extends_trans with p.
    + apply NatPattern_match_extends with qbit_pattern qbit.
      assumption.
    + apply NatPattern_match_extends with cbit_pattern cbit.
      assumption.
  - apply NatPattern_match_extends with qbit_pattern qbit.
    assumption.
Qed.

Lemma InstructionPattern_match_sound :
  forall pattern instr map map',
    InstructionPattern_match pattern instr map = Some map' ->
    InstructionPattern_inst pattern map' = Some instr.
Proof.
  intros pattern instr map map' Hmatch.
  destruct pattern as [
    | theta' phi' lambda' qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern
  ], instr as [
    | theta phi lambda qbit
    | control target
    | qbit1 qbit2
    | qbit cbit
    | instrs
    | cbit expected body
    | qbit
  ]; try discriminate; inversion Hmatch as [H]; subst.
  - reflexivity.
  - destruct (R_eqb theta theta') eqn:Htheta;
    destruct (R_eqb phi phi') eqn:Hphi;
    destruct (R_eqb lambda lambda') eqn:Hlambda; try discriminate.
    apply R_eqb_eq in Htheta, Hphi, Hlambda; subst.
    simpl.
    erewrite NatPattern_match_sound with (value := qbit).
    reflexivity.
    apply H.
  - destruct (NatPattern_match control_pattern control map) eqn:H'; try discriminate.
    simpl.
    erewrite NatPattern_inst_extends with (value := control).
    erewrite NatPattern_match_sound with (value := target).
    + reflexivity.
    + apply H.
    + eapply NatPattern_match_extends. apply H.
    + eapply NatPattern_match_sound. apply H'.
  - destruct (NatPattern_match qbit1_pattern qbit1 map) eqn:H'; try discriminate.
    simpl.
    erewrite NatPattern_inst_extends with (value := qbit1).
    erewrite NatPattern_match_sound with (value := qbit2).
    + reflexivity.
    + apply H.
    + eapply NatPattern_match_extends. apply H.
    + eapply NatPattern_match_sound. apply H'.
  - destruct (NatPattern_match qbit_pattern qbit map) eqn:H'; try discriminate.
    simpl.
    erewrite NatPattern_inst_extends with (value := qbit).
    erewrite NatPattern_match_sound with (value := cbit).
    + reflexivity.
    + apply H.
    + eapply NatPattern_match_extends. apply H.
    + eapply NatPattern_match_sound. apply H'.
  - simpl.
    erewrite NatPattern_match_sound with (value := qbit).
    reflexivity.
    apply H.
Qed.

Lemma InstructionPattern_match_list_extends :
  forall patterns instrs map map',
    InstructionPattern_match_list
      patterns instrs map = Some map' ->
    PatternMap_extends map map'.
Proof.
  induction patterns as [| pattern patterns IH].
  - intros instrs map map' Hmatch.
    simpl in Hmatch.
    inversion Hmatch; subst.
    apply PatternMap_extends_refl.
  - intros instrs map map' Hmatch.
    destruct instrs as [| instr instrs];
    simpl in Hmatch; try discriminate.
    destruct (InstructionPattern_match pattern instr map)
    as [p |] eqn:Hhead; try discriminate.
    apply PatternMap_extends_trans with p.
    + eapply InstructionPattern_match_extends.
       apply Hhead.
    + eapply IH.
      apply Hmatch.
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
    inversion Hmatch; subst.
    exists [], instrs.
    repeat split; reflexivity.
  - intros instrs map map' Hmatch.
    destruct instrs as [| instr instrs];
    simpl in Hmatch; try discriminate.
    destruct (InstructionPattern_match pattern instr map)
    as [p |] eqn:Hhead; try discriminate.
    destruct (IH instrs p map' Hmatch)
    as (matched & suffix & Hinstrs & Htail_inst & Hlength).
    exists (instr :: matched), suffix.
    repeat split; simpl.
    + rewrite Hinstrs.
      reflexivity.
    + erewrite InstructionPattern_inst_extends.
      rewrite Htail_inst.
      reflexivity.
      * eapply InstructionPattern_match_list_extends.
        apply Hmatch.
      * eapply InstructionPattern_match_sound.
        apply Hhead.
    + rewrite Hlength.
      reflexivity.
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
  inversion Happly; subst.
  clear Happly.
  destruct (InstructionPattern_match_list_decompose
    (rule_lhs rule) instrs PatternMap_empty map Hmatch)
  as (lhs & suffix & Hinstrs & Hlhs & Hlength).
  exists map, lhs, rhs, suffix.
  repeat split; try assumption.
  simpl.
  symmetry.
  apply Hlength.
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
    + apply Hvalid.
  - intros rhs Hvalid.
    simpl in Hvalid.
    inversion Hvalid as
      [| instr' rest' Hinstr Hrest];
      subst.
    destruct (IH rhs Hrest) as [Hlhs Hrhs].
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

Theorem PatternRuleValid_implies_RewriteRuleValid :
  forall rule,
    PatternRuleValid rule ->
    RewriteRuleValid rule.
Proof.
  intros rule Hpattern.
  unfold RewriteRuleValid.
  intros instrs result Hvalid Happly.
  destruct (RewriteRule_apply_decompose rule instrs result Happly)
    as (map & lhs & rhs & suffix & Hinstrs & Hlhs & Hrhs & Hconsumed & Hreplacement).
  subst instrs.
  destruct (Instruction_list_qbits_valid_app_inv lhs suffix Hvalid)
    as [Hlhs_valid Hsuffix_valid].
  rewrite Hconsumed.
  rewrite Hreplacement.
  rewrite skipn_prefix_length.

  repeat rewrite Instruction_equiv_Seq_list_list_eq.
  apply Instruction_equiv_rewrite_start.
  unfold PatternRuleValid in Hpattern.
  apply Hpattern with map.
  all: assumption.
Qed.

Scheme Instruction_qbits_valid_induction :=
  Induction for Instruction_qbits_valid Sort Prop
with Instruction_list_qbits_valid_induction :=
  Induction for Instruction_list_qbits_valid Sort Prop.

Definition RewriteRule_apply_nth_result_list_sound
  (rule: RewriteRule) (Hrule: RewriteRuleValid rule)
  (instrs: list Instruction) (Hinstrs: Instruction_list_qbits_valid instrs): Prop :=
  forall occurrence instrs' status,
  RewriteRule_apply_nth_list_result
    rule (RewriteRule_apply_nth_result rule) instrs occurrence
    = (instrs', status) ->
  match status with
  | RewriteDone =>
    Instruction_equiv nq (SeqInstr instrs) (SeqInstr instrs')
  | RewriteContinue _ =>
    instrs' = instrs
  end.

Lemma RewriteRule_apply_nth_result_sound:
  forall rule, RewriteRuleValid rule ->
  forall instr, Instruction_qbits_valid instr ->
  forall occurrence instr' status,
  RewriteRule_apply_nth_result rule instr occurrence = (instr', status) ->
  match status with
  | RewriteDone =>
    Instruction_equiv nq instr instr'
  | RewriteContinue _ =>
    instr' = instr
  end.
Proof.
  intros rule Hrule instr Hvalid.
  induction Hvalid using Instruction_qbits_valid_induction
  with (P0 := RewriteRule_apply_nth_result_list_sound rule Hrule);
  intros occurrence instr' status Hresult; simpl in *.
  1-5, 8: destruct (RewriteRule_apply rule _) eqn:Happly; try (inversion Hresult; reflexivity).
  1-6: destruct occurrence; inversion Hresult; try reflexivity; subst.
  1-6: rewrite Instruction_list_simp_eq.
  1-6: unfold RewriteRuleValid in Hrule; rewrite <- Hrule.
  all: try (rewrite Instruction_equiv_Seq_singleton; reflexivity).
  all: try (constructor; constructor).
  all: try assumption.
  - destruct
      (RewriteRule_apply_nth_list_result
        rule (RewriteRule_apply_nth_result rule) instrs occurrence)
    as [instrs' status'] eqn:Hlist.
    inversion Hresult; subst.
    specialize (IHHvalid occurrence instrs' status Hlist).
    destruct status; subst.
    + apply IHHvalid.
    + reflexivity.
  - destruct
      (RewriteRule_apply_nth_result rule body occurrence)
      as [body' status'] eqn:Hbody.
    inversion Hresult; subst.
    specialize (IHHvalid occurrence body' status Hbody).
    destruct status; subst.
    + apply Instruction_if_Proper.
      apply IHHvalid.
    + reflexivity.
  - inversion Hresult; subst.
    reflexivity.
  - destruct
      (RewriteRule_apply rule (instr :: instrs))
      as [result |] eqn:Happly.
    + destruct occurrence.
      * inversion Hresult; subst.
        apply Hrule.
        constructor; assumption.
        assumption.
      * destruct
          (RewriteRule_apply_nth_list_result
            rule (RewriteRule_apply_nth_result rule)
            instrs occurrence)
          as [rest' rest_status] eqn:Hrest_result.
        inversion Hresult; subst.
        specialize (IHHvalid0 occurrence rest' status Hrest_result).
        destruct status.
        -- repeat rewrite Instruction_equiv_Seq_list_eq.
           apply Instruction_equiv_rewrite_end.
           exact IHHvalid0.
        -- f_equal.
           exact IHHvalid0.
    + destruct
        (RewriteRule_apply_nth_result
           rule instr occurrence)
        as [current' current_status] eqn:Hcurrent_result.
      destruct current_status as [| occurrence'].
      * inversion Hresult; subst.
        specialize
          (IHHvalid occurrence current' RewriteDone Hcurrent_result).
        repeat rewrite Instruction_equiv_Seq_list_eq.
        apply Instruction_equiv_rewrite_start.
        exact IHHvalid.
      * destruct
          (RewriteRule_apply_nth_list_result
             rule (RewriteRule_apply_nth_result rule)
             instrs occurrence')
          as [rest' rest_status] eqn:Hrest_result.
          inversion Hresult; subst.
          specialize
            (IHHvalid
               occurrence current'
               (RewriteContinue occurrence')
               Hcurrent_result).
          specialize
            (IHHvalid0 occurrence' rest' status Hrest_result).
          simpl in IHHvalid.
          subst current'.
          destruct status.
        -- repeat rewrite Instruction_equiv_Seq_list_eq.
           apply Instruction_equiv_rewrite_end.
           exact IHHvalid0.
        -- f_equal.
           rewrite IHHvalid0.
           reflexivity.
Qed.

Theorem RewriteRule_apply_nth_sound:
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

  unfold RewriteRule_apply_nth.
  destruct
    (RewriteRule_apply_nth_result rule instr occurrence)
    as [instr' status] eqn:Hresult.
  set (RewriteRule_apply_nth_result_sound rule Hrule instr Hvalid occurrence instr' status) as H.
  simpl.
  rewrite Hresult in H.
  destruct status.
  - apply H; reflexivity.
  - rewrite H; reflexivity.
Qed.

End PATTERN.

Section TRANSFORM_FUNCTIONS.

Variable nq: nat.

Definition Rule_Insert_I (qbit: nat) : RewriteRule :=
  {|
    rule_lhs := [];
    rule_rhs := [Pat_I (NatExact qbit)]
  |}.

Definition Rule_I_to_XX : RewriteRule :=
  {|
    rule_lhs :=
      [Pat_I (NatVar 0)];

    rule_rhs :=
      [Pat_X (NatVar 0);
       Pat_X (NatVar 0)]
  |}.

Definition Rule_I_to_YY : RewriteRule :=
  {|
    rule_lhs :=
      [Pat_I (NatVar 0)];

    rule_rhs :=
      [Pat_Y (NatVar 0);
       Pat_Y (NatVar 0)]
  |}.

Definition Transform_simple_rule (rule: RewriteRule) : TransformParameter -> option RewriteRule :=
  fun param =>
    match param with
    | Param_None => Some rule
    | _ => None
    end.

Definition Transform_spec_list : list TransformSpec :=
  [
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
      param_count := 1;
    |};
    {|
      transform_name := "I_to_XX";
      transform_rule := Transform_simple_rule Rule_I_to_XX;
      param_count := 0;
    |};
    {|
      transform_name := "I_to_YY";
      transform_rule := Transform_simple_rule Rule_I_to_YY;
      param_count := 0;
    |}
  ].

(* If occurrence is smaller than match count, applying really changes the instruction. *)
Lemma RewriteRule_apply_nth_list_neq:
  forall rule instrs occurrence,
  RewriteRuleValid nq rule ->
  (occurrence < RewriteRule_match_count_list rule instrs)%nat ->
  RewriteRule_apply_nth rule (SeqInstr instrs) occurrence <> SeqInstr instrs.
Proof.
  intros.
Admitted.

Theorem Transform_functions_valid:
  forall (instr: Instruction) (occurrence: nat),
  Instruction_qbits_valid nq instr ->
  Forall (fun spec =>
    forall param instr',
    (TransformSpec_apply spec param instr occurrence = Some instr') ->
    Instruction_equiv nq instr instr'
  )
  Transform_spec_list.
Proof.
  intros.
  repeat apply Forall_cons; try apply Forall_nil.
  all: unfold TransformSpec_apply; simpl.
  all: intros param instr'; destruct param; intros H'; try discriminate.
  1: destruct (n <? nq)%nat eqn:Hn; try discriminate; rewrite Nat.ltb_lt in Hn. 
  all: inversion H'; subst.
  all: apply RewriteRule_apply_nth_sound; try assumption.
  all: apply PatternRuleValid_implies_RewriteRuleValid.
  all: intros map lhs rhs Hlhs Hrhs Hvalid; simpl in Hlhs, Hrhs.
  2-3: destruct (NatMap.find 0%nat map)
    as [qbit |] eqn:Hqbit;
    try discriminate.
  all: inversion Hlhs; subst lhs.
  all: inversion Hrhs; subst rhs.
  all: symmetry.
  1: apply Transform_I; assumption.
  1: apply Transform_X_X.
  2: apply Transform_Y_Y.
  all: inversion Hvalid as [| h rt Hinstr Hrest]; subst.
  all: inversion Hinstr; subst.
  all: assumption.
Qed.

End TRANSFORM_FUNCTIONS.
