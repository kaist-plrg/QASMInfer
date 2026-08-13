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
  | PRotate: Angle -> Angle -> Angle -> NatPattern -> InstructionPattern 
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
      if Angle_eqb theta theta'
         && Angle_eqb phi phi'
         && Angle_eqb lambda lambda'
      then NatPattern_match qbit_pattern qbit map
      else None
  | PCnot control_pattern target_pattern,
    CnotInstr control target =>
      let* map' := NatPattern_match control_pattern control map in
      NatPattern_match target_pattern target map'
  | PSwap qbit1_pattern qbit2_pattern,
    SwapInstr qbit1 qbit2 =>
      let* map' := NatPattern_match qbit1_pattern qbit1 map in
      NatPattern_match qbit2_pattern qbit2 map'
  | PMeasure qbit_pattern cbit_pattern,
    MeasureInstr qbit cbit =>
      let* map' := NatPattern_match qbit_pattern qbit map in
      NatPattern_match cbit_pattern cbit map'
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
      let* map' := InstructionPattern_match pattern instr map in
      InstructionPattern_match_list pattern_rest instr_rest map'
  end.

Definition InstructionPattern_inst
    (pattern : InstructionPattern)
    (map : PatternMap)
    : option Instruction :=
  match pattern with
  | PNop => Some NopInstr
  | PRotate theta phi lambda qbit_pattern =>
      let* qbit := NatPattern_inst qbit_pattern map in
      Some (RotateInstr theta phi lambda qbit)
  | PCnot control_pattern target_pattern =>
      let* control := NatPattern_inst control_pattern map in
      let* target := NatPattern_inst target_pattern map in
      Some (CnotInstr control target)
  | PSwap qbit1_pattern qbit2_pattern =>
      let* qbit1 := NatPattern_inst qbit1_pattern map in
      let* qbit2 := NatPattern_inst qbit2_pattern map in
      Some (SwapInstr qbit1 qbit2)
  | PMeasure qbit_pattern cbit_pattern =>
      let* qbit := NatPattern_inst qbit_pattern map in
      let* cbit := NatPattern_inst cbit_pattern map in
      Some (MeasureInstr qbit cbit)
  | PReset qbit_pattern =>
      let* qbit := NatPattern_inst qbit_pattern map in
      Some (ResetInstr qbit)
  end.

Fixpoint InstructionPattern_inst_list
    (patterns : list InstructionPattern)
    (map: PatternMap)
    {struct patterns}
    : option (list Instruction) :=
  match patterns with
  | [] => Some []
  | pattern :: pattern_rest =>
      let* instr := InstructionPattern_inst pattern map in
      let* instrs := InstructionPattern_inst_list pattern_rest map in
      Some (instr :: instrs)
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
  let* subst :=
    InstructionPattern_match_list
      (rule_lhs rule)
      instrs
      PatternMap_empty
  in
  let* replacement := InstructionPattern_inst_list (rule_rhs rule) subst in
  Some {|
    RewriteResult_consumed := length (rule_lhs rule);
    RewriteResult_replacement := replacement
  |}.

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

Definition RewriteRule_match_at
    (rule : RewriteRule) (instrs : list Instruction) : nat :=
  match RewriteRule_apply rule instrs with
  | Some _ => 1
  | None => 0
  end.

Fixpoint RewriteRule_match_count_top_list
    (rule : RewriteRule)
    (instrs : list Instruction)
    : nat :=
  match instrs with
  | [] =>
      0%nat
  | _ :: rest =>
      (RewriteRule_match_at rule instrs
       + RewriteRule_match_count_top_list rule rest)%nat
  end.

Definition RewriteRule_match_count_top
    (rule : RewriteRule)
    (instr : Instruction)
    : nat :=
  match instr with
  | SeqInstr instrs =>
      RewriteRule_match_count_top_list rule instrs
  | _ =>
      RewriteRule_match_at rule [instr]
  end.

Fixpoint RewriteRule_match_count
    (rule : RewriteRule) (instr : Instruction) {struct instr} : nat :=
  match instr with
  | SeqInstr instrs =>
      let fix count_list (xs : list Instruction) : nat :=
          match xs with
          | [] =>
              0%nat
          | head :: rest =>
              (RewriteRule_match_at rule xs
              +
              (match head with
               | SeqInstr _ =>
                  RewriteRule_match_count rule head
               | IfInstr _ _ _ =>
                  RewriteRule_match_count rule head
               | _ =>
                   0
               end)
              +
              count_list rest)%nat
          end
      in
      count_list instrs
  | IfInstr _ _ body =>
      RewriteRule_match_count rule body
  | _ =>
      RewriteRule_match_at rule [instr]
  end.

Inductive RewriteStatus : Type :=
  | RewriteDone
  | RewriteContinue : nat -> RewriteStatus.

Fixpoint RewriteRule_apply_top_level_list_result
    (rule : RewriteRule)
    (postprocesses : Instruction -> Instruction)
    (remaining : list Instruction)
    (remaining_occurrence : nat)
    {struct remaining}
    : list Instruction * RewriteStatus :=
  match remaining with
  | [] =>
      ([], RewriteContinue remaining_occurrence)
  | current :: rest =>
      match RewriteRule_apply rule remaining with
      | Some result =>
          match remaining_occurrence with
          | O =>
              ( RewriteResult_replacement result
                ++ map postprocesses
                     (skipn (RewriteResult_consumed result) remaining),
                RewriteDone
              )
          | S occurrence' =>
              let '(rest', status) :=
                RewriteRule_apply_top_level_list_result
                  rule postprocesses rest occurrence'
              in
              (current :: rest', status)
          end
      | None =>
          let '(rest', status) :=
            RewriteRule_apply_top_level_list_result
              rule postprocesses rest remaining_occurrence
          in
          (current :: rest', status)
      end
  end.

Definition RewriteRule_apply_top_level_result
    (rule : RewriteRule)
    (postprocesses : Instruction -> Instruction)
    (instr : Instruction)
    (occurrence : nat)
    : Instruction * RewriteStatus :=
  match instr with
  | SeqInstr instrs =>
      let '(instrs', status) :=
        RewriteRule_apply_top_level_list_result
          rule postprocesses instrs occurrence
      in
      (SeqInstr instrs', status)
  | _ =>
      match RewriteRule_apply rule [instr] with
      | Some result =>
          match occurrence with
          | O =>
              ( Instruction_list_simp
                  (RewriteResult_replacement result
                   ++ map postprocesses
                        (skipn (RewriteResult_consumed result) [instr])),
                RewriteDone
              )
          | S occurrence' =>
              (instr, RewriteContinue occurrence')
          end
      | None =>
          (instr, RewriteContinue occurrence)
      end
  end.

Fixpoint RewriteRule_apply_nth_list_result
    (rule : RewriteRule)
    (postprocesses : Instruction -> Instruction)
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
                ++ map postprocesses (skipn
                     (RewriteResult_consumed result)
                     remaining),
                RewriteDone
              )
          | S occurrence' =>
              (*
                After skipping the match at this list position, continue in
                the same order used by RewriteRule_match_count: first search a
                structured current instruction, then the remaining siblings.
              *)
              match current with
              | SeqInstr _ | IfInstr _ _ _ =>
                  let '(current', current_status) :=
                    rewrite_instr current occurrence'
                  in
                  match current_status with
                  | RewriteDone =>
                      (current' :: rest, RewriteDone)

                  | RewriteContinue occurrence'' =>
                      let '(rest', rest_status) :=
                        RewriteRule_apply_nth_list_result
                          rule postprocesses rewrite_instr rest occurrence''
                      in
                      (current' :: rest', rest_status)
                  end
              | _ =>
                  let '(rest', status) :=
                    RewriteRule_apply_nth_list_result
                      rule postprocesses rewrite_instr rest occurrence'
                  in
                  (current :: rest', status)
              end
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
                  rule postprocesses rewrite_instr rest occurrence'
              in
              (current' :: rest', rest_status)
          end
      end
  end
.

Fixpoint RewriteRule_apply_nth_result
    (rule : RewriteRule)
    (postprocesses : Instruction -> Instruction)
    (instr : Instruction)
    (occurrence : nat)
    {struct instr}
    : Instruction * RewriteStatus :=
  match instr with
  | SeqInstr instrs =>
      let '(instrs', status) :=
        RewriteRule_apply_nth_list_result
          rule postprocesses (RewriteRule_apply_nth_result rule postprocesses) instrs occurrence
      in
      (SeqInstr instrs', status)
  | IfInstr cbit expected body =>
      let '(body', status) :=
        RewriteRule_apply_nth_result rule postprocesses body occurrence
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
                   ++ map postprocesses (skipn
                        (RewriteResult_consumed result)
                        [instr])),
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
    (postprocesses : Instruction -> Instruction)
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  fst (RewriteRule_apply_nth_result rule postprocesses instr occurrence).

Definition Postprocess_id : Instruction -> Instruction :=
  fun instr => instr.

Fixpoint RewriteRule_apply_deep_list_result
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
              match current with
              | SeqInstr _ | IfInstr _ _ _ =>
                  let '(current', current_status) :=
                    rewrite_instr current occurrence'
                  in
                  match current_status with
                  | RewriteDone =>
                      (current' :: rest, RewriteDone)
                  | RewriteContinue occurrence'' =>
                      let '(rest', rest_status) :=
                        RewriteRule_apply_deep_list_result
                          rule rewrite_instr rest occurrence''
                      in
                      (current' :: rest', rest_status)
                  end
              | _ =>
                  let '(rest', status) :=
                    RewriteRule_apply_deep_list_result
                      rule rewrite_instr rest occurrence'
                  in
                  (current :: rest', status)
              end
          end
      | None =>
          let '(current', current_status) :=
            rewrite_instr current remaining_occurrence
          in
          match current_status with
          | RewriteDone =>
              (current' :: rest, RewriteDone)
          | RewriteContinue occurrence' =>
              let '(rest', rest_status) :=
                RewriteRule_apply_deep_list_result
                  rule rewrite_instr rest occurrence'
              in
              (current' :: rest', rest_status)
          end
      end
  end.

Fixpoint RewriteRule_apply_deep_result
    (rule : RewriteRule)
    (instr : Instruction)
    (occurrence : nat)
    {struct instr}
    : Instruction * RewriteStatus :=
  match instr with
  | SeqInstr instrs =>
      let '(instrs', status) :=
        RewriteRule_apply_deep_list_result
          rule (RewriteRule_apply_deep_result rule) instrs occurrence
      in
      (SeqInstr instrs', status)
  | IfInstr cbit expected body =>
      let '(body', status) :=
        RewriteRule_apply_deep_result rule body occurrence
      in
      (IfInstr cbit expected body', status)
  | _ =>
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

Definition RewriteRule_apply_deep
    (rule : RewriteRule)
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  fst (RewriteRule_apply_deep_result rule instr occurrence).

Definition Pat_I (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate A0 A0 A0 qbit_pattern.

Definition Pat_X (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate API A0 API qbit_pattern.

Definition Pat_Y (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate API API2 API2 qbit_pattern.

Definition Pat_Z (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate A0 A0 API qbit_pattern.

Definition Pat_H (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate API2 A0 API qbit_pattern.

Definition Pat_S (qbit_pattern : NatPattern) : InstructionPattern :=
  PRotate A0 A0 API2 qbit_pattern.

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

Fixpoint Instruction_qbits_validb (instr : Instruction) : bool :=
  match instr with
  | NopInstr =>
      true
  | RotateInstr _ _ _ qbit =>
      qbit <? nq
  | CnotInstr control target =>
      (control <? nq) && (target <? nq)
  | SwapInstr qbit1 qbit2 =>
      (qbit1 <? nq) && (qbit2 <? nq)
  | MeasureInstr qbit _ =>
      qbit <? nq
  | SeqInstr instrs =>
      let fix list_validb
          (instrs : list Instruction)
          : bool :=
        match instrs with
        | [] =>
            true
        | instr :: rest =>
            Instruction_qbits_validb instr
            && list_validb rest
        end
      in
      list_validb instrs
  | IfInstr _ _ body =>
      Instruction_qbits_validb body
  | ResetInstr qbit =>
      qbit <? nq
  end.

Fixpoint Instruction_list_qbits_validb (instrs: list Instruction) : bool :=
  match instrs with
  | [] => true
  | instr :: rest =>
      Instruction_qbits_validb instr
      && Instruction_list_qbits_validb rest
  end.

Inductive TransformParameter : Type :=
  | Param_None : TransformParameter
  | Param_qbit1 : nat -> TransformParameter
  | Param_qbit2 : nat -> nat -> TransformParameter.

Inductive TransformStrategy : Type :=
  | TransformTopLevel : TransformStrategy
  | TransformDeep : TransformStrategy.

Record TransformSpec : Type := {
  transform_name : string;
  transform_rule : TransformParameter -> option RewriteRule;
  transform_postprocess : TransformParameter -> Instruction -> Instruction;
  transform_strategy : TransformStrategy;
  param_count : nat; (* Parameter count of TransformParameter; to inform OCaml implementation *)
}.

Definition TransformSpec_count
    (spec : TransformSpec)
    (param : TransformParameter)
    (instr : Instruction)
    : nat :=
  match transform_rule spec param with
  | Some rule =>
      match transform_strategy spec with
      | TransformTopLevel =>
          RewriteRule_match_count_top rule instr
      | TransformDeep =>
          RewriteRule_match_count rule instr
      end
  | None =>
      0
  end.

Definition TransformSpec_apply
    (spec : TransformSpec)
    (param : TransformParameter)
    (instr : Instruction)
    (occurrence : nat)
    : option Instruction :=
  let* rule := transform_rule spec param in
  let '(instr', status) :=
    match transform_strategy spec with
    | TransformTopLevel =>
        RewriteRule_apply_top_level_result
          rule (transform_postprocess spec param) instr occurrence
    | TransformDeep =>
        RewriteRule_apply_deep_result
          rule instr occurrence
    end
  in
  match status with
  | RewriteDone =>
      Some instr'
  | RewriteContinue _ =>
      None
  end.

(* ================================================================ *)
(* Proof                                                            *)
(* ================================================================ *)
Lemma Q_eqb_exact_eq :
  forall x y,
    Q_eqb_exact x y = true ->
    x = y.
Proof.
  intros x y Heq.
  unfold Q_eqb_exact in Heq.
  apply andb_true_iff in Heq as [Hnum Hden].
  apply Z.eqb_eq in Hnum.
  apply Pos.eqb_eq in Hden.
  destruct x as [xnum xden].
  destruct y as [ynum yden].
  simpl in *.
  subst.
  reflexivity.
Qed.

Lemma Angle_eqb_eq :
  forall x y,
    Angle_eqb x y = true ->
    x = y.
Proof.
  intros x y Heq.
  destruct x as [qx | rx], y as [qy | ry]; simpl in Heq; try discriminate.
  apply Q_eqb_exact_eq in Heq.
  subst.
  reflexivity.
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
  - destruct (Angle_eqb theta theta');
    destruct (Angle_eqb phi phi');
    destruct (Angle_eqb lambda lambda'); try discriminate.
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
  - destruct (Angle_eqb theta theta') eqn:Htheta;
    destruct (Angle_eqb phi phi') eqn:Hphi;
    destruct (Angle_eqb lambda lambda') eqn:Hlambda; try discriminate.
    apply Angle_eqb_eq in Htheta, Hphi, Hlambda; subst.
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

Lemma Instruction_qbits_validb_spec :
  forall instr,
    Instruction_qbits_validb instr = true <->
    Instruction_qbits_valid instr.
Proof.
  intros; split.
  - apply Instruction_ind' with (instr:=instr); simpl in *; try constructor.
    all: try (rewrite andb_true_iff in H; destruct H as [H0 H1]).
    all: try rewrite Nat.ltb_lt in H.
    all: try rewrite Nat.ltb_lt in H0, H1.
    all: try assumption.
    + induction is. constructor.
      inversion H; subst.
      rewrite andb_true_iff in H0; destruct H0.
      constructor.
      * apply H3. apply H0.
      * apply IHis. apply H4. apply H1.
    + apply H.
      assumption.
  - apply Instruction_ind' with (instr:=instr); simpl in *; intros.
    all: try (rewrite andb_true_iff; split).
    all: try apply Nat.ltb_lt.
    all: try (inversion H; assumption).
    + reflexivity.
    + induction is; try reflexivity.
      inversion H. inversion H0. inversion H6.
      rewrite andb_true_iff; split.
      * apply H3. apply H9.
      * apply IHis. apply H4.
        constructor. apply H10.
    + apply H. inversion H0. assumption.
Qed.

(* Connection between rewriting scheme and instruction equality proof *)

Definition PatternRuleValid
    (spec : TransformSpec)
    (param : TransformParameter)
    : Prop :=
  forall rule,
  transform_rule spec param = Some rule ->
  forall subst lhs rhs suffix,
  InstructionPattern_inst_list (rule_lhs rule) subst = Some lhs ->
  InstructionPattern_inst_list (rule_rhs rule) subst = Some rhs ->
  Instruction_list_qbits_valid (lhs ++ suffix) ->
  Instruction_behavioral_equiv nq
    (SeqInstr (lhs ++ suffix))
    (SeqInstr
      (rhs ++ map (transform_postprocess spec param) suffix)).

Definition RewriteRuleValid
    (spec : TransformSpec)
    (param : TransformParameter)
    : Prop :=
  forall rule,
  transform_rule spec param = Some rule ->
  forall instrs result,
    Instruction_list_qbits_valid instrs ->
    RewriteRule_apply rule instrs = Some result ->
    Instruction_behavioral_equiv nq
      (SeqInstr instrs)
      (SeqInstr
        (RewriteResult_replacement result
          ++ List.map
            (transform_postprocess spec param)
            (skipn (RewriteResult_consumed result) instrs))).

Definition PatternRuleEquivValid
    (spec : TransformSpec)
    (param : TransformParameter)
    : Prop :=
  forall rule,
  transform_rule spec param = Some rule ->
  forall subst lhs rhs,
    InstructionPattern_inst_list (rule_lhs rule) subst = Some lhs ->
    InstructionPattern_inst_list (rule_rhs rule) subst = Some rhs ->
    Instruction_list_qbits_valid lhs ->
    Instruction_equiv nq
      (SeqInstr lhs)
      (SeqInstr rhs).

Definition RewriteRuleEquivValid
    (spec : TransformSpec)
    (param : TransformParameter)
    : Prop :=
  forall rule,
  transform_rule spec param = Some rule ->
  forall instrs result,
    Instruction_list_qbits_valid instrs ->
    RewriteRule_apply rule instrs = Some result ->
    Instruction_equiv nq
      (SeqInstr instrs)
      (SeqInstr
        (RewriteResult_replacement result
         ++ skipn (RewriteResult_consumed result) instrs)).

Definition TransformSpecValid
  (spec : TransformSpec) : Prop :=
  forall param,
    match transform_strategy spec with
    | TransformTopLevel =>
        PatternRuleValid spec param
    | TransformDeep =>
        PatternRuleEquivValid spec param
    end.

Theorem PatternRuleValid_implies_RewriteRuleValid :
  forall spec param,
    PatternRuleValid spec param ->
    RewriteRuleValid spec param.
Proof.
  intros spec param Hpattern.
  unfold PatternRuleValid in Hpattern.
  unfold RewriteRuleValid.
  intros rule Hrule.
  intros instrs result Hvalid Happly.
  destruct (RewriteRule_apply_decompose rule instrs result Happly)
    as (subst & lhs & rhs & suffix & Hinstrs & Hlhs & Hrhs & Hconsumed & Hreplacement).
  subst instrs.
  rewrite Hconsumed.
  rewrite Hreplacement.
  rewrite skipn_prefix_length.
  eapply Hpattern; eauto.
Qed.

Theorem TransformSpec_rule_valid :
  forall spec param,
    transform_strategy spec = TransformTopLevel ->
    TransformSpecValid spec ->
    RewriteRuleValid spec param.
Proof.
  intros spec param Hstrategy Hvalid.
  apply PatternRuleValid_implies_RewriteRuleValid.
  specialize (Hvalid param).
  unfold TransformSpecValid in Hvalid.
  rewrite Hstrategy in Hvalid.
  exact Hvalid.
Qed.

Theorem PatternRuleEquivValid_implies_RewriteRuleEquivValid :
  forall spec param,
    PatternRuleEquivValid spec param ->
    RewriteRuleEquivValid spec param.
Proof.
  intros spec param Hpattern.
  unfold RewriteRuleEquivValid.
  intros rule Hrule instrs result Hvalid Happly.
  destruct (RewriteRule_apply_decompose rule instrs result Happly)
    as (subst & lhs & rhs & suffix & Hinstrs & Hlhs & Hrhs & Hconsumed & Hreplacement).
  subst instrs.
  destruct (Instruction_list_qbits_valid_app_inv lhs suffix Hvalid)
    as [Hlhs_valid _].
  rewrite Hconsumed.
  rewrite Hreplacement.
  rewrite skipn_prefix_length.
  repeat rewrite Instruction_equiv_Seq_list_list_eq.
  apply Instruction_equiv_rewrite_start.
  eapply Hpattern; eauto.
Qed.

Theorem TransformSpec_rule_equiv_valid :
  forall spec param,
    transform_strategy spec = TransformDeep ->
    TransformSpecValid spec ->
    RewriteRuleEquivValid spec param.
Proof.
  intros spec param Hstrategy Hvalid.
  apply PatternRuleEquivValid_implies_RewriteRuleEquivValid.
  specialize (Hvalid param).
  unfold TransformSpecValid in Hvalid.
  rewrite Hstrategy in Hvalid.
  exact Hvalid.
Qed.

Lemma RewriteRule_apply_top_level_single_result_sound :
  forall spec param rule instr,
    RewriteRuleValid spec param ->
    transform_rule spec param = Some rule ->
    Instruction_qbits_valid instr ->
    forall occurrence instr' status,
      match RewriteRule_apply rule [instr] with
      | Some result =>
          match occurrence with
          | O =>
              ( Instruction_list_simp
                  (RewriteResult_replacement result
                   ++ map (transform_postprocess spec param)
                        (skipn (RewriteResult_consumed result) [instr])),
                RewriteDone
              )
          | S occurrence' =>
              (instr, RewriteContinue occurrence')
          end
      | None =>
          (instr, RewriteContinue occurrence)
      end = (instr', status) ->
      match status with
      | RewriteDone =>
          Instruction_behavioral_equiv nq instr instr'
      | RewriteContinue _ =>
          instr' = instr
      end.
Proof.
  intros spec param rule instr Hrule_valid Hrule Hvalid
    occurrence instr' status Hresult.
  destruct (RewriteRule_apply rule [instr]) as [result |] eqn:Happly.
  - destruct occurrence as [| occurrence']; inversion Hresult; subst.
    + transitivity (SeqInstr [instr]).
      * symmetry.
        apply Instruction_equiv_implies_behavioral_equiv.
        apply Instruction_equiv_Seq_singleton.
      * transitivity
          (SeqInstr
            (RewriteResult_replacement result
             ++ map (transform_postprocess spec param)
                  (skipn (RewriteResult_consumed result) [instr]))).
        -- eapply Hrule_valid; eauto.
           constructor; [assumption | constructor].
        -- symmetry.
           apply Instruction_equiv_implies_behavioral_equiv.
           apply Instruction_list_simp_eq.
    + reflexivity.
  - inversion Hresult; subst.
    reflexivity.
Qed.

Lemma RewriteRule_apply_top_level_list_result_sound :
  forall spec param rule,
    RewriteRuleValid spec param ->
    transform_rule spec param = Some rule ->
    forall instrs,
      Instruction_list_qbits_valid instrs ->
      forall occurrence instrs' status,
        RewriteRule_apply_top_level_list_result
          rule (transform_postprocess spec param) instrs occurrence
        = (instrs', status) ->
        match status with
        | RewriteDone =>
            Instruction_behavioral_equiv nq
              (SeqInstr instrs)
              (SeqInstr instrs')
        | RewriteContinue _ =>
            instrs' = instrs
        end.
Proof.
  intros spec param rule Hrule_valid Hrule instrs Hvalid.
  induction instrs as [| instr instrs IH]; intros occurrence instrs' status Hresult.
  - simpl in Hresult.
    inversion Hresult; subst.
    reflexivity.
  - simpl in Hresult.
    inversion Hvalid as [| ? ? Hinstr_valid Hrest_valid]; subst.
    destruct (RewriteRule_apply rule (instr :: instrs)) as [result |] eqn:Happly.
    + destruct occurrence as [| occurrence'].
      * inversion Hresult; subst.
        eapply Hrule_valid; eauto.
      * destruct
          (RewriteRule_apply_top_level_list_result
            rule (transform_postprocess spec param) instrs occurrence')
          as [rest' rest_status] eqn:Hrest.
        specialize (IH Hrest_valid occurrence' rest' rest_status Hrest).
        destruct rest_status.
        -- inversion Hresult; subst.
           setoid_rewrite (Instruction_equiv_Seq_list_eq nq instr instrs).
           setoid_rewrite (Instruction_equiv_Seq_list_eq nq instr rest').
           eapply Instruction_behavioral_equiv_rewrite_end with
             (pre_instr := instr)
             (instr1 := SeqInstr instrs)
             (instr2 := SeqInstr rest').
           exact IH.
        -- inversion Hresult; subst.
           f_equal.
    + destruct
        (RewriteRule_apply_top_level_list_result
          rule (transform_postprocess spec param) instrs occurrence)
        as [rest' rest_status] eqn:Hrest.
      specialize (IH Hrest_valid occurrence rest' rest_status Hrest).
      destruct rest_status.
      * inversion Hresult; subst.
        setoid_rewrite (Instruction_equiv_Seq_list_eq nq instr instrs).
        setoid_rewrite (Instruction_equiv_Seq_list_eq nq instr rest').
        eapply Instruction_behavioral_equiv_rewrite_end with
          (pre_instr := instr)
          (instr1 := SeqInstr instrs)
          (instr2 := SeqInstr rest').
        exact IH.
      * inversion Hresult; subst.
        f_equal.
Qed.

Lemma RewriteRule_apply_top_level_result_sound :
  forall spec param rule,
    RewriteRuleValid spec param ->
    transform_rule spec param = Some rule ->
    forall instr,
      Instruction_qbits_valid instr ->
      forall occurrence instr' status,
        RewriteRule_apply_top_level_result
          rule (transform_postprocess spec param) instr occurrence
        = (instr', status) ->
        match status with
        | RewriteDone =>
            Instruction_behavioral_equiv nq instr instr'
        | RewriteContinue _ =>
            instr' = instr
        end.
Proof.
  intros spec param rule Hrule_valid Hrule instr Hvalid
    occurrence instr' status Hresult.
  destruct instr; simpl in Hresult.
  6: {
    inversion Hvalid as [| | | | | ? Hlist_valid | |]; subst.
    destruct
      (RewriteRule_apply_top_level_list_result
        rule (transform_postprocess spec param) l occurrence)
      as [instrs' status'] eqn:Hlist.
    inversion Hresult; subst.
    specialize
      (RewriteRule_apply_top_level_list_result_sound
        spec param rule Hrule_valid Hrule l Hlist_valid
        occurrence instrs' status Hlist)
      as Hsound.
    destruct status; simpl.
    + exact Hsound.
    + f_equal.
      exact Hsound.
  }
  all: eapply RewriteRule_apply_top_level_single_result_sound; eauto.
Qed.

Ltac solve_rewrite_apply_deep_list_atomic
    rule instrs occurrence Hresult IHHvalid0 :=
  destruct
    (RewriteRule_apply_deep_list_result
      rule (RewriteRule_apply_deep_result rule)
      instrs occurrence)
    as [rest' rest_status] eqn:Hrest_result;
  specialize (IHHvalid0 occurrence rest' rest_status Hrest_result);
  destruct rest_status;
  inversion Hresult; subst;
  [ repeat rewrite Instruction_equiv_Seq_list_eq;
    apply Instruction_equiv_rewrite_end;
    exact IHHvalid0
  | f_equal; exact IHHvalid0
  ].

Ltac solve_rewrite_apply_deep_list_current
    rule instrs Hresult IHHvalid IHHvalid0 Hcurrent_result :=
  match type of Hcurrent_result with
  | RewriteRule_apply_deep_result rule ?current ?occurrence =
      (?current', ?current_status) =>
      destruct current_status as [| occurrence'];
      [ inversion Hresult; subst;
        specialize
          (IHHvalid occurrence current' RewriteDone Hcurrent_result);
        repeat rewrite Instruction_equiv_Seq_list_eq;
        apply Instruction_equiv_rewrite_start;
        exact IHHvalid
      | destruct
          (RewriteRule_apply_deep_list_result
            rule (RewriteRule_apply_deep_result rule)
            instrs occurrence')
          as [rest' rest_status] eqn:Hrest_result;
        specialize
          (IHHvalid
            occurrence current'
            (RewriteContinue occurrence')
            Hcurrent_result);
        simpl in IHHvalid;
        subst current';
        specialize
          (IHHvalid0 occurrence' rest' rest_status Hrest_result);
        destruct rest_status;
        [ inversion Hresult; subst;
          repeat rewrite Instruction_equiv_Seq_list_eq;
          apply Instruction_equiv_rewrite_end;
          exact IHHvalid0
        | inversion Hresult; subst;
          f_equal
        ]
      ]
  end.

Ltac solve_rewrite_apply_deep_list_structured
    rule instrs Hresult IHHvalid IHHvalid0 :=
  match type of Hresult with
  | context[RewriteRule_apply_deep_result rule ?current ?occurrence] =>
      destruct
        (RewriteRule_apply_deep_result rule current occurrence)
        as [current' current_status] eqn:Hcurrent_result;
      solve_rewrite_apply_deep_list_current
        rule instrs Hresult IHHvalid IHHvalid0 Hcurrent_result
  end.

Lemma RewriteRule_apply_deep_single_result_sound :
  forall spec param rule instr,
    RewriteRuleEquivValid spec param ->
    transform_rule spec param = Some rule ->
    Instruction_qbits_valid instr ->
    forall occurrence instr' status,
      match RewriteRule_apply rule [instr] with
      | Some result =>
          match occurrence with
          | O =>
              ( Instruction_list_simp
                  (RewriteResult_replacement result
                   ++ skipn (RewriteResult_consumed result) [instr]),
                RewriteDone
              )
          | S occurrence' =>
              (instr, RewriteContinue occurrence')
          end
      | None =>
          (instr, RewriteContinue occurrence)
      end = (instr', status) ->
      match status with
      | RewriteDone =>
          Instruction_equiv nq instr instr'
      | RewriteContinue _ =>
          instr' = instr
      end.
Proof.
  intros spec param rule instr Hrule_valid Hrule Hvalid
    occurrence instr' status Hresult.
  destruct (RewriteRule_apply rule [instr]) as [result |] eqn:Happly.
  - destruct occurrence as [| occurrence']; inversion Hresult; subst.
    + transitivity (SeqInstr [instr]).
      * symmetry.
        apply Instruction_equiv_Seq_singleton.
      * transitivity
          (SeqInstr
            (RewriteResult_replacement result
             ++ skipn (RewriteResult_consumed result) [instr])).
        -- eapply Hrule_valid; eauto.
           constructor; [assumption | constructor].
        -- symmetry.
           apply Instruction_list_simp_eq.
    + reflexivity.
  - inversion Hresult; subst.
    reflexivity.
Qed.

Lemma RewriteRule_apply_deep_result_sound :
  forall spec param rule,
    transform_rule spec param = Some rule ->
    RewriteRuleEquivValid spec param ->
    forall instr,
      Instruction_qbits_valid instr ->
      forall occurrence instr' status,
        RewriteRule_apply_deep_result rule instr occurrence
        = (instr', status) ->
        match status with
        | RewriteDone =>
            Instruction_equiv nq instr instr'
        | RewriteContinue _ =>
            instr' = instr
        end.
Proof.
  intros spec param rule Hrule_find Hrule.
  pose (P := fun instr =>
    Instruction_qbits_valid instr ->
    forall occurrence instr' status,
      RewriteRule_apply_deep_result rule instr occurrence
      = (instr', status) ->
      match status with
      | RewriteDone =>
          Instruction_equiv nq instr instr'
      | RewriteContinue _ =>
          instr' = instr
      end).
  assert (list_sound :
    forall instrs,
      Forall P instrs ->
      Instruction_list_qbits_valid instrs ->
      forall occurrence instrs' status,
        RewriteRule_apply_deep_list_result
          rule (RewriteRule_apply_deep_result rule) instrs occurrence
        = (instrs', status) ->
        match status with
        | RewriteDone =>
            Instruction_equiv nq (SeqInstr instrs) (SeqInstr instrs')
        | RewriteContinue _ =>
            instrs' = instrs
        end).
  {
    induction instrs as [| instr instrs IHtail];
      intros Hforall Hvalid_list occurrence instrs' status Hresult; simpl in *.
    - inversion Hresult; subst.
      reflexivity.
    - inversion Hforall as [| ? ? Hcurrent_sound Htail_sound]; subst.
      inversion Hvalid_list as [| ? ? Hinstr_valid Htail_valid]; subst.
      pose proof (Hcurrent_sound Hinstr_valid) as IHHvalid.
      pose proof (IHtail Htail_sound Htail_valid) as IHHvalid0.
      destruct
        (RewriteRule_apply rule (instr :: instrs))
        as [result |] eqn:Happly.
      + destruct occurrence.
        * inversion Hresult; subst.
          eapply Hrule; eauto.
        * destruct instr
            as [| theta phi lambda target
               | control target
               | qbit1 qbit2
               | qbit cbit
               | seq_instrs
               | cbit expected body
               | target].
          all: try solve [
            solve_rewrite_apply_deep_list_atomic
              rule instrs occurrence Hresult IHHvalid0
          ].
          all: solve_rewrite_apply_deep_list_structured
            rule instrs Hresult IHHvalid IHHvalid0.
      + solve_rewrite_apply_deep_list_structured
          rule instrs Hresult IHHvalid IHHvalid0.
  }
  assert (instr_sound : forall instr, P instr).
  {
    induction instr using Instruction_ind';
      intros Hvalid occurrence instr' status Hresult; simpl in *.
    all: try solve [
      eapply RewriteRule_apply_deep_single_result_sound; eauto;
      inversion Hvalid; constructor; eauto
    ].
    - inversion Hvalid as [| | | | | ? Hlist_valid | |]; subst.
      destruct
        (RewriteRule_apply_deep_list_result
          rule (RewriteRule_apply_deep_result rule) is occurrence)
        as [instrs' status'] eqn:Hlist.
      inversion Hresult; subst.
      specialize (list_sound is H Hlist_valid occurrence instrs' status Hlist)
        as Hlist_sound.
      destruct status; subst.
      + exact Hlist_sound.
      + reflexivity.
    - inversion Hvalid as [| | | | | | ? ? ? Hbody_valid |]; subst.
      destruct
        (RewriteRule_apply_deep_result rule instr occurrence)
        as [body' status'] eqn:Hbody.
      inversion Hresult; subst.
      specialize (IHinstr Hbody_valid occurrence body' status Hbody)
        as Hbody_sound.
      destruct status; subst.
      + apply Instruction_if_Proper.
        exact Hbody_sound.
      + reflexivity.
  }
  exact instr_sound.
Qed.

Theorem TransformSpec_apply_result_equiv :
  forall nc spec param instr occurrence instr',
    TransformSpecValid spec ->
    Instruction_qbits_validb instr = true ->
    TransformSpec_apply spec param instr occurrence = Some instr' ->
    Instruction_result_equiv nq nc instr instr'.
Proof.
  intros nc spec param instr occurrence instr' Hspec Hvalidb Happly.
  rewrite Instruction_qbits_validb_spec in Hvalidb.
  unfold TransformSpec_apply in Happly.
  destruct (transform_rule spec param) as [rule |] eqn:Hrule;
    try discriminate.
  destruct (transform_strategy spec) eqn:Hstrategy.
  - destruct
      (RewriteRule_apply_top_level_result
        rule (transform_postprocess spec param) instr occurrence)
      as [applied status] eqn:Hresult.
    destruct status; try discriminate.
    inversion Happly; subst.
    apply Instruction_behavioral_equiv_implies_result_equiv.
    pose proof
      (RewriteRule_apply_top_level_result_sound
        spec param rule
        (TransformSpec_rule_valid spec param Hstrategy Hspec)
        Hrule instr Hvalidb occurrence instr' RewriteDone Hresult)
      as Hsound.
    exact Hsound.
  - destruct
      (RewriteRule_apply_deep_result rule instr occurrence)
      as [applied status] eqn:Hresult.
    destruct status; try discriminate.
    inversion Happly; subst.
    apply Instruction_behavioral_equiv_implies_result_equiv.
    apply Instruction_equiv_implies_behavioral_equiv.
    pose proof
      (RewriteRule_apply_deep_result_sound
        spec param rule Hrule
        (TransformSpec_rule_equiv_valid spec param Hstrategy Hspec)
        instr Hvalidb occurrence instr' RewriteDone Hresult)
      as Hsound.
    exact Hsound.
Qed.

Lemma PatternRuleValid_id_from_equiv :
  forall spec param,
    (forall instr, transform_postprocess spec param instr = instr) ->
    (forall rule,
      transform_rule spec param = Some rule ->
      forall subst lhs rhs,
        InstructionPattern_inst_list (rule_lhs rule) subst = Some lhs ->
        InstructionPattern_inst_list (rule_rhs rule) subst = Some rhs ->
        Instruction_list_qbits_valid lhs ->
        Instruction_equiv nq
          (SeqInstr lhs)
          (SeqInstr rhs)) ->
    PatternRuleValid spec param.
Proof.
  intros spec param Hpost Hrule.
  unfold PatternRuleValid.
  intros rule Hrule_find.
  intros subst lhs rhs suffix Hlhs Hrhs Hvalid.
  assert (Hmap :
    List.map (transform_postprocess spec param) suffix = suffix).
  {
    clear Hrule Hlhs Hrhs Hvalid.
    induction suffix as [| instr suffix IHsuffix]; simpl.
    - reflexivity.
    - rewrite Hpost.
      rewrite IHsuffix.
      reflexivity.
  }
  rewrite Hmap.
  apply Instruction_equiv_implies_behavioral_equiv.
  destruct (Instruction_list_qbits_valid_app_inv lhs suffix Hvalid)
    as [Hlhs_valid _].
  repeat rewrite Instruction_equiv_Seq_list_list_eq.
  apply Instruction_equiv_rewrite_start.
  eapply Hrule; eauto.
Qed.

End PATTERN.

Section TRANSFORM_FUNCTIONS.

Variable nq: nat.

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
    param_count := 0;
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
    param_count := 1;
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
    param_count := 2;
  |}.

Definition Transform_spec_list : list TransformSpec :=
  [
    TransformSpec_Insert_I;
    TransformSpec_Insert_Swap
  ].

Lemma TransformSpec_Insert_I_valid :
  TransformSpecValid nq TransformSpec_Insert_I.
Proof.
  unfold TransformSpecValid, TransformSpec_Insert_I.
  simpl.
  intros param.
  destruct param as [| qbit | qbit1 qbit2]; simpl.
  all: try (intros rule Hrule; discriminate).
  destruct (qbit <? nq) eqn:Hqbit; simpl.
  - intros rule Hrule subst lhs rhs Hlhs Hrhs _.
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
  destruct param as [| qbit | qbit1 qbit2]; simpl.
  all: try (intros rule Hrule; discriminate).
  destruct ((qbit1 <? nq) && (qbit2 <? nq)) eqn:Hqbits; simpl.
  - intros rule Hrule subst lhs rhs suffix Hlhs Hrhs Hvalid.
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

Theorem Transform_spec_list_valid :
  Forall (TransformSpecValid nq) Transform_spec_list.
Proof.
  repeat constructor.
  - apply TransformSpec_Insert_I_valid.
  - apply TransformSpec_Insert_Swap_valid.
Qed.

End TRANSFORM_FUNCTIONS.
