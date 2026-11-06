Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.All.

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
Module NatMapProperties := WProperties_fun NatMap.E NatMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Import List.ListNotations.
Open Scope list_scope.

Section PATTERN.

Fixpoint Instruction_eqb (instr1 instr2 : Instruction) {struct instr1} : bool :=
  match instr1, instr2 with
  | NopInstr, NopInstr =>
      true
  | RotateInstr theta1 phi1 lambda1 qbit1,
    RotateInstr theta2 phi2 lambda2 qbit2 =>
      Angle_eqb theta1 theta2
      && Angle_eqb phi1 phi2
      && Angle_eqb lambda1 lambda2
      && Nat.eqb qbit1 qbit2
  | CnotInstr control1 target1,
    CnotInstr control2 target2 =>
      Nat.eqb control1 control2 && Nat.eqb target1 target2
  | SwapInstr qbit1 qbit2,
    SwapInstr qbit1' qbit2' =>
      Nat.eqb qbit1 qbit1' && Nat.eqb qbit2 qbit2'
  | MeasureInstr qbit1 cbit1,
    MeasureInstr qbit2 cbit2 =>
      Nat.eqb qbit1 qbit2 && Nat.eqb cbit1 cbit2
  | SeqInstr instrs1,
    SeqInstr instrs2 =>
      let fix list_eqb
          (instrs1 instrs2 : list Instruction)
          {struct instrs1}
          : bool :=
        match instrs1, instrs2 with
        | [], [] =>
            true
        | instr1 :: rest1, instr2 :: rest2 =>
            Instruction_eqb instr1 instr2 && list_eqb rest1 rest2
        | _, _ =>
            false
        end
      in
      list_eqb instrs1 instrs2
  | IfInstr cbit1 expected1 body1,
    IfInstr cbit2 expected2 body2 =>
      Nat.eqb cbit1 cbit2
      && Bool.eqb expected1 expected2
      && Instruction_eqb body1 body2
  | ResetInstr qbit1,
    ResetInstr qbit2 =>
      Nat.eqb qbit1 qbit2
  | _, _ =>
      false
  end.

Record PatternMap : Type := {
  pattern_qbit_map : NatMap.t nat;
  pattern_cbit_map : NatMap.t nat;
  pattern_instr_map : NatMap.t Instruction
}.

Definition PatternMap_empty : PatternMap :=
  {|
    pattern_qbit_map := NatMap.empty _;
    pattern_cbit_map := NatMap.empty _;
    pattern_instr_map := NatMap.empty _
  |}.

Definition NatMap_values_distinct (map : NatMap.t nat) : Prop :=
  forall key1 key2 value,
    NatMap.find key1 map = Some value ->
    NatMap.find key2 map = Some value ->
    key1 = key2.

Definition PatternMap_distinct (map : PatternMap) : Prop :=
  NatMap_values_distinct (pattern_qbit_map map)
  /\
  NatMap_values_distinct (pattern_cbit_map map).

Definition NatMap_value_existsb (value : nat) (map : NatMap.t nat)
    : bool :=
  NatMap.fold
    (fun _ found_value acc =>
      Nat.eqb found_value value || acc)
    map
    false.

Definition NatMap_bind_distinct
    (variable value : nat)
    (map : NatMap.t nat)
    : option (NatMap.t nat) :=
  match NatMap.find variable map with
  | None =>
      if NatMap_value_existsb value map
      then None
      else Some (NatMap.add variable value map)
  | Some old_value =>
      if Nat.eqb old_value value
      then Some map
      else None
  end.

Definition PatternMap_bind_qbit (variable value : nat) (map : PatternMap)
    : option PatternMap :=
  match NatMap_bind_distinct variable value (pattern_qbit_map map) with
  | Some qbit_map =>
      Some
        {|
          pattern_qbit_map := qbit_map;
          pattern_cbit_map := pattern_cbit_map map;
          pattern_instr_map :=
            pattern_instr_map map
        |}
  | None => None
  end.

Definition PatternMap_bind_cbit (variable value : nat) (map : PatternMap)
    : option PatternMap :=
  match NatMap_bind_distinct variable value (pattern_cbit_map map) with
  | Some cbit_map =>
      Some
        {|
          pattern_qbit_map := pattern_qbit_map map;
          pattern_cbit_map := cbit_map;
          pattern_instr_map :=
            pattern_instr_map map
        |}
  | None => None
  end.

Definition PatternMap_bind_instr
    (variable : nat)
    (instr : Instruction)
    (map : PatternMap)
    : option PatternMap :=
  match NatMap.find variable (pattern_instr_map map) with
  | None =>
      Some
        {|
          pattern_qbit_map :=
            pattern_qbit_map map;
          pattern_cbit_map :=
            pattern_cbit_map map;
          pattern_instr_map :=
            NatMap.add variable instr (pattern_instr_map map)
        |}
  | Some old_instr =>
      if Instruction_eqb old_instr instr
      then Some map
      else None
  end.

Definition PatternMap_extends
    (map1 map2 : PatternMap)
    : Prop :=
  (forall variable value,
    NatMap.find variable (pattern_qbit_map map1) = Some value ->
    NatMap.find variable (pattern_qbit_map map2) = Some value)
  /\
  (forall variable value,
    NatMap.find variable (pattern_cbit_map map1) = Some value ->
    NatMap.find variable (pattern_cbit_map map2) = Some value)
  /\
  (forall variable instr,
    NatMap.find variable (pattern_instr_map map1) = Some instr ->
    NatMap.find variable (pattern_instr_map map2) = Some instr).

Inductive NatPattern: Type :=
  | NatExact: nat -> NatPattern
  | NatVar: nat -> NatPattern.

Definition QbitPattern_match (pattern : NatPattern) (value : nat) (map : PatternMap)
    : option PatternMap :=
  match pattern with
  | NatExact expected =>
      if Nat.eqb expected value
      then Some map
      else None
  | NatVar variable =>
      PatternMap_bind_qbit variable value map
  end.

Definition CbitPattern_match (pattern : NatPattern) (value : nat) (map : PatternMap)
    : option PatternMap :=
  match pattern with
  | NatExact expected =>
      if Nat.eqb expected value
      then Some map
      else None
  | NatVar variable =>
      PatternMap_bind_cbit variable value map
  end.

Definition QbitPattern_inst
    (pattern : NatPattern)
    (subst : PatternMap)
    : option nat :=
  match pattern with
  | NatExact value => Some value
  | NatVar variable =>
      NatMap.find variable (pattern_qbit_map subst)
  end.

Definition CbitPattern_inst
    (pattern : NatPattern)
    (subst : PatternMap)
    : option nat :=
  match pattern with
  | NatExact value => Some value
  | NatVar variable =>
      NatMap.find variable (pattern_cbit_map subst)
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

Definition InstructionPattern_body_view
    (instr : Instruction)
    : list Instruction :=
  match instr with
  | NopInstr =>
      []
  | SeqInstr instrs =>
      instrs
  | _ =>
      [instr]
  end.

Fixpoint InstructionPattern_canonicalize
    (instr : Instruction)
    : Instruction :=
  match instr with
  | SeqInstr instrs =>
      SeqInstr
        (fold_right
          (fun instr acc =>
            InstructionPattern_canonicalize instr :: acc)
          []
          instrs)
  | IfInstr cbit expected NopInstr =>
      IfInstr cbit expected NopInstr
  | IfInstr cbit expected (SeqInstr instrs) =>
      IfInstr
        cbit
        expected
        (Instruction_list_simp
          (fold_right
            (fun instr acc =>
              InstructionPattern_canonicalize instr :: acc)
            []
            instrs))
  | IfInstr cbit expected body =>
      IfInstr
        cbit
        expected
        (InstructionPattern_canonicalize body)
  | _ =>
      instr
  end.

Inductive InstructionPattern: Type :=
  | PNop: InstructionPattern
  | PRotate: Angle -> Angle -> Angle -> NatPattern -> InstructionPattern 
  | PCnot: NatPattern -> NatPattern -> InstructionPattern 
  | PSwap: NatPattern -> NatPattern -> InstructionPattern 
  | PMeasure: NatPattern -> NatPattern -> InstructionPattern 
  | PReset: NatPattern -> InstructionPattern
  | PIf: NatPattern -> bool -> list InstructionPattern -> InstructionPattern
  | PInstrVar: nat -> InstructionPattern
  | PInstrExact: Instruction -> InstructionPattern.

Lemma InstructionPattern_ind' :
  forall (P : InstructionPattern -> Prop),
    P PNop ->
    (forall theta phi lambda qbit, P (PRotate theta phi lambda qbit)) ->
    (forall control target, P (PCnot control target)) ->
    (forall qbit1 qbit2, P (PSwap qbit1 qbit2)) ->
    (forall qbit cbit, P (PMeasure qbit cbit)) ->
    (forall qbit, P (PReset qbit)) ->
    (forall cbit expected body_patterns,
      Forall P body_patterns ->
      P (PIf cbit expected body_patterns)) ->
    (forall variable, P (PInstrVar variable)) ->
    (forall instr, P (PInstrExact instr)) ->
    forall pattern, P pattern.
Proof.
  intros P Hnop Hrotate Hcnot Hswap Hmeasure Hreset Hif Hinstr_var Hinstr_exact.
  fix IH 1.
  intro pattern.
  destruct pattern.
  - exact Hnop.
  - apply Hrotate.
  - apply Hcnot.
  - apply Hswap.
  - apply Hmeasure.
  - apply Hreset.
  - apply Hif.
    induction l as [| pattern patterns IHpatterns].
    + constructor.
    + constructor.
      * apply IH.
      * apply IHpatterns.
  - apply Hinstr_var.
  - apply Hinstr_exact.
Qed.

Fixpoint InstructionPattern_match
    (pattern : InstructionPattern)
    (instr : Instruction)
    (map : PatternMap)
    {struct pattern}
    : option PatternMap :=
  match pattern, instr with
  | PNop, NopInstr => Some map
  | PRotate theta' phi' lambda' qbit_pattern,
    RotateInstr theta phi lambda qbit =>
      if Angle_eqb theta theta'
         && Angle_eqb phi phi'
         && Angle_eqb lambda lambda'
      then QbitPattern_match qbit_pattern qbit map
      else None
  | PCnot control_pattern target_pattern,
    CnotInstr control target =>
      let* map' := QbitPattern_match control_pattern control map in
      QbitPattern_match target_pattern target map'
  | PSwap qbit1_pattern qbit2_pattern,
    SwapInstr qbit1 qbit2 =>
      let* map' := QbitPattern_match qbit1_pattern qbit1 map in
      QbitPattern_match qbit2_pattern qbit2 map'
  | PMeasure qbit_pattern cbit_pattern,
    MeasureInstr qbit cbit =>
      let* map' := QbitPattern_match qbit_pattern qbit map in
      CbitPattern_match cbit_pattern cbit map'
  | PReset qbit_pattern,
    ResetInstr qbit =>
      QbitPattern_match qbit_pattern qbit map
  | PIf cbit_pattern expected_pattern body_patterns,
    IfInstr cbit expected body =>
      if Bool.eqb expected_pattern expected
      then
        let* map' := CbitPattern_match cbit_pattern cbit map in
        let fix match_exact_list
            (patterns : list InstructionPattern)
            (instrs : list Instruction)
            (map : PatternMap)
            {struct patterns}
            : option PatternMap :=
          match patterns, instrs with
          | [], [] =>
              Some map
          | pattern :: pattern_rest, instr :: instr_rest =>
              let* map' := InstructionPattern_match pattern instr map in
              match_exact_list pattern_rest instr_rest map'
          | _, _ =>
              None
          end
        in
        match_exact_list
          body_patterns
          (InstructionPattern_body_view body)
          map'
      else None
  | PInstrVar variable, _ =>
      PatternMap_bind_instr
        variable
        (InstructionPattern_canonicalize instr)
        map
  | PInstrExact expected_instr, _ =>
      if Instruction_eqb expected_instr (InstructionPattern_canonicalize instr)
      then Some map
      else None
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

Fixpoint InstructionPattern_inst
    (pattern : InstructionPattern)
    (map : PatternMap)
    {struct pattern}
    : option Instruction :=
  match pattern with
  | PNop => Some NopInstr
  | PRotate theta phi lambda qbit_pattern =>
      let* qbit := QbitPattern_inst qbit_pattern map in
      Some (RotateInstr theta phi lambda qbit)
  | PCnot control_pattern target_pattern =>
      let* control := QbitPattern_inst control_pattern map in
      let* target := QbitPattern_inst target_pattern map in
      Some (CnotInstr control target)
  | PSwap qbit1_pattern qbit2_pattern =>
      let* qbit1 := QbitPattern_inst qbit1_pattern map in
      let* qbit2 := QbitPattern_inst qbit2_pattern map in
      Some (SwapInstr qbit1 qbit2)
  | PMeasure qbit_pattern cbit_pattern =>
      let* qbit := QbitPattern_inst qbit_pattern map in
      let* cbit := CbitPattern_inst cbit_pattern map in
      Some (MeasureInstr qbit cbit)
  | PReset qbit_pattern =>
      let* qbit := QbitPattern_inst qbit_pattern map in
      Some (ResetInstr qbit)
  | PIf cbit_pattern expected body_patterns =>
      let* cbit := CbitPattern_inst cbit_pattern map in
      let* body_instrs :=
        fold_right
          (fun pattern instrs =>
            let* instr := InstructionPattern_inst pattern map in
            let* instrs := instrs in
            Some (instr :: instrs)
          )
          (Some [])
          body_patterns
      in
      Some (IfInstr cbit expected (Instruction_list_simp body_instrs))
  | PInstrVar variable =>
      NatMap.find variable (pattern_instr_map map)
  | PInstrExact instr =>
      Some instr
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

Definition NatPattern_vars (pattern : NatPattern) : list nat :=
  match pattern with
  | NatExact _ => []
  | NatVar variable => [variable]
  end.

Fixpoint InstructionPattern_qbit_vars
    (pattern : InstructionPattern)
    {struct pattern}
    : list nat :=
  match pattern with
  | PNop =>
      []
  | PRotate _ _ _ qbit =>
      NatPattern_vars qbit
  | PCnot control target =>
      NatPattern_vars control ++ NatPattern_vars target
  | PSwap qbit1 qbit2 =>
      NatPattern_vars qbit1 ++ NatPattern_vars qbit2
  | PMeasure qbit _ =>
      NatPattern_vars qbit
  | PReset qbit =>
      NatPattern_vars qbit
  | PIf _ _ body =>
      List.concat (map InstructionPattern_qbit_vars body)
  | PInstrVar _ =>
      []
  | PInstrExact _ =>
      []
  end.

Fixpoint InstructionPattern_cbit_vars
    (pattern : InstructionPattern)
    {struct pattern}
    : list nat :=
  match pattern with
  | PNop =>
      []
  | PRotate _ _ _ _ =>
      []
  | PCnot _ _ =>
      []
  | PSwap _ _ =>
      []
  | PMeasure _ cbit =>
      NatPattern_vars cbit
  | PReset _ =>
      []
  | PIf cbit _ body =>
      NatPattern_vars cbit
      ++ List.concat (map InstructionPattern_cbit_vars body)
  | PInstrVar _ =>
      []
  | PInstrExact _ =>
      []
  end.

Fixpoint InstructionPattern_instr_vars
    (pattern : InstructionPattern)
    {struct pattern}
    : list nat :=
  match pattern with
  | PNop =>
      []
  | PRotate _ _ _ _ =>
      []
  | PCnot _ _ =>
      []
  | PSwap _ _ =>
      []
  | PMeasure _ _ =>
      []
  | PReset _ =>
      []
  | PIf _ _ body =>
      List.concat (map InstructionPattern_instr_vars body)
  | PInstrVar variable =>
      [variable]
  | PInstrExact _ =>
      []
  end.

Definition InstructionPattern_list_qbit_vars
    (patterns : list InstructionPattern)
    : list nat :=
  List.concat (map InstructionPattern_qbit_vars patterns).

Definition InstructionPattern_list_cbit_vars
    (patterns : list InstructionPattern)
    : list nat :=
  List.concat (map InstructionPattern_cbit_vars patterns).

Definition InstructionPattern_list_instr_vars
    (patterns : list InstructionPattern)
    : list nat :=
  List.concat (map InstructionPattern_instr_vars patterns).

Definition list_subset {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Definition RewriteRule_safe (rule : RewriteRule) : Prop :=
  list_subset
    (InstructionPattern_list_qbit_vars (rule_rhs rule))
    (InstructionPattern_list_qbit_vars (rule_lhs rule))
  /\
  list_subset
    (InstructionPattern_list_cbit_vars (rule_rhs rule))
    (InstructionPattern_list_cbit_vars (rule_lhs rule))
  /\
  list_subset
    (InstructionPattern_list_instr_vars (rule_rhs rule))
    (InstructionPattern_list_instr_vars (rule_lhs rule)).

Definition nat_inb (needle : nat) (haystack : list nat) : bool :=
  existsb (Nat.eqb needle) haystack.

Definition list_subsetb (xs ys : list nat) : bool :=
  forallb (fun x => nat_inb x ys) xs.

Definition RewriteRule_safeb (rule : RewriteRule) : bool :=
  list_subsetb
    (InstructionPattern_list_qbit_vars (rule_rhs rule))
    (InstructionPattern_list_qbit_vars (rule_lhs rule))
  &&
  list_subsetb
    (InstructionPattern_list_cbit_vars (rule_rhs rule))
    (InstructionPattern_list_cbit_vars (rule_lhs rule))
  &&
  list_subsetb
    (InstructionPattern_list_instr_vars (rule_rhs rule))
    (InstructionPattern_list_instr_vars (rule_lhs rule)).

Lemma nat_inb_sound :
  forall needle haystack,
    nat_inb needle haystack = true ->
    In needle haystack.
Proof.
  intros needle haystack H.
  unfold nat_inb in H.
  apply existsb_exists in H as [found [Hin Heq]].
  apply Nat.eqb_eq in Heq.
  subst.
  exact Hin.
Qed.

Lemma list_subsetb_sound :
  forall xs ys,
    list_subsetb xs ys = true ->
    list_subset xs ys.
Proof.
  intros xs ys Hsubset.
  unfold list_subsetb in Hsubset.
  unfold list_subset.
  intros x Hin.
  apply forallb_forall with (x := x) in Hsubset.
  - apply nat_inb_sound.
    exact Hsubset.
  - exact Hin.
Qed.

Lemma RewriteRule_safeb_sound :
  forall rule,
    RewriteRule_safeb rule = true ->
    RewriteRule_safe rule.
Proof.
  intros rule Hsafe.
  unfold RewriteRule_safeb in Hsafe.
  repeat rewrite andb_true_iff in Hsafe.
  destruct Hsafe as [[Hqbit Hcbit] Hinstr].
  unfold RewriteRule_safe.
  repeat split;
    apply list_subsetb_sound;
    assumption.
Qed.

Record RewriteResult : Type := {
  RewriteResult_consumed : nat;
  RewriteResult_replacement : list Instruction
}.

(* Apply rule at the first place *)
Definition RewriteRule_apply
    (rule : RewriteRule)
    (instrs : list Instruction)
    : option RewriteResult :=
  if RewriteRule_safeb rule
  then
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
  |}
  else None.

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
               | IfInstr _ _ body =>
                  RewriteRule_match_count rule body
               | _ =>
                   0
               end)
              +
              count_list rest)%nat
          end
      in
      count_list instrs
  | IfInstr _ _ body =>
      (RewriteRule_match_at rule [instr]
       + RewriteRule_match_count rule body)%nat
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
              | SeqInstr _ =>
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
              | IfInstr cbit expected body =>
                  let '(current', current_status) :=
                    rewrite_instr (IfInstr cbit expected body) (S occurrence')
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
              let '(body', status) :=
                RewriteRule_apply_deep_result rule body occurrence'
              in
              (IfInstr cbit expected body', status)
          end
      | None =>
          let '(body', status) :=
            RewriteRule_apply_deep_result rule body occurrence
          in
          (IfInstr cbit expected body', status)
      end
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

End PATTERN.
