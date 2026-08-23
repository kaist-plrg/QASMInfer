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
Module NatMapProperties := WProperties_fun NatMap.E NatMap.

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

Definition InstructionPattern_match_exact_list
    (patterns : list InstructionPattern)
    (instrs : list Instruction)
    (map : PatternMap)
    : option PatternMap :=
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
  match_exact_list patterns instrs map.

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

Example InstructionPattern_match_if_atomic_body :
  InstructionPattern_match
    (PIf (NatExact 0) true [Pat_H (NatExact 1)])
    (IfInstr 0 true (RotateInstr API2 A0 API 1))
    PatternMap_empty =
  Some PatternMap_empty.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_if_singleton_seq_body :
  InstructionPattern_match
    (PIf (NatExact 0) true [Pat_H (NatExact 1)])
    (IfInstr 0 true (SeqInstr [RotateInstr API2 A0 API 1]))
    PatternMap_empty =
  Some PatternMap_empty.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_if_requires_exact_body_length :
  InstructionPattern_match
    (PIf (NatExact 0) true [Pat_H (NatExact 1); Pat_X (NatExact 1)])
    (IfInstr 0 true (SeqInstr [RotateInstr API2 A0 API 1]))
    PatternMap_empty =
  None.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_if_bool_mismatch :
  InstructionPattern_match
    (PIf (NatExact 0) true [Pat_H (NatExact 1)])
    (IfInstr 0 false (RotateInstr API2 A0 API 1))
    PatternMap_empty =
  None.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_cnot_distinct_qbit_reject :
  match
    InstructionPattern_match
      (PCnot (NatVar 0) (NatVar 1))
      (CnotInstr 2 2)
      PatternMap_empty
  with
  | Some _ => true
  | None => false
  end =
  false.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_cnot_same_qbit_variable_accept :
  match
    InstructionPattern_match
      (PCnot (NatVar 0) (NatVar 0))
      (CnotInstr 2 2)
      PatternMap_empty
  with
  | Some _ => true
  | None => false
  end =
  true.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_measure_qbit_cbit_namespace_accept :
  match
    InstructionPattern_match
      (PMeasure (NatVar 0) (NatVar 0))
      (MeasureInstr 2 2)
      PatternMap_empty
  with
  | Some _ => true
  | None => false
  end =
  true.
Proof.
  reflexivity.
Qed.

Example InstructionPattern_match_if_distinct_cbit_reject :
  InstructionPattern_match
    (PIf (NatVar 0) true [PMeasure (NatExact 1) (NatVar 1)])
    (IfInstr 0 true (MeasureInstr 1 0))
    PatternMap_empty =
  None.
Proof.
  reflexivity.
Qed.

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
  | Param_qbit2 : nat -> nat -> TransformParameter
  | Param_cbit_instr : nat -> Instruction -> TransformParameter.

Inductive TransformParamKind : Type :=
  | ParamKind_None : TransformParamKind
  | ParamKind_qbit1 : TransformParamKind
  | ParamKind_qbit2 : TransformParamKind
  | ParamKind_cbit_instr : TransformParamKind.

Inductive TransformStrategy : Type :=
  | TransformTopLevel : TransformStrategy
  | TransformDeep : TransformStrategy.

Record TransformSpec : Type := {
  transform_name : string;
  transform_rule : TransformParameter -> option RewriteRule;
  transform_postprocess : TransformParameter -> Instruction -> Instruction;
  transform_strategy : TransformStrategy;
  transform_param_kind : TransformParamKind;
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

Lemma Instruction_eqb_eq :
  forall instr1 instr2,
    Instruction_eqb instr1 instr2 = true ->
    instr1 = instr2.
Proof.
  induction instr1 as [
    | theta1 phi1 lambda1 qbit1
    | control1 target1
    | qbit1 qbit2
    | qbit1 cbit1
    | instrs1 Hinstrs1
    | cbit1 expected1 body1 Hbody1
    | qbit1
  ] using Instruction_ind';
  intros instr2 Heq;
  destruct instr2 as [
    | theta2 phi2 lambda2 qbit2'
    | control2 target2
    | qbit1' qbit2'
    | measure_qbit2 cbit2
    | instrs2
    | cbit2 expected2 body2
    | reset_qbit2
  ]; simpl in Heq; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Heq as [Hangles Hqbit].
    apply andb_true_iff in Hangles as [Hangles Hlambda].
    apply andb_true_iff in Hangles as [Htheta Hphi].
    apply Angle_eqb_eq in Htheta.
    apply Angle_eqb_eq in Hphi.
    apply Angle_eqb_eq in Hlambda.
    apply Nat.eqb_eq in Hqbit.
    subst.
    reflexivity.
  - apply andb_true_iff in Heq as [Hcontrol Htarget].
    apply Nat.eqb_eq in Hcontrol.
    apply Nat.eqb_eq in Htarget.
    subst.
    reflexivity.
  - apply andb_true_iff in Heq as [Hqbit1 Hqbit2].
    apply Nat.eqb_eq in Hqbit1.
    apply Nat.eqb_eq in Hqbit2.
    subst.
    reflexivity.
  - apply andb_true_iff in Heq as [Hqbit Hcbit].
    apply Nat.eqb_eq in Hqbit.
    apply Nat.eqb_eq in Hcbit.
    subst.
    reflexivity.
  - f_equal.
    revert instrs2 Heq Hinstrs1.
    induction instrs1 as [| instr1 instrs1 IHinstrs1];
    intros instrs2 Heq Hinstrs1;
    destruct instrs2 as [| instr2 instrs2];
    simpl in Heq; try discriminate.
    + reflexivity.
    + apply andb_true_iff in Heq as [Hhead Htail].
      inversion Hinstrs1 as [| ? ? Hhead_ih Htail_ih]; subst.
      f_equal.
      * exact (Hhead_ih instr2 Hhead).
      * apply IHinstrs1.
        -- change (Instruction_eqb (SeqInstr instrs1) (SeqInstr instrs2) = true).
           exact Htail.
        -- exact Htail_ih.
  - apply andb_true_iff in Heq as [Hcond Hbody].
    apply andb_true_iff in Hcond as [Hcbit Hexpected].
    apply Nat.eqb_eq in Hcbit.
    destruct expected1, expected2; simpl in Hexpected; try discriminate;
    apply Hbody1 in Hbody; subst; reflexivity.
  - apply Nat.eqb_eq in Heq.
    subst.
    reflexivity.
Qed.

Lemma PatternMap_extends_refl :
  forall map,
    PatternMap_extends map map.
Proof.
  unfold PatternMap_extends.
  repeat split; auto.
Qed.

Lemma PatternMap_extends_trans :
  forall map1 map2 map3,
    PatternMap_extends map1 map2 ->
    PatternMap_extends map2 map3 ->
    PatternMap_extends map1 map3.
Proof.
  unfold PatternMap_extends.
  intros map1 map2 map3
    [H12_qbit [H12_cbit H12_instr]]
    [H23_qbit [H23_cbit H23_instr]].
  repeat split.
  - intros variable value Hfind.
    apply H23_qbit.
    apply H12_qbit.
    exact Hfind.
  - intros variable value Hfind.
    apply H23_cbit.
    apply H12_cbit.
    exact Hfind.
  - intros variable instr Hfind.
    apply H23_instr.
    apply H12_instr.
    exact Hfind.
Qed.

Lemma PatternMap_empty_distinct :
  PatternMap_distinct PatternMap_empty.
Proof.
  unfold PatternMap_distinct, NatMap_values_distinct, PatternMap_empty.
  simpl.
  split; intros key1 key2 value Hfind1 Hfind2;
    rewrite NatMapFacts.empty_o in Hfind1; discriminate.
Qed.

Lemma NatMap_value_existsb_false_find :
  forall value map key,
    NatMap_value_existsb value map = false ->
    NatMap.find key map = Some value ->
    False.
Proof.
  intros value map key.
  unfold NatMap_value_existsb.
  eapply
    (NatMapProperties.fold_rec_bis
      (elt := nat)
      (A := bool)
      (P := fun map acc =>
        acc = false ->
        NatMap.find key map = Some value ->
        False)).
  - intros m m' acc Heq Hacc Hfold Hfind.
    apply Hacc.
    + exact Hfold.
    + unfold NatMap.Equal in Heq.
      rewrite Heq.
      exact Hfind.
  - intros _ Hfind.
    rewrite NatMapFacts.empty_o in Hfind.
    discriminate.
  - intros k found_value acc m Hmaps Hnotin IH Hfold Hfind.
    destruct (Nat.eq_dec key k) as [Heq | Hneq].
    + subst key.
      rewrite NatMapFacts.add_eq_o in Hfind by reflexivity.
      inversion Hfind; subst found_value.
      simpl in Hfold.
      rewrite Nat.eqb_refl in Hfold.
      discriminate.
    + rewrite NatMapFacts.add_neq_o in Hfind by lia.
      simpl in Hfold.
      apply Bool.orb_false_iff in Hfold as [_ Hacc].
      eapply IH; eauto.
Qed.

Lemma NatMap_bind_distinct_values_distinct :
  forall variable value map map',
    NatMap_values_distinct map ->
    NatMap_bind_distinct variable value map = Some map' ->
    NatMap_values_distinct map'.
Proof.
  intros variable value map map' Hdistinct Hbind.
  unfold NatMap_values_distinct in *.
  unfold NatMap_bind_distinct in Hbind.
  destruct (NatMap.find variable map) as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq; try discriminate.
    inversion Hbind; subst.
    exact Hdistinct.
  - destruct (NatMap_value_existsb value map) eqn:Hexists; try discriminate.
    inversion Hbind; subst.
    intros key1 key2 found_value Hkey1 Hkey2.
    destruct (Nat.eq_dec key1 variable) as [Hkey1_eq | Hkey1_neq];
    destruct (Nat.eq_dec key2 variable) as [Hkey2_eq | Hkey2_neq].
    + subst. reflexivity.
    + subst key1.
      rewrite NatMapFacts.add_eq_o in Hkey1 by reflexivity.
      rewrite NatMapFacts.add_neq_o in Hkey2 by lia.
      inversion Hkey1; subst found_value.
      exfalso.
      eapply NatMap_value_existsb_false_find; eauto.
    + subst key2.
      rewrite NatMapFacts.add_neq_o in Hkey1 by lia.
      rewrite NatMapFacts.add_eq_o in Hkey2 by reflexivity.
      inversion Hkey2; subst found_value.
      exfalso.
      eapply NatMap_value_existsb_false_find; eauto.
    + rewrite NatMapFacts.add_neq_o in Hkey1 by lia.
      rewrite NatMapFacts.add_neq_o in Hkey2 by lia.
      eapply Hdistinct; eauto.
Qed.

Lemma NatMap_bind_distinct_extends :
  forall variable value map map',
    NatMap_bind_distinct variable value map = Some map' ->
    forall key old,
      NatMap.find key map = Some old ->
      NatMap.find key map' = Some old.
Proof.
  intros variable value map map' Hbind key old Hkey.
  unfold NatMap_bind_distinct in Hbind.
  destruct (NatMap.find variable map) as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq; try discriminate.
    inversion Hbind; subst.
    exact Hkey.
  - destruct (NatMap_value_existsb value map); try discriminate.
    inversion Hbind; subst.
    destruct (Nat.eq_dec key variable) as [Heq | Hneq].
    + subst key.
      rewrite Hfind in Hkey.
      discriminate.
    + rewrite NatMapFacts.add_neq_o.
      * exact Hkey.
      * lia.
Qed.

Lemma NatMap_bind_distinct_find :
  forall variable value map map',
    NatMap_bind_distinct variable value map = Some map' ->
    NatMap.find variable map' = Some value.
Proof.
  intros variable value map map' Hbind.
  unfold NatMap_bind_distinct in Hbind.
  destruct (NatMap.find variable map) as [old_value |] eqn:Hfind.
  - destruct (Nat.eqb old_value value) eqn:Heq; try discriminate.
    apply Nat.eqb_eq in Heq.
    inversion Hbind; subst.
    subst.
    exact Hfind.
  - destruct (NatMap_value_existsb value map); try discriminate.
    inversion Hbind; subst.
    apply NatMapFacts.add_eq_o.
    reflexivity.
Qed.

Lemma PatternMap_bind_qbit_extends :
  forall variable value map map',
    PatternMap_bind_qbit variable value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros variable value map map' Hbind.
  unfold PatternMap_bind_qbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_qbit_map map))
    as [qbit_map |] eqn:Hqbit; try discriminate.
  inversion Hbind; subst.
  unfold PatternMap_extends.
  simpl.
  repeat split.
  - eapply NatMap_bind_distinct_extends.
    apply Hqbit.
  - intros key old Hkey.
    exact Hkey.
  - intros key instr Hkey.
    exact Hkey.
Qed.

Lemma PatternMap_bind_qbit_find :
  forall variable value map map',
    PatternMap_bind_qbit variable value map = Some map' ->
    NatMap.find variable (pattern_qbit_map map') = Some value.
Proof.
  intros variable value map map' Hbind.
  unfold PatternMap_bind_qbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_qbit_map map))
    as [qbit_map |] eqn:Hqbit; try discriminate.
  inversion Hbind; subst.
  simpl.
  eapply NatMap_bind_distinct_find.
  apply Hqbit.
Qed.

Lemma PatternMap_bind_cbit_extends :
  forall variable value map map',
    PatternMap_bind_cbit variable value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros variable value map map' Hbind.
  unfold PatternMap_bind_cbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_cbit_map map))
    as [cbit_map |] eqn:Hcbit; try discriminate.
  inversion Hbind; subst.
  unfold PatternMap_extends.
  simpl.
  repeat split.
  - intros key old Hkey.
    exact Hkey.
  - eapply NatMap_bind_distinct_extends.
    apply Hcbit.
  - intros key instr Hkey.
    exact Hkey.
Qed.

Lemma PatternMap_bind_cbit_find :
  forall variable value map map',
    PatternMap_bind_cbit variable value map = Some map' ->
    NatMap.find variable (pattern_cbit_map map') = Some value.
Proof.
  intros variable value map map' Hbind.
  unfold PatternMap_bind_cbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_cbit_map map))
    as [cbit_map |] eqn:Hcbit; try discriminate.
  inversion Hbind; subst.
  simpl.
  eapply NatMap_bind_distinct_find.
  apply Hcbit.
Qed.

Lemma PatternMap_bind_instr_extends :
  forall variable instr map map',
    PatternMap_bind_instr variable instr map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros variable instr map map' Hbind.
  unfold PatternMap_bind_instr in Hbind.
  destruct (NatMap.find variable (pattern_instr_map map))
    as [old_instr |] eqn:Hfind.
  - destruct (Instruction_eqb old_instr instr); try discriminate.
    inversion Hbind; subst.
    apply PatternMap_extends_refl.
  - inversion Hbind; subst.
    unfold PatternMap_extends.
    simpl.
    repeat split.
    + intros key value Hkey.
      exact Hkey.
    + intros key value Hkey.
      exact Hkey.
    + intros key old Hkey.
      destruct (Nat.eq_dec key variable) as [Heq | Hneq].
      * subst key.
        rewrite Hfind in Hkey.
        discriminate.
      * rewrite NatMapFacts.add_neq_o.
        -- exact Hkey.
        -- lia.
Qed.

Definition PatternMap_domain_subset
    (map : PatternMap)
    (qbits cbits instrs : list nat)
    : Prop :=
  (forall variable value,
    NatMap.find variable (pattern_qbit_map map) = Some value ->
    In variable qbits)
  /\
  (forall variable value,
    NatMap.find variable (pattern_cbit_map map) = Some value ->
    In variable cbits)
  /\
  (forall variable instr,
    NatMap.find variable (pattern_instr_map map) = Some instr ->
    In variable instrs).

Lemma PatternMap_empty_domain_subset :
  PatternMap_domain_subset PatternMap_empty [] [] [].
Proof.
  unfold PatternMap_domain_subset, PatternMap_empty.
  simpl.
  repeat split; intros variable value Hfind;
    rewrite NatMapFacts.empty_o in Hfind; discriminate.
Qed.

Lemma PatternMap_domain_subset_weaken :
  forall map q1 c1 i1 q2 c2 i2,
    PatternMap_domain_subset map q1 c1 i1 ->
    list_subset q1 q2 ->
    list_subset c1 c2 ->
    list_subset i1 i2 ->
    PatternMap_domain_subset map q2 c2 i2.
Proof.
  unfold PatternMap_domain_subset, list_subset.
  intros map q1 c1 i1 q2 c2 i2
    [Hq [Hc Hi]] Hqsub Hcsub Hisub.
  repeat split; eauto.
Qed.

Lemma PatternMap_bind_qbit_domain_subset :
  forall variable value map map' qbits cbits instrs,
    PatternMap_domain_subset map qbits cbits instrs ->
    PatternMap_bind_qbit variable value map = Some map' ->
    PatternMap_domain_subset map' (variable :: qbits) cbits instrs.
Proof.
  intros variable value map map' qbits cbits instrs
    [Hq [Hc Hi]] Hbind.
  unfold PatternMap_domain_subset.
  unfold PatternMap_bind_qbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_qbit_map map))
    as [qbit_map |] eqn:Hqbit; try discriminate.
  inversion Hbind; subst; simpl.
  repeat split.
  - intros key old Hfind.
    destruct (Nat.eq_dec key variable) as [Heq | Hneq].
    + subst. simpl. auto.
    + right.
      unfold NatMap_bind_distinct in Hqbit.
      destruct (NatMap.find variable (pattern_qbit_map map)); try
        (destruct (Nat.eqb n value); inversion Hqbit; subst; exact (Hq _ _ Hfind)).
      destruct (NatMap_value_existsb value (pattern_qbit_map map));
        try discriminate.
      inversion Hqbit; subst.
      rewrite NatMapFacts.add_neq_o in Hfind by lia.
      eapply Hq; eauto.
  - intros key old Hfind.
    eapply Hc; eauto.
  - intros key instr Hfind.
    eapply Hi; eauto.
Qed.

Lemma PatternMap_bind_cbit_domain_subset :
  forall variable value map map' qbits cbits instrs,
    PatternMap_domain_subset map qbits cbits instrs ->
    PatternMap_bind_cbit variable value map = Some map' ->
    PatternMap_domain_subset map' qbits (variable :: cbits) instrs.
Proof.
  intros variable value map map' qbits cbits instrs
    [Hq [Hc Hi]] Hbind.
  unfold PatternMap_domain_subset.
  unfold PatternMap_bind_cbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_cbit_map map))
    as [cbit_map |] eqn:Hcbit; try discriminate.
  inversion Hbind; subst; simpl.
  repeat split.
  - intros key old Hfind.
    eapply Hq; eauto.
  - intros key old Hfind.
    destruct (Nat.eq_dec key variable) as [Heq | Hneq].
    + subst. simpl. auto.
    + right.
      unfold NatMap_bind_distinct in Hcbit.
      destruct (NatMap.find variable (pattern_cbit_map map)); try
        (destruct (Nat.eqb n value); inversion Hcbit; subst; exact (Hc _ _ Hfind)).
      destruct (NatMap_value_existsb value (pattern_cbit_map map));
        try discriminate.
      inversion Hcbit; subst.
      rewrite NatMapFacts.add_neq_o in Hfind by lia.
      eapply Hc; eauto.
  - intros key instr Hfind.
    eapply Hi; eauto.
Qed.

Lemma PatternMap_bind_instr_domain_subset :
  forall variable instr map map' qbits cbits instrs,
    PatternMap_domain_subset map qbits cbits instrs ->
    PatternMap_bind_instr variable instr map = Some map' ->
    PatternMap_domain_subset map' qbits cbits (variable :: instrs).
Proof.
  intros variable instr map map' qbits cbits instrs
    [Hq [Hc Hi]] Hbind.
  unfold PatternMap_domain_subset.
  unfold PatternMap_bind_instr in Hbind.
  destruct (NatMap.find variable (pattern_instr_map map))
    as [old_instr |] eqn:Hfind.
  - destruct (Instruction_eqb old_instr instr); try discriminate.
    inversion Hbind; subst.
    repeat split; eauto.
    intros key found Hkey.
    right.
    eapply Hi; eauto.
  - inversion Hbind; subst; simpl.
    repeat split; eauto.
    intros key found Hkey.
    destruct (Nat.eq_dec key variable) as [Heq | Hneq].
    + subst. auto.
    + right.
      rewrite NatMapFacts.add_neq_o in Hkey by lia.
      eapply Hi; eauto.
Qed.

Lemma PatternMap_bind_qbit_distinct :
  forall variable value map map',
    PatternMap_distinct map ->
    PatternMap_bind_qbit variable value map = Some map' ->
    PatternMap_distinct map'.
Proof.
  intros variable value map map' [Hqbit_distinct Hcbit_distinct] Hbind.
  unfold PatternMap_bind_qbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_qbit_map map))
    as [qbit_map |] eqn:Hqbit; try discriminate.
  inversion Hbind; subst.
  simpl.
  split.
  - eapply NatMap_bind_distinct_values_distinct
      with (variable := variable) (value := value)
           (map := pattern_qbit_map map); eauto.
  - exact Hcbit_distinct.
Qed.

Lemma PatternMap_bind_cbit_distinct :
  forall variable value map map',
    PatternMap_distinct map ->
    PatternMap_bind_cbit variable value map = Some map' ->
    PatternMap_distinct map'.
Proof.
  intros variable value map map' [Hqbit_distinct Hcbit_distinct] Hbind.
  unfold PatternMap_bind_cbit in Hbind.
  destruct (NatMap_bind_distinct variable value (pattern_cbit_map map))
    as [cbit_map |] eqn:Hcbit; try discriminate.
  inversion Hbind; subst.
  simpl.
  split.
  - exact Hqbit_distinct.
  - eapply NatMap_bind_distinct_values_distinct
      with (variable := variable) (value := value)
           (map := pattern_cbit_map map); eauto.
Qed.

Lemma PatternMap_bind_instr_distinct :
  forall variable instr map map',
    PatternMap_distinct map ->
    PatternMap_bind_instr variable instr map = Some map' ->
    PatternMap_distinct map'.
Proof.
  intros variable instr map map' Hdistinct Hbind.
  unfold PatternMap_bind_instr in Hbind.
  destruct (NatMap.find variable (pattern_instr_map map)) as [old_instr |]
    eqn:Hfind.
  - destruct (Instruction_eqb old_instr instr); try discriminate.
    inversion Hbind; subst.
    exact Hdistinct.
  - inversion Hbind; subst.
    exact Hdistinct.
Qed.

Lemma PatternMap_bind_instr_find :
  forall variable instr map map',
    PatternMap_bind_instr variable instr map = Some map' ->
    NatMap.find variable (pattern_instr_map map') = Some instr.
Proof.
  intros variable instr map map' Hbind.
  unfold PatternMap_bind_instr in Hbind.
  destruct (NatMap.find variable (pattern_instr_map map))
    as [old_instr |] eqn:Hfind.
  - destruct (Instruction_eqb old_instr instr) eqn:Heq; try discriminate.
    apply Instruction_eqb_eq in Heq.
    inversion Hbind; subst.
    subst.
    exact Hfind.
  - inversion Hbind; subst.
    apply NatMapFacts.add_eq_o.
    reflexivity.
Qed.

Lemma QbitPattern_match_extends :
  forall pattern value map map',
    QbitPattern_match pattern value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern; simpl in *.
  - destruct (Nat.eqb n value); try discriminate.
    inversion Hmatch; subst.
    apply PatternMap_extends_refl.
  - eapply PatternMap_bind_qbit_extends.
    apply Hmatch.
Qed.

Lemma CbitPattern_match_extends :
  forall pattern value map map',
    CbitPattern_match pattern value map = Some map' ->
    PatternMap_extends map map'.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern; simpl in *.
  - destruct (Nat.eqb n value); try discriminate.
    inversion Hmatch; subst.
    apply PatternMap_extends_refl.
  - eapply PatternMap_bind_cbit_extends.
    apply Hmatch.
Qed.

Lemma QbitPattern_match_sound :
  forall pattern value map map',
    QbitPattern_match pattern value map = Some map' ->
    QbitPattern_inst pattern map' = Some value.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern; simpl in *.
  - destruct (Nat.eqb n value) eqn:E; try discriminate.
    f_equal.
    apply Nat.eqb_eq.
    apply E.
  - apply PatternMap_bind_qbit_find in Hmatch.
    exact Hmatch.
Qed.

Lemma CbitPattern_match_sound :
  forall pattern value map map',
    CbitPattern_match pattern value map = Some map' ->
    CbitPattern_inst pattern map' = Some value.
Proof.
  intros pattern value map map' Hmatch.
  destruct pattern; simpl in *.
  - destruct (Nat.eqb n value) eqn:E; try discriminate.
    f_equal.
    apply Nat.eqb_eq.
    apply E.
  - apply PatternMap_bind_cbit_find in Hmatch.
    exact Hmatch.
Qed.

Lemma QbitPattern_inst_extends :
  forall pattern map1 map2 value,
    PatternMap_extends map1 map2 ->
    QbitPattern_inst pattern map1 = Some value ->
    QbitPattern_inst pattern map2 = Some value.
Proof.
  intros pattern map1 map2 value Hextends Hinst.
  destruct pattern; simpl in *.
  - apply Hinst.
  - apply (proj1 Hextends).
    apply Hinst.
Qed.

Lemma CbitPattern_inst_extends :
  forall pattern map1 map2 value,
    PatternMap_extends map1 map2 ->
    CbitPattern_inst pattern map1 = Some value ->
    CbitPattern_inst pattern map2 = Some value.
Proof.
  intros pattern map1 map2 value Hextends Hinst.
  destruct pattern; simpl in *.
  - apply Hinst.
  - apply (proj1 (proj2 Hextends)).
    apply Hinst.
Qed.

Lemma InstructionPattern_inst_extends :
  forall pattern map1 map2 instr,
    PatternMap_extends map1 map2 ->
    InstructionPattern_inst pattern map1 = Some instr ->
    InstructionPattern_inst pattern map2 = Some instr.
Proof.
  induction pattern as [
    | theta phi lambda qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern
    | cbit_pattern expected body_patterns Hbody_patterns
    | instr_variable
    | exact_instr
  ] using InstructionPattern_ind';
  intros map1 map2 instr Hextends Hinst; simpl in *.
  - assumption.
  - destruct (QbitPattern_inst qbit_pattern map1) as [qbit |] eqn:Hqbit; try discriminate.
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := qbit).
    all: assumption.
  - destruct (QbitPattern_inst control_pattern map1) as [control |] eqn:Hcontrol; try discriminate.
    destruct (QbitPattern_inst target_pattern map1) as [target |] eqn:Htarget; try discriminate.
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := control).
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := target).
    all: assumption.
  - destruct (QbitPattern_inst qbit1_pattern map1) as [qbit1 |] eqn:Hqbit1; try discriminate.
    destruct (QbitPattern_inst qbit2_pattern map1) as [qbit2 |] eqn:Hqbit2; try discriminate.
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := qbit1).
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := qbit2).
    all: assumption.
  - destruct (QbitPattern_inst qbit_pattern map1) as [qbit |] eqn:Hqbit; try discriminate.
    destruct (CbitPattern_inst cbit_pattern map1) as [cbit |] eqn:Hcbit; try discriminate.
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := qbit).
    rewrite CbitPattern_inst_extends with (map1 := map1) (value := cbit).
    all: assumption.
  - destruct (QbitPattern_inst qbit_pattern map1) as [qbit |] eqn:Hqbit; try discriminate.
    rewrite QbitPattern_inst_extends with (map1 := map1) (value := qbit).
    all: assumption.
  - destruct (CbitPattern_inst cbit_pattern map1) as [cbit_value |] eqn:Hcbit;
    try discriminate.
    destruct
      (fold_right
        (fun pattern instrs =>
          let* instr := InstructionPattern_inst pattern map1 in
          let* instrs := instrs in
          Some (instr :: instrs))
        (Some [])
        body_patterns)
      as [body_instrs |] eqn:Hbody; try discriminate.
    inversion Hinst; subst; clear Hinst.
    erewrite CbitPattern_inst_extends with
      (map1 := map1) (value := cbit_value); try eassumption.
    replace
      (fold_right
        (fun pattern instrs =>
          let* instr := InstructionPattern_inst pattern map2 in
          let* instrs := instrs in
          Some (instr :: instrs))
        (Some [])
        body_patterns)
      with (Some body_instrs).
    + reflexivity.
    + symmetry.
      revert body_instrs Hbody Hbody_patterns.
      induction body_patterns as [| pattern patterns IHpatterns];
      intros body_instrs Hbody Hforall; simpl in *.
      * exact Hbody.
      * inversion Hforall as [| ? ? Hhead_extends Htail_extends]; subst.
        destruct (InstructionPattern_inst pattern map1)
          as [body_instr |] eqn:Hbody_instr; try discriminate.
        destruct
          (fold_right
            (fun pattern instrs =>
              let* instr := InstructionPattern_inst pattern map1 in
              let* instrs := instrs in
              Some (instr :: instrs))
            (Some [])
            patterns)
          as [body_instrs' |] eqn:Hbody_instrs; try discriminate.
        inversion Hbody; subst.
        rewrite (Hhead_extends map1 map2 body_instr Hextends Hbody_instr).
        rewrite (IHpatterns body_instrs' eq_refl Htail_extends).
        reflexivity.
  - destruct (NatMap.find instr_variable (pattern_instr_map map1))
      as [found_instr |] eqn:Hfound; try discriminate.
    inversion Hinst; subst; clear Hinst.
    apply (proj2 (proj2 Hextends)) in Hfound.
    rewrite Hfound.
    reflexivity.
  - exact Hinst.
Qed.

Lemma InstructionPattern_match_extends :
  forall pattern instr map map',
    InstructionPattern_match pattern instr map = Some map' ->
    PatternMap_extends map map'.
Proof.
  induction pattern as [
    | theta' phi' lambda' qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern
    | cbit_pattern expected_pattern body_patterns Hbody_patterns
    | instr_variable
    | exact_instr
  ] using InstructionPattern_ind';
  intros instr map map' Hmatch.
  - destruct instr; simpl in Hmatch; try discriminate.
    inversion Hmatch; subst.
    apply PatternMap_extends_refl.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (Angle_eqb theta theta');
    destruct (Angle_eqb phi phi');
    destruct (Angle_eqb lambda lambda'); try discriminate.
    eapply QbitPattern_match_extends.
    apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match control_pattern control map)
      as [map_control |] eqn:Hcontrol; try discriminate.
    apply PatternMap_extends_trans with map_control.
    + eapply QbitPattern_match_extends.
      apply Hcontrol.
    + eapply QbitPattern_match_extends.
      apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match qbit1_pattern qbit1 map)
      as [map_qbit1 |] eqn:Hqbit1; try discriminate.
    apply PatternMap_extends_trans with map_qbit1.
    + eapply QbitPattern_match_extends.
      apply Hqbit1.
    + eapply QbitPattern_match_extends.
      apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match qbit_pattern qbit map)
      as [map_qbit |] eqn:Hqbit; try discriminate.
    apply PatternMap_extends_trans with map_qbit.
    + eapply QbitPattern_match_extends.
      apply Hqbit.
    + eapply CbitPattern_match_extends.
      apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    eapply QbitPattern_match_extends.
    apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (Bool.eqb expected_pattern expected); try discriminate.
    destruct (CbitPattern_match cbit_pattern cbit map)
      as [map_cbit |] eqn:Hcbit; try discriminate.
    apply PatternMap_extends_trans with map_cbit.
    + eapply CbitPattern_match_extends.
      apply Hcbit.
    + clear Hcbit.
      revert map_cbit map' Hmatch Hbody_patterns.
      generalize (InstructionPattern_body_view body) as body_instrs.
      induction body_patterns as [| pattern patterns IHpatterns];
      intros body_instrs map_body map' Hmatch Hforall;
      destruct body_instrs as [| instr instrs];
      simpl in Hmatch; try discriminate.
      * inversion Hmatch; subst.
        apply PatternMap_extends_refl.
      * inversion Hforall as [| ? ? Hhead_extends Htail_extends]; subst.
        destruct (InstructionPattern_match pattern instr map_body)
          as [map_head |] eqn:Hhead; try discriminate.
        apply PatternMap_extends_trans with map_head.
        -- eapply Hhead_extends.
           apply Hhead.
        -- eapply IHpatterns; eauto.
  - simpl in Hmatch.
    eapply PatternMap_bind_instr_extends.
    apply Hmatch.
  - simpl in Hmatch.
    destruct (Instruction_eqb exact_instr (InstructionPattern_canonicalize instr));
    try discriminate.
    inversion Hmatch; subst.
    apply PatternMap_extends_refl.
Qed.

Lemma QbitPattern_match_distinct :
  forall pattern value map map',
    PatternMap_distinct map ->
    QbitPattern_match pattern value map = Some map' ->
    PatternMap_distinct map'.
Proof.
  intros pattern value map map' Hdistinct Hmatch.
  destruct pattern; simpl in Hmatch.
  - destruct (Nat.eqb n value); try discriminate.
    inversion Hmatch; subst.
    exact Hdistinct.
  - eapply PatternMap_bind_qbit_distinct; eauto.
Qed.

Lemma CbitPattern_match_distinct :
  forall pattern value map map',
    PatternMap_distinct map ->
    CbitPattern_match pattern value map = Some map' ->
    PatternMap_distinct map'.
Proof.
  intros pattern value map map' Hdistinct Hmatch.
  destruct pattern; simpl in Hmatch.
  - destruct (Nat.eqb n value); try discriminate.
    inversion Hmatch; subst.
    exact Hdistinct.
  - eapply PatternMap_bind_cbit_distinct; eauto.
Qed.

Lemma InstructionPattern_match_distinct :
  forall pattern instr map map',
    PatternMap_distinct map ->
    InstructionPattern_match pattern instr map = Some map' ->
    PatternMap_distinct map'.
Proof.
  induction pattern as [
    | theta' phi' lambda' qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern
    | cbit_pattern expected_pattern body_patterns Hbody_patterns
    | instr_variable
    | exact_instr
  ] using InstructionPattern_ind';
  intros instr map map' Hdistinct Hmatch.
  - destruct instr; simpl in Hmatch; try discriminate.
    inversion Hmatch; subst.
    exact Hdistinct.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (Angle_eqb theta theta');
    destruct (Angle_eqb phi phi');
    destruct (Angle_eqb lambda lambda'); try discriminate.
    eapply QbitPattern_match_distinct
      with (pattern := qbit_pattern) (value := qbit) (map := map);
      eauto.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match control_pattern control map)
      as [map_control |] eqn:Hcontrol; try discriminate.
    eapply QbitPattern_match_distinct
      with (pattern := target_pattern) (value := target)
           (map := map_control); eauto.
    eapply QbitPattern_match_distinct
      with (pattern := control_pattern) (value := control) (map := map);
      eauto.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match qbit1_pattern qbit1 map)
      as [map_qbit1 |] eqn:Hqbit1; try discriminate.
    eapply QbitPattern_match_distinct
      with (pattern := qbit2_pattern) (value := qbit2)
           (map := map_qbit1); eauto.
    eapply QbitPattern_match_distinct
      with (pattern := qbit1_pattern) (value := qbit1) (map := map);
      eauto.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match qbit_pattern qbit map)
      as [map_qbit |] eqn:Hqbit; try discriminate.
    eapply CbitPattern_match_distinct
      with (pattern := cbit_pattern) (value := cbit)
           (map := map_qbit); eauto.
    eapply QbitPattern_match_distinct
      with (pattern := qbit_pattern) (value := qbit) (map := map);
      eauto.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    eapply QbitPattern_match_distinct
      with (pattern := qbit_pattern) (value := qbit) (map := map);
      eauto.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (Bool.eqb expected_pattern expected); try discriminate.
    destruct (CbitPattern_match cbit_pattern cbit map)
      as [map_cbit |] eqn:Hcbit; try discriminate.
    assert (Hmap_cbit_distinct : PatternMap_distinct map_cbit).
    {
      eapply CbitPattern_match_distinct; eauto.
    }
    clear Hcbit.
    revert map_cbit map' Hmap_cbit_distinct Hmatch Hbody_patterns.
    generalize (InstructionPattern_body_view body) as body_instrs.
    induction body_patterns as [| pattern patterns IHpatterns];
    intros body_instrs map_body map' Hmap_body_distinct Hmatch Hforall;
    destruct body_instrs as [| instr instrs];
    simpl in Hmatch; try discriminate.
    + inversion Hmatch; subst.
      exact Hmap_body_distinct.
    + inversion Hforall as [| ? ? Hhead_distinct Htail_distinct]; subst.
      destruct (InstructionPattern_match pattern instr map_body)
        as [map_head |] eqn:Hhead; try discriminate.
      eapply IHpatterns
        with (body_instrs := instrs) (map_cbit := map_head);
        eauto.
  - simpl in Hmatch.
    eapply PatternMap_bind_instr_distinct; eauto.
  - simpl in Hmatch.
    destruct (Instruction_eqb exact_instr (InstructionPattern_canonicalize instr));
    try discriminate.
    inversion Hmatch; subst.
    exact Hdistinct.
Qed.

Lemma InstructionPattern_match_list_distinct :
  forall patterns instrs map map',
    PatternMap_distinct map ->
    InstructionPattern_match_list patterns instrs map = Some map' ->
    PatternMap_distinct map'.
Proof.
  induction patterns as [| pattern patterns IH]; intros instrs map map' Hdistinct Hmatch.
  - simpl in Hmatch.
    inversion Hmatch; subst.
    exact Hdistinct.
  - destruct instrs as [| instr instrs]; simpl in Hmatch; try discriminate.
    destruct (InstructionPattern_match pattern instr map)
      as [map_head |] eqn:Hhead; try discriminate.
    eapply IH with (instrs := instrs) (map := map_head); eauto.
    eapply InstructionPattern_match_distinct
      with (pattern := pattern) (instr := instr) (map := map); eauto.
Qed.

Lemma InstructionPattern_match_sound :
  forall pattern instr map map',
    InstructionPattern_match pattern instr map = Some map' ->
    InstructionPattern_inst pattern map' =
      Some (InstructionPattern_canonicalize instr).
Proof.
  induction pattern as [
    | theta' phi' lambda' qbit_pattern
    | control_pattern target_pattern
    | qbit1_pattern qbit2_pattern
    | qbit_pattern cbit_pattern
    | qbit_pattern
    | cbit_pattern expected_pattern body_patterns Hbody_patterns
    | instr_variable
    | exact_instr
  ] using InstructionPattern_ind';
  intros instr map map' Hmatch.
  - destruct instr; simpl in Hmatch; try discriminate.
    inversion Hmatch; subst.
    reflexivity.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (Angle_eqb theta theta') eqn:Htheta;
    destruct (Angle_eqb phi phi') eqn:Hphi;
    destruct (Angle_eqb lambda lambda') eqn:Hlambda; try discriminate.
    apply Angle_eqb_eq in Htheta, Hphi, Hlambda; subst.
    simpl.
    erewrite QbitPattern_match_sound with (value := qbit).
    reflexivity.
    apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match control_pattern control map)
      as [map_control |] eqn:Hcontrol; try discriminate.
    simpl.
    erewrite QbitPattern_inst_extends with (value := control).
    erewrite QbitPattern_match_sound with (value := target).
    + reflexivity.
    + apply Hmatch.
    + eapply QbitPattern_match_extends. apply Hmatch.
    + eapply QbitPattern_match_sound. apply Hcontrol.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match qbit1_pattern qbit1 map)
      as [map_qbit1 |] eqn:Hqbit1; try discriminate.
    simpl.
    erewrite QbitPattern_inst_extends with (value := qbit1).
    erewrite QbitPattern_match_sound with (value := qbit2).
    + reflexivity.
    + apply Hmatch.
    + eapply QbitPattern_match_extends. apply Hmatch.
    + eapply QbitPattern_match_sound. apply Hqbit1.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (QbitPattern_match qbit_pattern qbit map)
      as [map_qbit |] eqn:Hqbit; try discriminate.
    simpl.
    erewrite QbitPattern_inst_extends with (value := qbit).
    erewrite CbitPattern_match_sound with (value := cbit).
    + reflexivity.
    + apply Hmatch.
    + eapply CbitPattern_match_extends. apply Hmatch.
    + eapply QbitPattern_match_sound. apply Hqbit.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    simpl.
    erewrite QbitPattern_match_sound with (value := qbit).
    reflexivity.
    apply Hmatch.
  - destruct instr as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit
      | instrs
      | cbit expected body
      | qbit
    ]; simpl in Hmatch; try discriminate.
    destruct (Bool.eqb expected_pattern expected) eqn:Hexpected;
    try discriminate.
    assert (Hexpected_eq : expected_pattern = expected).
    {
      destruct expected_pattern, expected; simpl in Hexpected;
      try discriminate; reflexivity.
    }
    subst expected.
    destruct (CbitPattern_match cbit_pattern cbit map)
      as [map_cbit |] eqn:Hcbit; try discriminate.
    assert (Hcbit_inst : CbitPattern_inst cbit_pattern map_cbit = Some cbit).
    {
      eapply CbitPattern_match_sound.
      apply Hcbit.
    }
    clear Hcbit.
    assert (
      Hbody :
        fold_right
          (fun pattern instrs =>
            let* instr := InstructionPattern_inst pattern map' in
            let* instrs := instrs in
            Some (instr :: instrs))
          (Some [])
          body_patterns =
        Some
          (fold_right
            (fun instr acc =>
              InstructionPattern_canonicalize instr :: acc)
            []
            (InstructionPattern_body_view body))
        /\
        PatternMap_extends map_cbit map'
    ).
    {
      clear Hcbit_inst.
      revert map_cbit map' Hmatch Hbody_patterns.
      generalize (InstructionPattern_body_view body) as body_instrs.
      induction body_patterns as [| pattern patterns IHpatterns];
      intros body_instrs map_body map_final Hmatch Hforall;
      destruct body_instrs as [| instr instrs];
      simpl in Hmatch; try discriminate.
      - inversion Hmatch; subst.
        split.
        + reflexivity.
        + apply PatternMap_extends_refl.
      - inversion Hforall as [| ? ? Hhead_sound Htail_sound]; subst.
        destruct (InstructionPattern_match pattern instr map_body)
          as [map_head |] eqn:Hhead; try discriminate.
        destruct (IHpatterns instrs map_head map_final Hmatch Htail_sound)
          as [Htail_inst Htail_extends].
        split.
        + simpl.
          erewrite InstructionPattern_inst_extends with
            (map1 := map_head)
            (map2 := map_final)
            (instr := InstructionPattern_canonicalize instr).
          * rewrite Htail_inst.
            reflexivity.
          * apply Htail_extends.
          * exact (Hhead_sound instr map_body map_head Hhead).
        + apply PatternMap_extends_trans with map_head.
          * eapply InstructionPattern_match_extends.
            apply Hhead.
          * apply Htail_extends.
    }
    destruct Hbody as [Hbody_inst Hbody_extends].
    simpl.
    erewrite CbitPattern_inst_extends with (value := cbit).
    + rewrite Hbody_inst.
      destruct body; reflexivity.
    + apply Hbody_extends.
    + apply Hcbit_inst.
  - simpl in Hmatch.
    apply PatternMap_bind_instr_find in Hmatch.
    simpl.
    exact Hmatch.
  - simpl in Hmatch.
    destruct (Instruction_eqb exact_instr (InstructionPattern_canonicalize instr))
      eqn:Hinstr_eq; try discriminate.
    apply Instruction_eqb_eq in Hinstr_eq.
    subst exact_instr.
    reflexivity.
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
        patterns map' =
          Some (List.map InstructionPattern_canonicalize matched)
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
    exists map raw_lhs lhs rhs suffix,
      instrs = raw_lhs ++ suffix
      /\
      InstructionPattern_inst_list
        (rule_lhs rule) map = Some lhs
      /\
      lhs = List.map InstructionPattern_canonicalize raw_lhs
      /\
      InstructionPattern_inst_list
        (rule_rhs rule) map = Some rhs
      /\
      RewriteResult_consumed result = length raw_lhs
      /\
      RewriteResult_replacement result = rhs
      /\
      PatternMap_distinct map.
Proof.
  intros rule instrs result Happly.
  unfold RewriteRule_apply in Happly.
  destruct (RewriteRule_safeb rule) eqn:Hsafe; try discriminate.
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
  as (raw_lhs & suffix & Hinstrs & Hlhs & Hlength).
  exists
    map,
    raw_lhs,
    (List.map InstructionPattern_canonicalize raw_lhs),
    rhs,
    suffix.
  repeat split;
    try assumption;
    try reflexivity;
    try (simpl; symmetry; exact Hlength);
    try solve [
      eapply InstructionPattern_match_list_distinct;
      [apply PatternMap_empty_distinct | apply Hmatch]
    ].
Qed.

Lemma RewriteRule_apply_safe :
  forall rule instrs result,
    RewriteRule_apply rule instrs = Some result ->
    RewriteRule_safe rule.
Proof.
  intros rule instrs result Happly.
  unfold RewriteRule_apply in Happly.
  destruct (RewriteRule_safeb rule) eqn:Hsafe; try discriminate.
  apply RewriteRule_safeb_sound.
  exact Hsafe.
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

Lemma InstructionPattern_canonicalize_equiv :
  forall instr,
    Instruction_equiv nq
      instr
      (InstructionPattern_canonicalize instr).
Proof.
  apply Instruction_ind'; simpl; try reflexivity.
  - intros instrs Hforall.
    induction instrs as [| instr instrs IHinstrs]; simpl; try reflexivity.
    inversion Hforall as [| ? ? Hhead Htail]; subst.
    repeat rewrite Instruction_equiv_Seq_list_eq.
    apply qasm_seq_equiv_Proper.
    + exact Hhead.
    + apply IHinstrs.
      exact Htail.
  - intros cbit expected body Hbody.
    destruct body; simpl in *.
    + reflexivity.
    + apply Instruction_if_Proper; exact Hbody.
    + apply Instruction_if_Proper; exact Hbody.
    + apply Instruction_if_Proper; exact Hbody.
    + apply Instruction_if_Proper; exact Hbody.
    + apply Instruction_if_Proper.
      transitivity (SeqInstr (List.map InstructionPattern_canonicalize l)).
      * exact Hbody.
      * symmetry.
        apply Instruction_list_simp_eq.
    + apply Instruction_if_Proper; exact Hbody.
    + apply Instruction_if_Proper; exact Hbody.
Qed.

Lemma InstructionPattern_canonicalize_list_equiv :
  forall instrs,
    Instruction_equiv nq
      (SeqInstr instrs)
      (SeqInstr (List.map InstructionPattern_canonicalize instrs)).
Proof.
  intros instrs.
  induction instrs as [| instr instrs IHinstrs]; simpl; try reflexivity.
  repeat rewrite Instruction_equiv_Seq_list_eq.
  apply qasm_seq_equiv_Proper.
  - apply InstructionPattern_canonicalize_equiv.
  - exact IHinstrs.
Qed.

Lemma Instruction_list_simp_qbits_valid :
  forall instrs,
    Instruction_list_qbits_valid instrs ->
    Instruction_qbits_valid (Instruction_list_simp instrs).
Proof.
  intros instrs Hvalid.
  destruct instrs as [| instr instrs]; simpl.
  - constructor.
  - destruct instrs as [| instr' instrs]; simpl.
    + inversion Hvalid; subst.
      assumption.
    + constructor.
      exact Hvalid.
Qed.

Lemma InstructionPattern_canonicalize_qbits_valid :
  forall instr,
    Instruction_qbits_valid instr ->
    Instruction_qbits_valid (InstructionPattern_canonicalize instr).
Proof.
  intro instr.
  induction instr as [
    | theta phi lambda qbit
    | control target
    | qbit1 qbit2
    | qbit cbit
    | instrs Hforall
    | cbit expected body Hbody_ih
    | qbit
  ] using Instruction_ind'; simpl.
  - intros _.
    constructor.
  - intros Hvalid.
    exact Hvalid.
  - intros Hvalid.
    exact Hvalid.
  - intros Hvalid.
    exact Hvalid.
  - intros Hvalid.
    exact Hvalid.
  - intros Hvalid.
    inversion Hvalid as [| | | | | ? Hlist_valid | |]; subst.
    constructor.
    revert Hforall Hlist_valid.
    induction instrs as [| instr instrs IHinstrs];
    intros Hforall Hlist_valid; simpl.
    + constructor.
    + inversion Hforall as [| ? ? Hhead_ih Htail_ih]; subst.
      inversion Hlist_valid as [| ? ? Hhead_valid Htail_valid]; subst.
      constructor.
      * apply Hhead_ih.
        exact Hhead_valid.
      * apply IHinstrs.
        -- constructor.
           exact Htail_valid.
        -- exact Htail_ih.
        -- exact Htail_valid.
  - intros Hvalid.
    inversion Hvalid as [| | | | | | ? ? ? Hbody_valid |]; subst.
    destruct body as [
      | theta phi lambda qbit
      | control target
      | qbit1 qbit2
      | qbit cbit'
      | instrs
      | cbit' expected' body'
      | qbit
    ]; simpl in *.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
    + constructor.
      apply Instruction_list_simp_qbits_valid.
      specialize (Hbody_ih Hbody_valid).
      simpl in Hbody_ih.
      inversion Hbody_ih as [| | | | | ? Hcanonical_list_valid | |]; subst.
      exact Hcanonical_list_valid.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
    + constructor.
      apply Hbody_ih.
      exact Hbody_valid.
  - intros Hvalid.
    exact Hvalid.
Qed.

Lemma InstructionPattern_canonicalize_list_qbits_valid :
  forall instrs,
    Instruction_list_qbits_valid instrs ->
    Instruction_list_qbits_valid
      (List.map InstructionPattern_canonicalize instrs).
Proof.
  intros instrs Hvalid.
  induction instrs as [| instr instrs IHinstrs]; simpl.
  - constructor.
  - inversion Hvalid; subst.
    constructor.
    + apply InstructionPattern_canonicalize_qbits_valid.
      exact H1.
    + apply IHinstrs.
      exact H2.
Qed.

Lemma Instruction_list_qbits_valid_app :
  forall lhs rhs,
    Instruction_list_qbits_valid lhs ->
    Instruction_list_qbits_valid rhs ->
    Instruction_list_qbits_valid (lhs ++ rhs).
Proof.
  intros lhs rhs Hlhs Hrhs.
  induction Hlhs.
  - exact Hrhs.
  - simpl.
    constructor; assumption.
Qed.

(* Connection between rewriting scheme and instruction equality proof *)

Definition PatternRuleValid
    (spec : TransformSpec)
    (param : TransformParameter)
    : Prop :=
  forall rule,
  transform_rule spec param = Some rule ->
  forall subst lhs rhs suffix,
  RewriteRule_safe rule ->
  PatternMap_distinct subst ->
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
    RewriteRule_safe rule ->
    PatternMap_distinct subst ->
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
  pose proof (RewriteRule_apply_safe rule instrs result Happly)
    as Hrule_safe.
  destruct (RewriteRule_apply_decompose rule instrs result Happly)
    as (subst & raw_lhs & lhs & rhs & suffix
      & Hinstrs & Hlhs & Hlhs_eq & Hrhs & Hconsumed
      & Hreplacement & Hsubst_distinct).
  subst instrs lhs.
  destruct (Instruction_list_qbits_valid_app_inv raw_lhs suffix Hvalid)
    as [Hraw_lhs_valid Hsuffix_valid].
  assert (
    Hlhs_valid :
      Instruction_list_qbits_valid
        (List.map InstructionPattern_canonicalize raw_lhs ++ suffix)
  ).
  {
    apply Instruction_list_qbits_valid_app.
    - apply InstructionPattern_canonicalize_list_qbits_valid.
      exact Hraw_lhs_valid.
    - exact Hsuffix_valid.
  }
  rewrite Hconsumed.
  rewrite Hreplacement.
  rewrite skipn_prefix_length.
  transitivity
    (SeqInstr
      (List.map InstructionPattern_canonicalize raw_lhs ++ suffix)).
  - apply Instruction_equiv_implies_behavioral_equiv.
    repeat rewrite Instruction_equiv_Seq_list_list_eq.
    apply Instruction_equiv_rewrite_start.
    apply InstructionPattern_canonicalize_list_equiv.
  - eapply Hpattern; eauto.
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
  pose proof (RewriteRule_apply_safe rule instrs result Happly)
    as Hrule_safe.
  destruct (RewriteRule_apply_decompose rule instrs result Happly)
    as (subst & raw_lhs & lhs & rhs & suffix
      & Hinstrs & Hlhs & Hlhs_eq & Hrhs & Hconsumed
      & Hreplacement & Hsubst_distinct).
  subst instrs lhs.
  destruct (Instruction_list_qbits_valid_app_inv raw_lhs suffix Hvalid)
    as [Hraw_lhs_valid Hsuffix_valid].
  assert (
    Hlhs_valid :
      Instruction_list_qbits_valid
        (List.map InstructionPattern_canonicalize raw_lhs)
  ).
  {
    apply InstructionPattern_canonicalize_list_qbits_valid.
    exact Hraw_lhs_valid.
  }
  rewrite Hconsumed.
  rewrite Hreplacement.
  rewrite skipn_prefix_length.
  transitivity
    (SeqInstr
      (List.map InstructionPattern_canonicalize raw_lhs ++ suffix)).
  - repeat rewrite Instruction_equiv_Seq_list_list_eq.
    apply Instruction_equiv_rewrite_start.
    apply InstructionPattern_canonicalize_list_equiv.
  - repeat rewrite Instruction_equiv_Seq_list_list_eq.
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
		          -- solve_rewrite_apply_deep_list_structured
		              rule instrs Hresult IHHvalid IHHvalid0.
	          -- destruct (RewriteRule_apply rule [IfInstr cbit expected body])
	               as [root_result |] eqn:Hroot.
	             ++ destruct
	                  (RewriteRule_apply_deep_result rule body occurrence)
	                  as [body' body_status] eqn:Hbody_result.
	                assert (
	                  Hcurrent_result :
	                    RewriteRule_apply_deep_result
	                      rule (IfInstr cbit expected body) (S occurrence)
	                    =
	                    (IfInstr cbit expected body', body_status)
	                ).
	                {
	                  simpl.
	                  rewrite Hroot.
	                  rewrite Hbody_result.
	                  reflexivity.
	                }
	                specialize
	                  (IHHvalid
	                    (S occurrence)
	                    (IfInstr cbit expected body')
	                    body_status
	                    Hcurrent_result).
	                destruct body_status as [| occurrence''].
	                ** inversion Hresult; subst.
	                   repeat rewrite Instruction_equiv_Seq_list_eq.
	                   apply Instruction_equiv_rewrite_start.
	                   exact IHHvalid.
	                ** simpl in IHHvalid.
	                   inversion IHHvalid; subst.
	                   destruct
	                     (RewriteRule_apply_deep_list_result
	                       rule (RewriteRule_apply_deep_result rule)
	                       instrs occurrence'')
	                     as [rest' rest_status] eqn:Hrest_result.
	                   specialize
	                     (IHHvalid0
	                       occurrence'' rest' rest_status Hrest_result).
	                   destruct rest_status.
	                   --- inversion Hresult; subst.
	                       repeat rewrite Instruction_equiv_Seq_list_eq.
	                       apply Instruction_equiv_rewrite_end.
	                       exact IHHvalid0.
		                   --- inversion Hresult; subst.
		                       f_equal.
	             ++ destruct
	                  (RewriteRule_apply_deep_result rule body (S occurrence))
	                  as [body' body_status] eqn:Hbody_result.
	                assert (
	                  Hcurrent_result :
	                    RewriteRule_apply_deep_result
	                      rule (IfInstr cbit expected body) (S occurrence)
	                    =
	                    (IfInstr cbit expected body', body_status)
	                ).
	                {
	                  simpl.
	                  rewrite Hroot.
	                  rewrite Hbody_result.
	                  reflexivity.
	                }
	                specialize
	                  (IHHvalid
	                    (S occurrence)
	                    (IfInstr cbit expected body')
	                    body_status
	                    Hcurrent_result).
	                destruct body_status as [| occurrence''].
	                ** inversion Hresult; subst.
	                   repeat rewrite Instruction_equiv_Seq_list_eq.
	                   apply Instruction_equiv_rewrite_start.
	                   exact IHHvalid.
	                ** simpl in IHHvalid.
	                   inversion IHHvalid; subst.
	                   destruct
	                     (RewriteRule_apply_deep_list_result
	                       rule (RewriteRule_apply_deep_result rule)
	                       instrs occurrence'')
	                     as [rest' rest_status] eqn:Hrest_result.
	                   specialize
	                     (IHHvalid0
	                       occurrence'' rest' rest_status Hrest_result).
	                   destruct rest_status.
	                   --- inversion Hresult; subst.
	                       repeat rewrite Instruction_equiv_Seq_list_eq.
	                       apply Instruction_equiv_rewrite_end.
	                       exact IHHvalid0.
		                   --- inversion Hresult; subst.
		                       f_equal.
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
	      destruct (RewriteRule_apply rule [IfInstr cbit cond instr])
	        as [root_result |] eqn:Hroot.
	      + destruct occurrence as [| occurrence'].
	        * inversion Hresult; subst.
	          transitivity (SeqInstr [IfInstr cbit cond instr]).
	          -- symmetry.
	             apply Instruction_equiv_Seq_singleton.
	          -- transitivity
	               (SeqInstr
	                 (RewriteResult_replacement root_result
	                  ++ skipn
	                       (RewriteResult_consumed root_result)
	                       [IfInstr cbit cond instr])).
	             ++ eapply Hrule; eauto.
	                constructor; [exact Hvalid | constructor].
	             ++ symmetry.
	                apply Instruction_list_simp_eq.
	        * destruct
	            (RewriteRule_apply_deep_result rule instr occurrence')
	            as [body' status'] eqn:Hbody.
	          inversion Hresult; subst.
	          specialize (IHinstr Hbody_valid occurrence' body' status Hbody)
	            as Hbody_sound.
	          destruct status; subst.
	          -- apply Instruction_if_Proper.
	             exact Hbody_sound.
	          -- reflexivity.
	      + destruct
	          (RewriteRule_apply_deep_result rule instr occurrence)
	          as [body' status'] eqn:Hbody.
	        inversion Hresult; subst.
	        specialize (IHinstr Hbody_valid occurrence body' status Hbody)
	          as Hbody_sound.
	        destruct status; subst.
	        * apply Instruction_if_Proper.
	          exact Hbody_sound.
	        * reflexivity.
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
        RewriteRule_safe rule ->
        PatternMap_distinct subst ->
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
  intros subst lhs rhs suffix Hrule_safe Hsubst_distinct Hlhs Hrhs Hvalid.
  assert (Hmap :
    List.map (transform_postprocess spec param) suffix = suffix).
  {
    clear Hrule Hlhs Hrhs Hvalid Hsubst_distinct Hrule_safe.
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

Ltac solve_rewrite_rule_safe :=
  unfold RewriteRule_safe, list_subset,
    InstructionPattern_list_qbit_vars,
    InstructionPattern_list_cbit_vars,
    InstructionPattern_list_instr_vars;
  simpl;
  repeat split;
  intros ? Hin;
  simpl in Hin;
  repeat
    match type of Hin with
    | False => contradiction
    | _ \/ _ =>
        destruct Hin as [Hin | Hin];
        [subst; simpl; auto | simpl in Hin]
    | _ =>
        subst; simpl; auto
    end.

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
