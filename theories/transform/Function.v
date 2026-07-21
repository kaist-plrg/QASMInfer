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

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Import List.ListNotations.

Section PATTERN.

Definition R_eqb (x y: R): bool :=
  if Req_EM_T x y then true else false.

Inductive NatPattern: Type :=
  | NatExact: nat -> NatPattern
  | NatVar: nat -> NatPattern.

Inductive InstructionPattern: Type :=
  | PNop: InstructionPattern
  | PRotate: R -> R -> R -> NatPattern -> InstructionPattern
  | PCnot: NatPattern -> NatPattern -> InstructionPattern
  | PSwap: NatPattern -> NatPattern -> InstructionPattern
  | PMeasure: NatPattern -> NatPattern -> InstructionPattern
  | PReset: NatPattern -> InstructionPattern.

Definition NatSubst : Type :=
  NatMap.t nat.

Definition empty_nat_subst : NatSubst :=
  NatMap.empty nat.

Definition lookup_nat
    (variable : nat)
    (subst : NatSubst)
    : option nat :=
  NatMap.find variable subst.

Definition bind_nat
    (variable value : nat)
    (subst : NatSubst)
    : option NatSubst :=
  match NatMap.find variable subst with
  | None =>
      Some (NatMap.add variable value subst)

  | Some old_value =>
      if Nat.eqb old_value value then
        Some subst
      else
        None
  end.

Definition match_nat_pattern
    (pattern : NatPattern)
    (value : nat)
    (subst : NatSubst)
    : option NatSubst :=
  match pattern with
  | NatExact expected =>
      if Nat.eqb expected value then
        Some subst
      else
        None
  | NatVar variable =>
      bind_nat variable value subst
  end.

Definition instantiate_nat_pattern
    (pattern : NatPattern)
    (subst : NatSubst)
    : option nat :=
  match pattern with
  | NatExact value =>
      Some value
  | NatVar variable =>
      NatMap.find variable subst
  end.

(* ================================================================ *)
(* Match one instruction                                            *)
(* ================================================================ *)

Definition match_instruction_pattern
    (pattern : InstructionPattern)
    (instr : Instruction)
    (subst : NatSubst)
    : option NatSubst :=
  match pattern, instr with
  | PNop, NopInstr =>
      Some subst

  | PRotate expected_theta
              expected_phi
              expected_lambda
              qbit_pattern,
    RotateInstr theta phi lambda qbit =>

      if R_eqb theta expected_theta then
        if R_eqb phi expected_phi then
          if R_eqb lambda expected_lambda then
            match_nat_pattern qbit_pattern qbit subst
          else
            None
        else
          None
      else
        None

  | PCnot control_pattern target_pattern,
    CnotInstr control target =>

      match match_nat_pattern control_pattern control subst with
      | Some subst' =>
          match_nat_pattern target_pattern target subst'
      | None =>
          None
      end

  | PSwap qbit1_pattern qbit2_pattern,
    SwapInstr qbit1 qbit2 =>

      match match_nat_pattern qbit1_pattern qbit1 subst with
      | Some subst' =>
          match_nat_pattern qbit2_pattern qbit2 subst'
      | None =>
          None
      end

  | PMeasure qbit_pattern cbit_pattern,
    MeasureInstr qbit cbit =>

      match match_nat_pattern qbit_pattern qbit subst with
      | Some subst' =>
          match_nat_pattern cbit_pattern cbit subst'
      | None =>
          None
      end

  | PReset qbit_pattern,
    ResetInstr qbit =>

      match_nat_pattern qbit_pattern qbit subst

  | _, _ =>
      None
  end.


(* ================================================================ *)
(* Match a pattern list against the prefix of an instruction list    *)
(* ================================================================ *)

Fixpoint match_instruction_prefix
    (patterns : list InstructionPattern)
    (instrs : list Instruction)
    (subst : NatSubst)
    {struct patterns}
    : option NatSubst :=
  match patterns with
  | [] =>
      Some subst

  | pattern :: pattern_rest =>
      match instrs with
      | [] =>
          None

      | instr :: instr_rest =>
          match match_instruction_pattern pattern instr subst with
          | Some subst' =>
              match_instruction_prefix
                pattern_rest
                instr_rest
                subst'

          | None =>
              None
          end
      end
  end.


(* ================================================================ *)
(* Instantiate one instruction pattern                              *)
(* ================================================================ *)

Definition instantiate_instruction_pattern
    (pattern : InstructionPattern)
    (subst : NatSubst)
    : option Instruction :=
  match pattern with
  | PNop =>
      Some NopInstr

  | PRotate theta phi lambda qbit_pattern =>
      match instantiate_nat_pattern qbit_pattern subst with
      | Some qbit =>
          Some (RotateInstr theta phi lambda qbit)
      | None =>
          None
      end

  | PCnot control_pattern target_pattern =>
      match instantiate_nat_pattern control_pattern subst with
      | Some control =>
          match instantiate_nat_pattern target_pattern subst with
          | Some target =>
              Some (CnotInstr control target)
          | None =>
              None
          end
      | None =>
          None
      end

  | PSwap qbit1_pattern qbit2_pattern =>
      match instantiate_nat_pattern qbit1_pattern subst with
      | Some qbit1 =>
          match instantiate_nat_pattern qbit2_pattern subst with
          | Some qbit2 =>
              Some (SwapInstr qbit1 qbit2)
          | None =>
              None
          end
      | None =>
          None
      end

  | PMeasure qbit_pattern cbit_pattern =>
      match instantiate_nat_pattern qbit_pattern subst with
      | Some qbit =>
          match instantiate_nat_pattern cbit_pattern subst with
          | Some cbit =>
              Some (MeasureInstr qbit cbit)
          | None =>
              None
          end
      | None =>
          None
      end

  | PReset qbit_pattern =>
      match instantiate_nat_pattern qbit_pattern subst with
      | Some qbit =>
          Some (ResetInstr qbit)
      | None =>
          None
      end
  end.


(* ================================================================ *)
(* Instantiate an instruction-pattern list                          *)
(* ================================================================ *)

Fixpoint instantiate_instruction_patterns
    (patterns : list InstructionPattern)
    (subst : NatSubst)
    {struct patterns}
    : option (list Instruction) :=
  match patterns with
  | [] =>
      Some []

  | pattern :: pattern_rest =>
      match instantiate_instruction_pattern pattern subst with
      | Some instr =>
          match
            instantiate_instruction_patterns
              pattern_rest
              subst
          with
          | Some instrs =>
              Some (instr :: instrs)
          | None =>
              None
          end

      | None =>
          None
      end
  end.


(* ================================================================ *)
(* Rewrite rule                                                     *)
(* ================================================================ *)

Record RewriteRule : Type := {
  rule_lhs : list InstructionPattern;
  rule_rhs : list InstructionPattern
}.


Record RewriteResult : Type := {
  rewrite_consumed : nat;
  rewrite_replacement : list Instruction
}.


(* 현재 instruction list의 시작 위치에서 rule을 적용해 본다. *)
Definition apply_rule_at
    (rule : RewriteRule)
    (instrs : list Instruction)
    : option RewriteResult :=
  match rule_lhs rule with
  | [] =>
      (* 빈 LHS는 허용하지 않는다. *)
      None

  | _ :: _ =>
      match
        match_instruction_prefix
          (rule_lhs rule)
          instrs
          empty_nat_subst
      with
      | Some subst =>
          match
            instantiate_instruction_patterns
              (rule_rhs rule)
              subst
          with
          | Some replacement =>
              Some {|
                rewrite_consumed :=
                  length (rule_lhs rule);

                rewrite_replacement :=
                  replacement
              |}

          | None =>
              None
          end

      | None =>
          None
      end
  end.


(* ================================================================ *)
(* Rewrite the nth occurrence in a flat sequence                    *)
(* ================================================================ *)

(*
  occurrence는 0부터 시작한다.

  0: 첫 번째로 일치하는 위치
  1: 두 번째로 일치하는 위치
  ...
*)
Fixpoint Rewrite_Nth_Seq
    (rule : RewriteRule)
    (instrs : list Instruction)
    (occurrence : nat)
    {struct instrs}
    : list Instruction :=
  match instrs with
  | [] =>
      []

  | current :: rest =>
      match apply_rule_at rule instrs with
      | Some result =>
          match occurrence with
          | O =>
              (* 목표 위치를 찾았으므로 치환하고,
                 뒤쪽은 더 탐색하지 않고 그대로 붙인다. *)
              rewrite_replacement result
              ++ skipn
                   (rewrite_consumed result)
                   instrs

          | S occurrence' =>
              (* 현재 위치도 일치하지만 원하는 occurrence가 아님. *)
              current
              :: Rewrite_Nth_Seq
                   rule
                   rest
                   occurrence'
          end

      | None =>
          (* 현재 위치에서는 일치하지 않음. *)
          current
          :: Rewrite_Nth_Seq
               rule
               rest
               occurrence
      end
  end.


(* ================================================================ *)
(* Convert a list back to Instruction                               *)
(* ================================================================ *)

Definition instruction_of_list
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
(* Public rewriting functions                                       *)
(* ================================================================ *)

Fixpoint Rewrite_Nth
    (rule : RewriteRule)
    (instr : Instruction)
    (occurrence : nat)
    {struct instr}
    : Instruction :=
  match instr with
  | SeqInstr instrs =>
      SeqInstr
        (Rewrite_Nth_Seq rule instrs occurrence)

  | IfInstr cbit expected body =>
      IfInstr
        cbit
        expected
        (Rewrite_Nth rule body occurrence)

  | _ =>
      instruction_of_list
        (Rewrite_Nth_Seq rule [instr] occurrence)
  end.


Definition Rewrite_First
    (rule : RewriteRule)
    (instr : Instruction)
    : Instruction :=
  Rewrite_Nth rule instr 0.

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
  PRotate PI (PI / 2) (PI / 2) qbit_pattern.

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

Definition Transform_X_X
    (instr : Instruction)
    (occurrence : nat)
    : Instruction :=
  Rewrite_Nth Rule_I_to_XX instr occurrence.

Definition Atomic_qbits_valid
    (instr : Instruction)
    : Prop :=
  match instr with
  | NopInstr =>
      True
  | RotateInstr _ _ _ qbit =>
      Qbit_index_valid nq qbit
  | CnotInstr control target =>
      Qbit_index_valid nq control
      /\ Qbit_index_valid nq target
  | SwapInstr qbit1 qbit2 =>
      Qbit_index_valid nq qbit1
      /\ Qbit_index_valid nq qbit2
  | MeasureInstr qbit _ =>
      Qbit_index_valid nq qbit
  | ResetInstr qbit =>
      Qbit_index_valid nq qbit
  | SeqInstr _ =>
      True
  | IfInstr _ _ _ =>
      True
  end.

Definition RewriteRuleValid
    (rule : RewriteRule)
    : Prop :=
  forall instrs result,
    Forall Atomic_qbits_valid instrs ->
    apply_rule_at rule instrs = Some result ->
    Instruction_equiv nq
      (SeqInstr instrs)
      (SeqInstr (rewrite_replacement result
       ++ skipn
            (rewrite_consumed result)
            instrs)).

Theorem Rewrite_Nth_Seq_sound :
  forall rule,
    RewriteRuleValid rule ->
    forall instrs occurrence,
      Forall Atomic_qbits_valid instrs ->
      Instruction_equiv nq
        (SeqInstr instrs)
        (SeqInstr (Rewrite_Nth_Seq rule instrs occurrence)).
Proof.
  intros rule Hrule.

  induction instrs as [| current rest IH].
  - intros occurrence Hvalid.
    simpl.
    reflexivity.
  - intros occurrence Hvalid.
    inversion Hvalid as
      [| current' rest' Hcurrent Hrest];
      subst.
    simpl.
    destruct (apply_rule_at rule (current :: rest))
      as [result |] eqn:Happly.
    + destruct occurrence as [| occurrence'].
      * (* 현재 위치가 원하는 occurrence *)
        apply Hrule; assumption.
      * (* 현재 match는 건너뛰고 뒤쪽을 rewrite *)
        shelve.

    + (* 현재 위치에서 match되지 않음 *)
      shelve.
Admitted.

Lemma Transform_X_X_valid:
  forall (instr: Instruction) (occurrence: nat),
  Instruction_equiv nq
  instr
  (Transform_X_X instr occurrence).
Proof.
Admitted.