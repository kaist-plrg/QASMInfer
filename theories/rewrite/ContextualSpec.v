Require Import QASMInfer.util.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.DeadGuard.
Require Import QASMInfer.rewrite.RewriteFunction.
Require Import QASMInfer.rewrite.Spec.
Require Import QASMInfer.rewrite.ManualSpec.
From Stdlib Require Import String.

(* A contextual entry has a checked application function in addition to its
   ordinary pattern metadata. The latter must not be dispatched through
   TransformSpec_apply: only contextual_apply enforces the prefix condition.
   None includes a failed site precondition; occurrences are not renumbered. *)
Record ContextualTransformSpec := {
  contextual_metadata : TransformSpec;
  contextual_apply : TransformParameter -> Instruction -> nat -> option Instruction
}.

Definition ContextualTransformSpecValid nq (spec : ContextualTransformSpec) : Prop :=
  forall param instr occurrence result nc,
  contextual_apply spec param instr occurrence = Some result ->
  Program_equiv nq nc result instr.

Definition TransformSpec_Insert_Dead_If_Bit nq : TransformSpec :=
  {| transform_name := "Insert_Dead_If_Bit";
     transform_rule := fun param =>
       match param with
       | Param_cbit_instr cbit instr =>
           if Instruction_qbits_validb nq instr
           then Some (Rule_Insert_Dead_If_Bit cbit instr) else None
       | _ => None
       end;
     transform_postprocess := fun _ instr => instr;
     transform_strategy := TransformDeep;
     transform_param_kind := ParamKind_cbit_instr |}.

Definition ContextualSpec_Insert_Dead_If_Bit nq : ContextualTransformSpec :=
  {| contextual_metadata := TransformSpec_Insert_Dead_If_Bit nq;
     contextual_apply := fun param instr occurrence =>
       match param with
       | Param_cbit_instr cbit body =>
           if Instruction_qbits_validb nq body
           then Dead_guard_apply cbit body instr occurrence else None
       | _ => None
       end |}.

Theorem ContextualSpec_Insert_Dead_If_Bit_valid : forall nq,
  ContextualTransformSpecValid nq (ContextualSpec_Insert_Dead_If_Bit nq).
Proof.
  intros nq param instr occurrence result nc Happ.
  destruct param; try discriminate.
  cbn [ContextualSpec_Insert_Dead_If_Bit contextual_apply] in Happ.
  destruct (Instruction_qbits_validb nq i); try discriminate.
  eapply Transform_dead_if_deep; exact Happ.
Qed.
