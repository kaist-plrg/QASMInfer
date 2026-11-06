Require Import QASMInfer.util.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.rewrite.RewriteFunction.

From Stdlib Require Import String.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.

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
