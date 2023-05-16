Require Export Tensor.
Import ListNotations.

Declare Scope Qst_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Open Scope M_scope.
Open Scope T_scope.

(* base single qubit state ====================================================================== *)

Definition Q0: ColVec := {| CVbits := 1; CVinner := fun i => i |}.

Definition Q1: ColVec := {| CVbits := 1; CVinner := fun i => 1 - i |}.

(* ============================================================================================== *)
(* qubit state ================================================================================== *)

(* Inductive Qstate: nat -> ColVec -> Prop :=
| Qstate_base_0: Qstate 0 Q0
| Qstate_base_1: Qstate 0 Q1. *)

(* ============================================================================================== *)
(* fundamental qubit states ===================================================================== *)

(* Definition Qstate_0: {q: Qstate | bits_qst q = 1}.
Proof.
  refine (exist _ {|
    bits_qst := 1;
    inner_qst := {|
      rows := 2;
      cols := 1;
      inner := fun i j => i; (* 0 j -> 0, 1 j -> 1 *)
      |}
    |} _).
  Unshelve.
  reflexivity. lia. lia. reflexivity. reflexivity.
  intros. simpl.
  unfold Mmult_inner.
  simpl.
  unfold dot_product.
  lca.
Defined.

Definition Qstate_1: {q: Qstate | bits_qst q = 1}.
Proof.
  refine ( exist _ {|
    bits_qst := 1;
    inner_qst := {|
      rows := 2;
      cols := 1;
      inner := fun i j => 1 - i; (* 0 j -> 1, 1 j -> 0 *)
      |}
    |} _).
  Unshelve.
  reflexivity. lia. lia. reflexivity. reflexivity.
  intros. simpl.
  unfold Mmult_inner.
  simpl.
  unfold dot_product.
  lca.
Defined. *)

(* qubit state product ========================================================================== *)
(* ============================================================================================== *)

(* Definition Qstate_prod (q1 q2: Qstate): {q: Qstate | bits_qst q = (bits_qst q1 + bits_qst q2)%nat}.
Proof.
  refine (exist _ {|
    bits_qst := bits_qst q1 + bits_qst q2;
    inner_qst := (Tproduct (inner_qst q1) (inner_qst q2)).1;
    |} _).
  Unshelve.
  - reflexivity.
  - destruct (Tproduct (inner_qst q1) (inner_qst q2)) as [q Hq].
    destruct Hq as [Hq1 Hq2].
    simpl.
    rewrite Hq1.
    repeat rewrite inner_rows_qst.
    rewrite Nat.pow_add_r.
    reflexivity.
  - destruct (Tproduct (inner_qst q1) (inner_qst q2)) as [q Hq].
    destruct Hq as [Hq1 Hq2].
    simpl.
    rewrite Hq2.
    repeat rewrite inner_cols_qst.
    lia.
  - simpl.
Defined. *)

(* ============================================================================================== *)