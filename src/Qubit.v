Require Export Operator.
Import ListNotations.

Declare Scope Qst_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Open Scope M_scope.
Open Scope T_scope.

(* normalized qubit state ======================================================================= *)

Definition Qst_normalized (qst: ColVec) := dot_product (CVconjtrans qst) (qst) (CVconjtrans_bits qst) = 1.

Lemma Qst_normalized_unitary: forall (qst: ColVec) (qop: Matrix) (Heq: _),
  Qst_normalized qst -> Qop_unitary qop -> Qst_normalized (MVmult qop qst Heq).
Proof.
  unfold Qst_normalized, dot_product.
  intros.
  assert (RMeqbits (CVconjtrans qst) (Mconjtrans qop)) as H2.
  { unfold RMeqbits.
    rewrite CVconjtrans_bits.
    simpl_bits.
    symmetry.
    apply Heq. }
  rewrite CVconjtrans_mult with (H2 := H2).
  specialize dot_product_Mmult_assoc as Hassoc.
  unfold dot_product in Hassoc.
  erewrite Hassoc.
  erewrite <- MMVmult_assoc.
  unfold Qop_unitary in H0.
  rewrite VM
  unfold MVmult.
  simpl.



(* ============================================================================================== *)
(* base single qubit state ====================================================================== *)

Definition Qst_0: ColVec := {| CVbits := 1; CVinner := fun i => i |}.

Definition Qst_1: ColVec := {| CVbits := 1; CVinner := fun i => 1 - i |}.

(* Lemma Qst_0_normalized *)

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