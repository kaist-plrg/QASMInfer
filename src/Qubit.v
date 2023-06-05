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
  intros qst qop Heq H [Hl Hr].
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
  specialize MVmult_eye as Hmveye.
  unfold Qop_unitary_l, Qop_unitary_r, Mmult, MVmult in *.
  rewrite Hr.
  replace (Mbits qop) with (CVbits qst).
  rewrite Hmveye.
  apply H.
  all: simpl_bits; lia.
  Unshelve.
  1-2: simpl_bits; reflexivity.
  simpl_bits. lia.
Qed.

(* ============================================================================================== *)
(* base single qubit state ====================================================================== *)

Definition Qst_0: ColVec := {| CVbits := 1; CVinner := fun i => i |}.

Definition Qst_1: ColVec := {| CVbits := 1; CVinner := fun i => 1 - i |}.

Lemma Qst_0_normalized: Qst_normalized Qst_0.
Proof. lca. Qed.

Lemma Qst_1_normalized: Qst_normalized Qst_1.
Proof. lca. Qed.

(* ============================================================================================== *)
(* qubit state ================================================================================== *)

Inductive Qstate: nat -> ColVec -> Prop :=
| Qstate_base_0: Qstate 1 Qst_0
| Qstate_base_1: Qstate 1 Qst_1
| Qstate_multi_qubit (n1 n2: nat) (qst1 qst2: ColVec):
    Qstate n1 qst1 -> Qstate n2 qst2 -> Qstate (n1 + n2) (TCVproduct qst1 qst2).

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