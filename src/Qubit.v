Require Export Tensor.
Import ListNotations.

Declare Scope Q_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Open Scope M_scope.
Open Scope T_scope.


(* qubit state ================================================================================== *)

Record Qstate := {
  bits_qst: nat;
  inner_qst: Matrix;
  inner_rows_qst: rows inner_qst = (2^bits_qst)%nat;
  inner_cols_qst: cols inner_qst = 1;
}.

Definition Qstate_0: Qstate.
Proof.
  refine {|
    bits_qst := 1;
    inner_qst := {|
      rows := 2;
      cols := 1;
      inner := fun i j => i; (* 0 j -> 0, 1 j -> 1 *)
      |}
    |}.
  Unshelve.
  reflexivity. reflexivity. lia. lia.
Defined.

Definition Qstate_1: Qstate.
Proof.
  refine {|
    bits_qst := 1;
    inner_qst := {|
      rows := 2;
      cols := 1;
      inner := fun i j => 1 - i; (* 0 j -> 1, 1 j -> 0 *)
      |}
    |}.
  Unshelve.
  reflexivity. reflexivity. lia. lia.
Defined.

(* qubit state product ========================================================================== *)
(* ============================================================================================== *)

Definition Qstate_prod (q1 q2: Qstate): {q: Qstate | bits_qst q = (bits_qst q1 + bits_qst q2)%nat}.
Proof.
  refine (exist _ {|
    bits_qst := bits_qst q1 + bits_qst q2;
    inner_qst := proj1_sig (Tproduct (inner_qst q1) (inner_qst q2));
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
Defined.

(* ============================================================================================== *)
(* quantum qubit operator ======================================================================= *)

Record Qoperator := {
  bits_qop: nat;
  inner_qop: Matrix;
  inner_rows_qop: rows inner_qop = (2^bits_qop)%nat;
  inner_cols_qop: cols inner_qop = (2^bits_qop)%nat;
}.

(* ============================================================================================== *)
(* ============================================================================================== *)