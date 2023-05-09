Require Export Tensor.
Import ListNotations.

Declare Scope Qop_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Open Scope M_scope.
Open Scope T_scope.


(* quantum qubit operator ======================================================================= *)

Record Qoperator := {
  bits_qop: nat;
  inner_qop: Matrix;
  inner_rows_qop: rows inner_qop = (2^bits_qop)%nat;
  inner_cols_qop: cols inner_qop = (2^bits_qop)%nat;
}.

(* ============================================================================================== *)
(* sequence of operators (not a multiplication) ================================================= *)

Definition Qop_seq (qop1 qop2: Qoperator) (H: bits_qop qop1 = bits_qop qop2)
  : {qop: Qoperator | bits_qop qop = bits_qop qop1}.
Proof.
  refine ( exist _ {|
    bits_qop := bits_qop qop1;
    (* NOTE: qop1 is applied first: m = m2 * m1 *)
    inner_qop := (Mmult (inner_qop qop2) (inner_qop qop1) _).1;
    |} _ ).
  Unshelve.
  - reflexivity.
  - rewrite inner_rows_qop.
    rewrite inner_cols_qop.
    rewrite H.
    reflexivity.
  - simpl.
    rewrite inner_rows_qop.
    rewrite H.
    reflexivity.
  - simpl.
    rewrite inner_cols_qop.
    rewrite H.
    reflexivity.
Qed.

(* ============================================================================================== *)
(* fundamental qubit operators ================================================================== *)

Definition Qop_id (bits: nat): {qop: Qoperator | bits_qop qop = bits}.
Proof.
  refine ( exist _ {|
    bits_qop := bits;
    inner_qop := (eye (2 ^ bits) _).1;
    |} _ ).
  Unshelve.
  - reflexivity.
  - induction bits as [|bits].
    * simpl. lia.
    * simpl. lia.
  - reflexivity.
  - reflexivity.
Defined.


Definition Qop_ry (theta: R): {qop: Qoperator | bits_qop qop = 1}.
Proof.
Local Open Scope R_scope.
  refine ( exist _ {|
    bits_qop := 1;
    inner_qop := {|
      rows := 2;
      cols := 2;
      inner := fun i j =>
        if i =? 0 then if j =? 0 then cos (theta / 2) else - sin (theta / 2)
        else if j =? 0 then           sin (theta / 2) else   cos (theta / 2);
      |}
    |} _ ).
  Unshelve.
  reflexivity. lia. lia. reflexivity. reflexivity.
Local Close Scope R_scope.
Qed.

Definition Qop_rz (theta: R): {qop: Qoperator | bits_qop qop = 1}.
Proof.
Local Open Scope R_scope.
  refine ( exist _ {|
    bits_qop := 1;
    inner_qop := {|
      rows := 2;
      cols := 2;
      inner := fun i j =>
        if i =? 0 then if j =? 0 then Cexp (0, - theta / 2) else          0
        else if j =? 0 then                     0           else Cexp (0, theta / 2);
      |}
    |} _ ).
  Unshelve.
  reflexivity. lia. lia. reflexivity. reflexivity.
Local Close Scope R_scope.
Qed.

Definition Qop_rot (theta phi lambda: R): {qop: Qoperator | bits_qop qop = 1}.
Proof.
  destruct (Qop_rz lambda) as [rzl Hrzl].
  destruct (Qop_ry theta) as [ryt Hryt].
  destruct (Qop_rz phi) as [rzp Hrzp].
  assert (bits_qop rzl = bits_qop ryt) as H1 by lia.
  destruct (Qop_seq rzl ryt H1) as [rzy Hzy].
  assert (bits_qop rzy = bits_qop rzp) as H2 by lia.
  destruct (Qop_seq rzy rzp H2) as [r Hr].
  refine (exist _ r _).
  lia.
Defined.

(* ============================================================================================== *)
(* ============================================================================================== *)