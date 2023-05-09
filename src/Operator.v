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
(* fundamental single qubit operator ============================================================ *)



(* ============================================================================================== *)
(* ============================================================================================== *)