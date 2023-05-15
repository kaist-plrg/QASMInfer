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


(* single qubit rotation operators ============================================================== *)

Local Open Scope R_scope.

Definition Qop_ry (theta: R): Matrix := {|
  Mbits := 1;
  Minner := fun i j =>
    if i =? 0 then if j =? 0 then cos (theta / 2) else - sin (theta / 2)
    else if j =? 0 then           sin (theta / 2) else   cos (theta / 2);
  |}.

Definition Qop_rz (theta: R): Matrix := {|
  Mbits := 1;
  Minner := fun i j =>
    if i =? 0 then if j =? 0 then Cexp (0, - theta / 2) else          0
    else if j =? 0 then                     0           else Cexp (0, theta / 2);
  |}.

Definition Qop_rot (theta phi lambda: R): Matrix.
Proof.
  assert (MMeqbits (Qop_rz phi) (Qop_ry theta)) by reflexivity.
  destruct (Mmult (Qop_rz phi) (Qop_ry theta) H) as [rzy Hzy].
  assert (MMeqbits rzy (Qop_rz lambda)) by apply Hzy.
  destruct (Mmult rzy (Qop_rz lambda) H0) as [rzyz Hzyz].
  exact rzyz.
Defined.

Local Close Scope R_scope.

(* swap operator ================================================================================ *)

Definition Qswap2: Matrix := {|
  Mbits := 2;
  Minner := fun i j => match i, j with
    | 0, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 3, 3 => 1
    | _, _ => 0
    end;
  |}.

Fixpoint Qswap1n (n: nat) (H: n > 1): {m: Matrix | Mbits m = n}.
Proof.
  destruct (lt_eq_lt_dec n 2) as [Hn|Hn].
  - destruct Hn.
    + lia.
    + refine (exist _ Qswap2 _).
      simpl. lia.
  - destruct n as [|n'].
    + lia.
    + destruct n' as [|n''] eqn: Hn'n''.
      * lia.
      * destruct (eye n'') as [eyen'' Heyen''].
        destruct (eye 1) as [eye1 Heye1].
        destruct (TMproduct Qswap2 (eyen'')) as [swap12n H12].
        assert (n' > 1) as Hn' by lia.
        destruct (Qswap1n n' Hn') as [swap1n' H1n'].
        destruct (TMproduct eye1 swap1n') as [swap1n'n H1n'n].
        assert (MMeqbits swap12n swap1n'n) as H1.
        { unfold MMeqbits.
          rewrite H1n'n.
          rewrite H12.
          rewrite Heyen''.
          rewrite H1n'.
          rewrite Heye1.
          simpl.
          lia. }
        destruct (Mmult swap12n swap1n'n H1) as [m' Hm'].
        destruct (Mmult m' swap12n Hm') as [m Hm].
        refine (exist _ m _).
        rewrite Hm.
        rewrite Hm'.
        rewrite H12.
        rewrite Heyen''.
        reflexivity.
Defined.

Definition Qswap (n q1 q2: nat) (H1: q1 < n) (H2: q2 < n): {m: Matrix | Mbits m = n}.
Proof.
  destruct (lt_eq_lt_dec q1 q2) as [H|H].
  - destruct H as [H|H].
    + destruct (eye q1) as [eye1 Heye1].
      destruct (eye (n - q2 - 1)) as [eye2 Heye2].
      assert (q2 - q1 + 1 > 1) as Hgt by lia.
      destruct (Qswap1n (q2 - q1 + 1) Hgt) as [swap1n H1n].
      destruct (TMproduct eye1 swap1n) as [swapq1q2' Hq1q2'].
      destruct (TMproduct swapq1q2' eye2) as [swapq1q2 Hq1q2].
      refine (exist _ swapq1q2 _).
      rewrite Hq1q2.
      rewrite Hq1q2'.
      rewrite Heye1.
      rewrite Heye2.
      rewrite H1n.
      ring_simplify.
      lia.
    + apply (eye n).
  - destruct (eye q2) as [eye1 Heye1].
    destruct (eye (n - q1 - 1)) as [eye2 Heye2].
    assert (q1 - q2 + 1 > 1) as Hgt by lia.
    destruct (Qswap1n (q1 - q2 + 1) Hgt) as [swap1n H1n].
    destruct (TMproduct eye1 swap1n) as [swapq1q2' Hq1q2'].
    destruct (TMproduct swapq1q2' eye2) as [swapq1q2 Hq1q2].
    refine (exist _ swapq1q2 _).
    rewrite Hq1q2.
    rewrite Hq1q2'.
    rewrite Heye1.
    rewrite Heye2.
    rewrite H1n.
    ring_simplify.
    lia.
Defined.

(* ============================================================================================== *)
(* CNOT operator ================================================================================ *)

Definition QcnotCT: Matrix := {|
  Mbits := 2;
  Minner := fun i j => match i, j with
    | 0, 0 => 1
    | 1, 1 => 1
    | 2, 3 => 1
    | 3, 2 => 1
    | _, _ => 0
    end;
  |}.

Definition QcnotTC: Matrix := {|
  Mbits := 2;
  Minner := fun i j => match i, j with
    | 0, 1 => 1
    | 1, 0 => 1
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
    end;
  |}.

Definition QcnotCTn (n: nat) (Hn: n >= 2): {m: Matrix | Mbits m = n}.
Proof.
  destruct (eye (n - 2)) as [eyen'' Heyen''].
  destruct (TMproduct QcnotCT eyen'') as [m Hm].
  refine (exist _ m _).
  rewrite Hm.
  rewrite Heyen''.
  simpl.
  lia.
Defined.

Definition QcnotTCn (n: nat) (Hn: n >= 2): {m: Matrix | Mbits m = n}.
Proof.
  destruct (eye (n - 2)) as [eyen'' Heyen''].
  destruct (TMproduct QcnotTC eyen'') as [m Hm].
  refine (exist _ m _).
  rewrite Hm.
  rewrite Heyen''.
  simpl.
  lia.
Defined.

Definition Qcnot (n qc qt: nat) (Hc: qc < n) (Ht: qt < n).
Proof.


(* ============================================================================================== *)
(* quantum qubit operator ======================================================================= *)

Inductive Qoperator: nat -> Matrix -> Prop :=

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