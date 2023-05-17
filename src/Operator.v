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


(* definition of unitary matrix ================================================================= *)

Definition Qop_mmd (m: Matrix): Matrix := Mmult m (Mconjtrans m) (Mconjtrans_bits m).

Definition Qop_unitary (m: Matrix) := Mequal (Qop_mmd m) (eye (Mbits m)).

Lemma Qop_unitary_mult_suppl: forall (m1 m2: Matrix) (H12: _) (H21: _) (H1221: _),
  Mequal (Mmult (Mmult m1 m2 H12) (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H1221) (eye (Mbits m1)) ->
  Qop_unitary (Mmult m1 m2 H12).
Proof.
  intros.
  split.
  - unfold MMeqbits.
    reflexivity.
  - intros.
    specialize (Mconjtrans_mult m1 m2 H12 H21) as Hd.
    destruct Hd as [Hd1 Hd2].
    unfold Mget in *.
    rewrite Mmult_bits_l.
    destruct H as [H1 H2].
    unfold Mget in H2.
    unfold Msize in *.
    unfold Qop_mmd in *.
    rewrite Mconjtrans_bits in *.
    repeat rewrite Mmult_bits_l in *.
    rewrite Mconjtrans_bits in *.
    rewrite eye_bits in *.
    rewrite <- H2.
    unfold Qop_mmd.
    assert (Mequal (Mmult (Mmult m1 m2 H12) (Mconjtrans (Mmult m1 m2 H12))
    (Mconjtrans_bits (Mmult m1 m2 H12))) (Mmult (Mmult m1 m2 H12) (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H1221)) as Heq.
    { apply Mmult_eq.
      split.
      - unfold MMeqbits.
        repeat rewrite Mconjtrans_bits.
        rewrite Mmult_bits_l.
        rewrite Mmult_bits_r.
        rewrite Mconjtrans_bits.
        reflexivity.
      - unfold Mget.
        apply Hd2. }
    destruct Heq.
    unfold Mget in *.
    unfold Msize in *.
    unfold Qop_mmd in *.
    repeat rewrite Mmult_bits_l in *.
    apply H0.
    lia.  lia.  lia.  lia.  lia.  lia.  lia.  lia.
Qed.

Lemma Qop_unitary_mult: forall (m1 m2: Matrix) (H: _),
  Qop_unitary m1 -> Qop_unitary m2 -> Qop_unitary (Mmult m1 m2 H).
Proof.
  intros.
  assert (MMeqbits (Mconjtrans m2) (Mconjtrans m1)) as H21.
  { unfold MMeqbits.
    repeat rewrite Mconjtrans_bits.
    symmetry.
    apply H. }
  assert (MMeqbits (Mmult m1 m2 H) (Mmult (Mconjtrans m2) (Mconjtrans m1) H21)) as H1221.
  { unfold MMeqbits.
    repeat rewrite Mmult_bits_l.
    rewrite Mconjtrans_bits.
    apply H. }
  apply (Qop_unitary_mult_suppl m1 m2 H H21 H1221).
  Unshelve.
  - split.
    + unfold MMeqbits.
      repeat rewrite Mmult_bits_l.
      apply eye_bits.
    + intros.
      unfold Mget.
      assert (MMeqbits m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21)) as H23.
      { unfold MMeqbits.
        repeat rewrite Mmult_bits_l.
        rewrite Mconjtrans_bits.
        reflexivity. }
      assert (MMeqbits m1 (Mmult m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H23)) as H1_23.
      { unfold MMeqbits.
        repeat rewrite Mmult_bits_l.
        apply H. }
      specialize
        (Mmult_assoc m1 m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H H1221 H23 H1_23)
        as Hassoc.
      destruct Hassoc as [_ Hassoc].
      unfold Mget, Msize in *.
      simpl_bits.
      specialize (Hassoc i j Hi1 Hi1 Hj1 Hj2).
      rewrite Hassoc.
      assert (MMeqbits (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1)) as H22_1.
      { unfold MMeqbits.
        repeat rewrite Mmult_bits_l.
        rewrite Mconjtrans_bits.
        symmetry.
        apply H. }
      assert (MMeqbits m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21)) as H2_21.
      { unfold MMeqbits.
        simpl_bits.
        reflexivity. }
      assert (Mequal
        (Mmult m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H23)
        (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1)) as Hassoc2.
      { split.
        - unfold MMeqbits.
          simpl_bits.
          reflexivity.
        - intros.
          unfold Mget.
          simpl_bits.
          specialize
            (Mmult_assoc m2 (Mconjtrans m2) (Mconjtrans m1) (Mconjtrans_bits m2) H22_1 H21 H2_21)
            as Hassoc2.
          destruct Hassoc2 as [_ Hassoc2].
          unfold Mget in Hassoc2.
          simpl_bits.
          symmetry.
          apply Hassoc2.
          lia.
          lia.
          lia.
          lia.
      }
      assert (MMeqbits m1 (Mmult m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H23)) as H1_2_21.
      { unfold MMeqbits.
      assert (MMeqbits m1 (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1)) as H1_22_1.
      specialize
        (Mmult_eq m1
        (Mmult m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H23)
        (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1)) as Hmeq.



      rewrite Mmult_eq.
      unfold Qop_unitary in *.
      unfold Mequal in *.
      destruct H0 as [H00 H01].
      destruct H1 as [H10 H11].
      unfold Mget in *.
      unfold Qop_mmd in *.
      unfold Msize in *.
      rewrite Mmult_bits_l in *.
      rewrite eye_bits in *.
      unfold Mmult in *.
      unfold Mmult_inner in *.
      simpl in *.
      unfold eye.
      f_equal.
      unfold Msize in *.
      simpl.
      rewrite H in Hi2.
      rewrite H in Hj2.
      specialize (H01 i j Hi1 Hi1 Hj1 Hj1).
      specialize (H11 i j Hi2 Hi2 Hj2 Hj2).
      f_equal.



  unfold Qop_unitary.
  intros.
  split.
  - reflexivity.
  - unfold Qop_mmd in *.
    unfold Mget in *.
    unfold Mconjtrans in *.
    unfold Mmult in *.
    unfold Mequal in *.
    simpl in *.
    unfold Mmult_inner in *.
    unfold extract_row_unsafe in *.
    unfold extract_col_unsafe in *.
    unfold RVsize in *.
    unfold Msize in *.
    unfold MMeqbits in *.
    simpl in *.

    simpl.
    unfold Mequal in H0.
    unfold

(* ============================================================================================== *)
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

(* ============================================================================================== *)
(* single qubit projection operators ============================================================ *)

Definition Qproj0: Matrix := {|
  Mbits := 1;
  Minner := fun i j => match i, j with
    | 0, 0 => 1
    | _, _ => 0
    end;
  |}.

Definition Qproj1: Matrix := {|
  Mbits := 1;
  Minner := fun i j => match i, j with
    | 1, 1 => 1
    | _, _ => 0
    end;
  |}.

(* ============================================================================================== *)
(* generalization of single qubit operators ===================================================== *)

Definition Qop_sq (n t: nat) (op: Matrix)
  (Ht: t < n) (Hop: Mbits op = 1): {m: Matrix | Mbits m = n}.
Proof.
  destruct (eye t) as [eye1 Heye1].
  destruct (eye (n - t - 1)) as [eye2 Heye2].
  destruct (TMproduct eye1 op) as [m' Hm'].
  destruct (TMproduct m' eye2) as [m Hm].
  refine (exist _ m _).
  rewrite Hm.
  rewrite Hm'.
  rewrite Heye1.
  rewrite Heye2.
  rewrite Hop.
  replace ((t + 1 + (n - t - 1))%nat) with (((n - t - 1) + 1 + t)%nat) by lia.
  repeat rewrite Nat.sub_add.
  reflexivity. lia. lia.
Qed.

(* ============================================================================================== *)
(* swap operator ================================================================================ *)

Definition Qop_swap2: Matrix := {|
  Mbits := 2;
  Minner := fun i j => match i, j with
    | 0, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 3, 3 => 1
    | _, _ => 0
    end;
  |}.

(* Eval compute in (Minner Qop_swap2 1 2). *)

Fixpoint Qop_swap1n (n: nat) (H: n > 1): {m: Matrix | Mbits m = n}.
Proof.
  destruct (lt_eq_lt_dec n 2) as [Hn|Hn].
  - destruct Hn.
    + lia.
    + refine (exist _ Qop_swap2 _).
      simpl. lia.
  - destruct n as [|n'].
    + lia.
    + destruct n' as [|n''] eqn: Hn'n''.
      * lia.
      * destruct (eye n'') as [eyen'' Heyen''].
        destruct (eye 1) as [eye1 Heye1].
        destruct (TMproduct Qop_swap2 (eyen'')) as [swap12n H12].
        assert (n' > 1) as Hn' by lia.
        destruct (Qop_swap1n n' Hn') as [swap1n' H1n'].
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

Definition Qop_swap (n q1 q2: nat) (H1: q1 < n) (H2: q2 < n): {m: Matrix | Mbits m = n}.
Proof.
  destruct (lt_eq_lt_dec q1 q2) as [H|H].
  - destruct H as [H|H].
    + destruct (eye q1) as [eye1 Heye1].
      destruct (eye (n - q2 - 1)) as [eye2 Heye2].
      assert (q2 - q1 + 1 > 1) as Hgt by lia.
      destruct (Qop_swap1n (q2 - q1 + 1) Hgt) as [swap1n H1n].
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
    destruct (Qop_swap1n (q1 - q2 + 1) Hgt) as [swap1n H1n].
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

Definition Qop_swap_op (n q1 q2: nat) (op: Matrix)
  (H1: q1 < n) (H2: q2 < n) (Hop: Mbits op = n): {m: Matrix | Mbits m = n}.
Proof.
  destruct (Qop_swap n q1 q2 H1 H2) as [swapq1q2 Hq1q2].
  assert (MMeqbits swapq1q2 op) as Hswapop.
  { unfold MMeqbits. lia. }
  destruct (Mmult swapq1q2 op Hswapop) as [m' Hm'].
  destruct (Mmult m' swapq1q2 Hm') as [m Hm].
  refine (exist _ m _).
  rewrite Hm.
  rewrite Hm'.
  apply Hq1q2.
Defined.

(* ============================================================================================== *)
(* CNOT operator ================================================================================ *)

Definition Qop_cnot_ct: Matrix := {|
  Mbits := 2;
  Minner := fun i j => match i, j with
    | 0, 0 => 1
    | 1, 1 => 1
    | 2, 3 => 1
    | 3, 2 => 1
    | _, _ => 0
    end;
  |}.

Definition Qop_cnot_tc: Matrix := {|
  Mbits := 2;
  Minner := fun i j => match i, j with
    | 0, 1 => 1
    | 1, 0 => 1
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
    end;
  |}.

Definition Qop_cnot_ct_n (n: nat) (Hn: n >= 2): {m: Matrix | Mbits m = n}.
Proof.
  destruct (eye (n - 2)) as [eyen'' Heyen''].
  destruct (TMproduct Qop_cnot_ct eyen'') as [m Hm].
  refine (exist _ m _).
  rewrite Hm.
  rewrite Heyen''.
  simpl.
  lia.
Defined.

Definition Qop_cnot_tc_n (n: nat) (Hn: n >= 2): {m: Matrix | Mbits m = n}.
Proof.
  destruct (eye (n - 2)) as [eyen'' Heyen''].
  destruct (TMproduct Qop_cnot_tc eyen'') as [m Hm].
  refine (exist _ m _).
  rewrite Hm.
  rewrite Heyen''.
  simpl.
  lia.
Defined.

Definition Qop_cnot (n qc qt: nat) (Hn: n >= 2) (Hc: qc < n) (Ht: qt < n): {m: Matrix | Mbits m = n}.
Proof.
  assert (0 < n) as H0 by lia.
  assert (1 < n) as H1 by lia.
  destruct (Qop_cnot_ct_n n Hn) as [cnotctn Hctn].
  destruct (Qop_cnot_tc_n n Hn) as [cnottcn Htcn].
  (* qc = 0 *)
  { destruct (Nat.eq_dec qc 0) as [Hqc0|Hqc0].
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply (Qop_cnot_ct_n n Hn). }
      { apply (Qop_swap_op n 1 qt cnotctn H1 Ht Hctn). } }
  (* qc = 1 *)
  { destruct (Nat.eq_dec qc 1) as [Hqc1|Hqc1].
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply (Qop_cnot_tc_n n Hn). }
      { apply (Qop_swap_op n 0 qt cnottcn H0 Ht Htcn). } }
  (* qc = otherwise *)
  { (* qt = 0 *)
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply (Qop_swap_op n 1 qc cnottcn H1 Hc Htcn). }
    (* qt = 1 *)
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply (Qop_swap_op n 0 qc cnotctn H0 Hc Hctn). }
    (* qt = otherwise *)
    { destruct (Qop_swap_op n 0 qc cnotctn H0 Hc Hctn) as [m' Hm'].
      apply (Qop_swap_op n 1 qt m' H1 Ht Hm'). } } } } } }
Defined.

(* ============================================================================================== *)
(* quantum qubit operator ======================================================================= *)

(* Inductive Qoperator: nat -> Matrix -> Prop :=
| *)