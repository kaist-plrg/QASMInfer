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

Definition Qop_unitary (m: Matrix) := Mmult m (Mconjtrans m) (Mconjtrans_bits m) = eye (Mbits m).

Lemma Qop_eye_unitary: forall (bits: nat), Qop_unitary (eye bits).
Proof.
  intros.
  unfold Qop_unitary, Mmult.
  rewrite eye_conjtrans.
  specialize (Mmult_eye_l (eye bits)) as Heye.
  unfold Mmult in Heye.
  replace (Mbits (eye bits)) with bits in *.
  rewrite Heye.
  reflexivity.
  simpl_bits.
  reflexivity.
  simpl_bits.
  reflexivity.
Qed.

Lemma Qop_unitary_mult_suppl: forall (m1 m2: Matrix) (H12: _) (H21: _) (H1221: _),
  Mmult (Mmult m1 m2 H12) (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H1221 = eye (Mbits m1) ->
  Qop_unitary (Mmult m1 m2 H12).
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    reflexivity.
  - intros.
    specialize (Mconjtrans_mult m1 m2 H12 H21) as Hd.
    unfold Mmult in *.
    rewrite Hd.
    simpl in *.
    unfold eye in H.
    inversion H.
    assert (forall f g: nat -> nat -> C, f = g -> f i j = g i j) as Hfeq.
    { intros. rewrite H2. reflexivity. }
    apply Hfeq in H3.
    apply H3.
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
  apply Mequal.
  - unfold MMeqbits.
    repeat rewrite Mmult_bits_l.
    apply eye_bits.
  - intros.
    simpl_bits.
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
    assert (
      (Mmult m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H23) =
      (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1)) as Hassoc2.
    { apply Mequal.
      - unfold MMeqbits.
        simpl_bits.
        reflexivity.
      - intros.
        unfold Mget.
        simpl_bits.
        specialize
          (Mmult_assoc m2 (Mconjtrans m2) (Mconjtrans m1) (Mconjtrans_bits m2) H22_1 H21 H23)
          as Hassoc2.
        rewrite Hassoc2.
        reflexivity.
    }
    assert (MMeqbits m1 (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1)) as H1_22_1.
    { simpl_bits. apply H. }
    assert (
      Mmult m1 (Mmult m2 (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H23) H1_23 =
      Mmult m1 (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1) H1_22_1).
    { unfold Mmult in *.
      rewrite Hassoc2.
      reflexivity. }
    rewrite H4.
    unfold Qop_unitary in *.
    assert (MMeqbits m1 (Mmult (eye (Mbits m2)) (Mconjtrans m1) H22_1)) as H1e1.
    { simpl_bits. apply H. }
    assert (
      Mmult m1 (Mmult (Mmult m2 (Mconjtrans m2) (Mconjtrans_bits m2)) (Mconjtrans m1) H22_1) H1_22_1 =
      Mmult m1 (Mmult (eye (Mbits m2)) (Mconjtrans m1) H22_1) H1e1).
    { unfold Mmult in *.
      rewrite H1.
      reflexivity. }
    rewrite H5.
    specialize (Mmult_eye_l (Mconjtrans m1) (Mconjtrans_bits m1)) as Heye.
    simpl_bits.
    unfold Mmult in *.
    rewrite H in Heye.
    rewrite Heye.
    rewrite H0.
    reflexivity.
Qed.

Lemma Qop_unitary_TMprod: forall (m1 m2: Matrix),
  Qop_unitary m1 -> Qop_unitary m2 -> Qop_unitary (TMproduct m1 m2).
Proof.
  intros.
  unfold Qop_unitary, Mmult in *.
  rewrite TMproduct_Mconjtrans.
  specialize TMproduct_mult as Htp.
  unfold Mmult in *.
  rewrite <- Htp.
  rewrite H.
  rewrite H0.
  rewrite TMproduct_eye.
  replace (Mbits m1 + Mbits m2)%nat with (Mbits (TMproduct m1 m2)).
  reflexivity.
  simpl_bits.
  reflexivity.
  simpl_bits.
  reflexivity.
  simpl_bits.
  reflexivity.
  repeat simpl_bits.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* single qubit rotation operators ============================================================== *)

Local Open Scope R_scope.

Definition Qop_ry (theta: R): Matrix := {|
  Mbits := 1;
  Minner := fun i j =>
    if i =? 0 then if j =? 0 then cos (theta / 2) else - sin (theta / 2)
    else if j =? 0 then           sin (theta / 2) else   cos (theta / 2);
  |}.

Lemma Qop_ry_unitary: forall (theta: R), Qop_unitary (Qop_ry theta).
Proof.
  intros.
  unfold Qop_unitary.
  simpl.
  unfold Mmult.
  unfold Qop_ry.
  unfold Mconjtrans.
  unfold Mmult_unsafe.
  unfold eye.
  apply Mequal.
  - reflexivity.
  - unfold Mmult_inner.
    repeat simpl_bits.
    simpl.
    intros.
    dps_unfold.
    unfold Cconj.
    destruct i as [|i].
      + destruct j as [|j].
        * simpl.
          unfold Cmult.
          unfold Cplus.
          simpl_tri.
          specialize (sin2_cos2 (theta / 2)) as Hsc.
          unfold Rsqr in Hsc.
          lca.
        * simpl.
          unfold Cmult.
          unfold Cplus.
          simpl_tri.
          lca.
      + destruct j as [|j].
        * simpl.
          unfold Cmult.
          unfold Cplus.
          simpl_tri.
          lca.
        * assert (i = 0%nat) by lia.
          assert (j = 0%nat) by lia.
          subst i j.
          simpl.
          unfold Cmult.
          unfold Cplus.
          simpl_tri.
          specialize (sin2_cos2 (theta / 2)) as Hsc.
          unfold Rsqr in Hsc.
          lca.
Qed.


Definition Qop_rz (theta: R): Matrix := {|
  Mbits := 1;
  Minner := fun i j =>
    if i =? 0 then if j =? 0 then Cexp (0, - theta / 2) else          0
    else if j =? 0 then                     0           else Cexp (0, theta / 2);
  |}.

Lemma Qop_rz_unitary: forall (theta: R), Qop_unitary (Qop_rz theta).
Proof.
  intros.
  unfold Qop_unitary.
  simpl.
  unfold Mmult.
  unfold Qop_ry.
  unfold Mconjtrans.
  unfold Mmult_unsafe.
  unfold eye.
  apply Mequal.
  - reflexivity.
  - unfold Mmult_inner.
    repeat simpl_bits.
    simpl.
    intros.
    dps_unfold.
    unfold Cconj.
    destruct i as [|i].
      + destruct j as [|j].
        * simpl.
          unfold Cmult.
          unfold Cplus.
          repeat simpl_tri.
          specialize (sin2_cos2 (theta / 2)) as Hsc.
          unfold Rsqr in Hsc.
          lca.
        * simpl.
          unfold Cmult.
          unfold Cplus.
          simpl_tri.
          lca.
      + destruct j as [|j].
        * simpl.
          unfold Cmult.
          unfold Cplus.
          simpl_tri.
          lca.
        * assert (i = 0%nat) by lia.
          assert (j = 0%nat) by lia.
          subst i j.
          simpl.
          unfold Cmult.
          unfold Cplus.
          repeat simpl_tri.
          specialize (sin2_cos2 (theta / 2)) as Hsc.
          unfold Rsqr in Hsc.
          lca.
Qed.

Definition Qop_rot (theta phi lambda: R): Matrix.
Proof.
  refine (Mmult (Mmult (Qop_rz phi) (Qop_ry theta) _) (Qop_rz lambda) _).
  Unshelve.
  - simpl_bits.
    reflexivity.
  - simpl_bits.
    reflexivity.
Defined.

Lemma Qop_rot_unitary: forall (theta phi lambda: R), Qop_unitary (Qop_rot theta phi lambda).
Proof.
  intros.
  unfold Qop_unitary.
  apply Qop_unitary_mult.
  unfold Qop_unitary.
  apply Qop_unitary_mult.
  apply Qop_rz_unitary.
  apply Qop_ry_unitary.
  apply Qop_rz_unitary.
Qed.

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
  (Ht: t < n) (Hop: Mbits op = 1): Matrix := TMproduct (TMproduct (eye t) op) (eye (n - t - 1)).

Lemma Qop_sq_bits: forall (n t: nat) (op: Matrix) (Ht: _) (Hop: _), Mbits (Qop_sq n t op Ht Hop) = n.
Proof.
  intros.
  unfold Qop_sq.
  repeat simpl_bits.
  lia.
Qed.

Lemma Qop_sq_unitary: forall (n t: nat) (op: Matrix) (Ht: _) (Hop: _), Qop_unitary (Qop_sq n t

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