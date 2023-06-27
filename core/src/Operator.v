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


(* definition of Hermitian operation ============================================================ *)

Definition Qop_Hermitian (m: Matrix) := Mconjtrans m = m.

Lemma Msmul_Hermitian: forall (m: Matrix) (c: C),
  Qop_Hermitian m -> Cimag c = R0 -> Qop_Hermitian (Msmul c m).
Proof.
  intros.
  destruct m.
  unfold Qop_Hermitian, Msmul, Muop, Mconjtrans in *.
  inversion H.
  simpl.
  f_equal.
  apply functional_extensionality.
  intros i.
  apply functional_extensionality.
  intros j.
  assert (forall f g: nat -> nat -> C, f = g -> f i j = g i j).
  { intros.
    rewrite H1.
    reflexivity. }
  apply H1 in H2.
  rewrite <- H2.
  rewrite Cconj_twice.
  rewrite Cconj_mult.
  destruct c.
  simpl in H0.
  subst r0.
  lca.
Qed.

Lemma TMproduct_Hermitian: forall (m1 m2: Matrix),
  Qop_Hermitian m1 -> Qop_Hermitian m2 -> Qop_Hermitian (TMproduct m1 m2).
Proof.
  intros.
  unfold Qop_Hermitian.
  rewrite TMproduct_Mconjtrans.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma Qop_Hermitian_eye: forall (n: nat), Qop_Hermitian (eye n).
Proof.
  unfold Qop_Hermitian, eye.
  intros.
  apply Mequal.
  - reflexivity.
  - simpl_bits.
    simpl.
    intros.
    rewrite Nat.eqb_sym.
    destruct (Nat.eq_dec i j).
    + replace (i =? j) with true.
      subst i.
      destruct (j <? 2 ^ n).
      1-2: lca.
      symmetry; apply Nat.eqb_eq; lia.
    + replace (i =? j) with false.
      lca.
      symmetry; apply Nat.eqb_neq; lia.
Qed.

(* ============================================================================================== *)
(* definition of positive operation ============================================================= *)

Definition Qop_positive (m: Matrix) :=
  forall c Hmc Hd, Cge_0 (dot_product (CVconjtrans c) (MVmult m c Hmc) Hd).

Lemma Qop_positive_pure: forall (m: Matrix),
  (exists (qst: ColVec) (H: _), m = VVmult qst (CVconjtrans qst) H) -> Qop_positive m.
Proof.
  intros.
  destruct H as [qst [Hqst H] ].
  specialize dot_product_conjtrans as Hconj.
  unfold Qop_positive, dot_product, MVmult.
  intros.
  rewrite H.
  assert (
    dot_product_unsafe (CVconjtrans c) (MVmult_unsafe (VVmult qst (CVconjtrans qst) Hqst) c) =
    dot_product_unsafe (CVconjtrans c) qst * dot_product_unsafe (CVconjtrans qst) c
  ) as Hassoc.
  { unfold MVmult_unsafe, MVmult_inner, dot_product_unsafe, RVsize.
    simpl_bits.
    simpl.
    replace (
      (fun i : nat => dot_product_suppl (fun j : nat => CVinner qst i * Cconj (CVinner qst j)) (CVinner c) (2 ^ CVbits c))
    ) with (
      (fun i : nat => CVinner qst i * dot_product_suppl (fun j : nat => Cconj (CVinner qst j)) (CVinner c) (2 ^ CVbits c))
    ).
    rewrite dot_product_suppl_scale_r with
      (f2 := (fun i : nat => CVinner qst i))
      (c := dot_product_suppl (fun j : nat => Cconj (CVinner qst j)) (CVinner c) (2 ^ CVbits c)).
    replace (CVbits qst) with (CVbits c).
    ring_simplify.
    reflexivity.
    specialize VVmult_bits_l as Hvvb.
    apply f_equal with (f:= Mbits) in H.
    simpl_bits.
    lia.
    intros.
    lca.
    apply functional_extensionality.
    intros.
    symmetry.
    apply dot_product_suppl_scale_l.
    intros.
    lca. }
  rewrite Hassoc.
  replace c with (RVconjtrans (CVconjtrans c)).
  unfold dot_product in Hconj.
  rewrite <- Hconj.
  rewrite CRVconjtrans_twice.
  apply Cconj_mult_ge0.
  apply f_equal with (f:= Mbits) in H; repeat simpl_bits; lia.
  apply f_equal with (f:= Mbits) in H; repeat simpl_bits; lia.
  apply CRVconjtrans_twice.
Qed.

Lemma Qop_positive_plus: forall (m1 m2: Matrix) (H: _),
  Qop_positive m1 -> Qop_positive m2 -> Qop_positive (Mplus m1 m2 H).
Proof.
  repeat unfold
    Qop_positive, CVconjtrans,
    dot_product, dot_product_unsafe,
    Mplus, Mbop_unsafe,
    MVmult, MVmult_unsafe, MVmult_inner,
    RVsize, CVsize in *.
  simpl_bits.
  simpl.
  intros.
  replace (
    fun i : nat => dot_product_suppl (fun j : nat => Minner m1 i j + Minner m2 i j) (CVinner c) (2 ^ CVbits c)
  ) with (
    fun i : nat => dot_product_suppl (fun j : nat => Minner m1 i j) (CVinner c) (2 ^ CVbits c)
                 + dot_product_suppl (fun j : nat => Minner m2 i j) (CVinner c) (2 ^ CVbits c)
  ).
  rewrite dot_product_suppl_plus_r with
    (f12 := fun i : nat =>
        dot_product_suppl (fun j : nat => Minner m1 i j) (CVinner c) (2 ^ CVbits c) +
        dot_product_suppl (fun j : nat => Minner m2 i j) (CVinner c) (2 ^ CVbits c))
    (f1  := fun i : nat =>
        dot_product_suppl (fun j : nat => Minner m1 i j) (CVinner c) (2 ^ CVbits c))
    (f2 := fun i : nat =>
        dot_product_suppl (fun j : nat => Minner m2 i j) (CVinner c) (2 ^ CVbits c)).
  apply Cge_0_plus.
  apply H0.
  1-2: lia.
  apply H1.
  1-2: lia.
  intros.
  lca.
  apply functional_extensionality.
  intros i.
  rewrite dot_product_suppl_plus_l with
    (f12 := fun j : nat => Minner m1 i j + Minner m2 i j)
    (f1 := fun j : nat => Minner m1 i j)
    (f2 := fun j : nat => Minner m2 i j).
  lca.
  intros.
  lca.
Qed.

Lemma Qop_positive_diag: forall (i: nat) (m: Matrix), Qop_positive m -> i < Msize m -> Cge_0 (Minner m i i).
Proof.
  intros i m.
  unfold Qop_positive, Mtrace, dot_product, Msize, MVmult, CVconjtrans.
  repeat simpl_bits.
  simpl.
  unfold dot_product_unsafe, MVmult_unsafe, MVmult_inner.
  unfold dot_product_suppl, func_sum.
  simpl_bits.
  simpl.
  intros.
  specialize H with (c := {|CVbits := Mbits m; CVinner := fun x => if x =? i then 1 else 0|}).
  simpl in *.
  assert (Mbits m = Mbits m) as Hrf by reflexivity.
  specialize (H Hrf Hrf).
  rewrite func_sum2_split3 with (k := i) in H.
  specialize func_sum2_split3 with (n := 0) (k := i) (m := (2 ^ Mbits m)%nat) as Hsplit.
  specialize (func_sum2_zero 0) as Hzero1.
  specialize (func_sum2_zero (1 + i)) as Hzero2.
  rewrite (func_sum2_zero 0) in H.
  rewrite (func_sum2_zero (1 + i)) in H.
  unfold func_sum2 in H, Hsplit, Hzero1, Hzero2.
  replace (1 + i - i)%nat with 1 in H by lia.
  unfold func_sum_suppl at 1 in H.
  repeat rewrite Nat.add_0_r in H.
  rewrite Hsplit in H.
  rewrite Hzero1 in H.
  rewrite Hzero2 in H.
  replace (1 + i - i)%nat with 1 in H by lia.
  unfold func_sum_suppl in H.
  repeat rewrite Nat.add_0_r in H.
  repeat rewrite Cplus_0_l in H.
  repeat rewrite Cplus_0_r in H.
  replace (i =? i) with true in H.
  assert (Cconj 1 = 1) as Hone by lca.
  rewrite Hone in H.
  rewrite Cmult_1_l in H.
  rewrite Cmult_1_r in H.
  apply H.
  symmetry.
  rewrite Nat.eqb_eq.
  reflexivity.
  intros.
  assert (k =? i = false) as Hneq.
  { apply Nat.eqb_neq.
    lia. }
  rewrite Hneq.
  lca.
  intros.
  assert (k =? i = false) as Hneq.
  { apply Nat.eqb_neq.
    lia. }
  rewrite Hneq.
  lca.
  lia.
  intros.
  assert (k =? i = false) as Hneq.
  { apply Nat.eqb_neq.
    lia. }
  rewrite Hneq.
  lca.
  intros.
  assert (k =? i = false) as Hneq.
  { apply Nat.eqb_neq.
    lia. }
  rewrite Hneq.
  lca.
  lia.
Qed.

Lemma Qop_positive_trace: forall (m: Matrix), Qop_positive m -> Cge_0 (Mtrace m).
Proof.
  intros.
  unfold Mtrace, dot_product, Msize, MVmult, CVconjtrans, func_sum, func_sum2.
  apply func_sum_suppl_pos.
  intros.
  apply Qop_positive_diag.
  apply H.
  unfold Msize.
  lia.
Qed.

Lemma Qop_positive_mult_l: forall (m1 m2: Matrix) H1 H2,
  Qop_positive m1 -> Qop_positive (Mmult (Mmult (Mconjtrans m2) m1 H1) m2 H2).
Proof.
  unfold Qop_positive in *.
  intros.
  specialize Mmult_assoc as Hma.
  specialize MMVmult_assoc as Hva.
  specialize VMVmult_assoc as Hvva.
  specialize CVconjtrans_mult as Hccm.
  unfold Mmult, MVmult, dot_product in *.
  rewrite Hma.
  rewrite Hva.
  erewrite Hvva.
  rewrite Hva.
  rewrite <- Hccm.
  apply H.
  Unshelve.
  all: repeat simpl_bits; lia.
Qed.

Lemma Qop_positive_mult_r: forall (m1 m2: Matrix) H1 H2,
  Qop_positive m1 -> Qop_positive (Mmult (Mmult m2 m1 H1) (Mconjtrans m2) H2).
Proof.
  unfold Qop_positive in *.
  intros.
  specialize Mmult_assoc as Hma.
  specialize MMVmult_assoc as Hva.
  specialize VMVmult_assoc as Hvva.
  specialize CVconjtrans_mult as Hccm.
  unfold Mmult, MVmult, VMmult, dot_product in *.
  rewrite Hma.
  rewrite Hva.
  erewrite Hvva.
  rewrite Hva.
  replace m2 with (Mconjtrans (Mconjtrans m2)) at 1.
  rewrite <- Hccm.
  apply H.
  Unshelve.
  5: apply Mconjtrans_twice.
  all: repeat simpl_bits; auto; lia.
Qed.

Lemma Qop_positive_mult_Hermitian: forall (m1 m2: Matrix) H1 H2,
  Qop_positive m1 -> Qop_Hermitian m2 -> Qop_positive (Mmult (Mmult m2 m1 H1) m2 H2).
Proof.
  intros.
  unfold Mmult in *.
  assert (Mmult_unsafe m2 m1 = Mmult_unsafe (Mconjtrans m2) m1).
  { rewrite H0.
    reflexivity. }
  rewrite H3.
  eapply Qop_positive_mult_l.
  apply H.
  Unshelve.
  simpl_bits. lia.
  simpl_bits. lia.
Qed.

Lemma Qop_positive_smult: forall (m: Matrix) (c: C),
  Qop_positive m -> Cge_0 c -> Qop_positive (Msmul c m).
Proof.
  unfold Qop_positive.
  intros.
  unfold dot_product, CVconjtrans, MVmult, Msmul, Muop, dot_product_unsafe, MVmult_unsafe in *.
  simpl_bits.
  simpl in *.
  unfold MVmult_inner, extract_row_unsafe in *.
  simpl in *.
  replace (fun i : nat => dot_product_suppl (fun j : nat => c * Minner m i j) (CVinner c0) (CVsize c0)) with
  (fun i : nat => c * dot_product_suppl (fun j : nat => Minner m i j) (CVinner c0) (CVsize c0)).
  rewrite dot_product_suppl_scale_r with (c := c) (f2 := (fun i : nat => dot_product_suppl (fun j : nat => Minner m i j) (CVinner c0) (CVsize c0))).
  apply Cge_0_mult.
  apply H0.
  unfold CVsize in *.
  apply H.
  simpl_bits.
  lia.
  reflexivity.
  intros. reflexivity.
  apply functional_extensionality.
  intros.
  symmetry.
  apply dot_product_suppl_scale_l.
  intros.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* definition of unitary operation ============================================================== *)

Definition Qop_unitary_l (m: Matrix) := Mmult m (Mconjtrans m) (Mconjtrans_bits m) = eye (Mbits m).
Definition Qop_unitary_r (m: Matrix) := Mmult (Mconjtrans m) m (Mconjtrans_bits m) = eye (Mbits m).

Definition Qop_unitary (m: Matrix) := Qop_unitary_l m /\ Qop_unitary_r m.


Lemma Qop_unitary_conjtrans: forall (m: Matrix), Qop_unitary m -> Qop_unitary (Mconjtrans m).
Proof.
  intros.
  destruct H as [H1 H2].
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r, Mmult in *.
  simpl_bits.
  split.
  - rewrite Mconjtrans_twice.
    apply H2.
  - rewrite Mconjtrans_twice.
    apply H1.
Qed.

Lemma Qop_unitary_eye: forall (bits: nat), Qop_unitary (eye bits).
Proof.
  intros.
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r, Mmult.
  rewrite eye_conjtrans.
  specialize (Mmult_eye_l (eye bits)) as Heye.
  unfold Mmult in Heye.
  replace (Mbits (eye bits)) with bits in *.
  rewrite Heye.
  split.
  all: simpl_bits; reflexivity.
Qed.

Lemma Qop_unitary_mult_suppl_l: forall (m1 m2: Matrix) (H12: _) (H21: _) (H1221: _),
  Mmult (Mmult m1 m2 H12) (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) H1221 = eye (Mbits m1) ->
  Qop_unitary_l (Mmult m1 m2 H12).
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
    { intros. rewrite H0. reflexivity. }
    apply Hfeq in H1.
    apply H1.
Qed.

Lemma Qop_unitary_mult_suppl_r: forall (m1 m2: Matrix) (H12: _) (H21: _) (H1221: _),
  Mmult (Mmult (Mconjtrans m2) (Mconjtrans m1) H21) (Mmult m1 m2 H12) H1221 = eye (Mbits m1) ->
  Qop_unitary_r (Mmult m1 m2 H12).
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
    { intros. rewrite H0. reflexivity. }
    apply Hfeq in H2.
    apply H2.
Qed.

Lemma Qop_unitary_mult: forall (m1 m2: Matrix) (H: _),
  Qop_unitary m1 -> Qop_unitary m2 -> Qop_unitary (Mmult m1 m2 H).
Proof.
  intros m1 m2 H [H1l H1r] [H2l H2r].
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
  split.
  - apply (Qop_unitary_mult_suppl_l m1 m2 H H21 H1221).
    apply Mequal.
    + simpl_bits.
      reflexivity.
    + intros.
      simpl_bits.
      erewrite Mmult_assoc.
      specialize (Mmult_assoc m2) as Hassoc.
      specialize Mmult_eye_l as Heye.
      unfold Qop_unitary_l in *.
      unfold Mmult in *.
      erewrite <- Hassoc.
      rewrite H2l.
      replace (Mbits m2) with (Mbits (Mconjtrans m1)).
      erewrite Heye.
      rewrite H1l.
      reflexivity.
      all: simpl_bits; lia.
  - eapply (Qop_unitary_mult_suppl_r m1 m2 H H21).
    apply Mequal.
    + simpl_bits.
      apply H21.
    + intros.
      simpl_bits.
      erewrite Mmult_assoc.
      specialize (Mmult_assoc (Mconjtrans m1)) as Hassoc.
      specialize Mmult_eye_l as Heye.
      unfold Qop_unitary_r in *.
      unfold Mmult in *.
      erewrite <- Hassoc.
      rewrite H1r.
      rewrite H.
      erewrite Heye.
      rewrite H2r.
      reflexivity.
      all: simpl_bits; lia.
      Unshelve.
      simpl_bits.
      reflexivity.
      repeat simpl_bits.
      unfold Mmult.
      rewrite Mmult_unsafe_bits_l.
      apply H.
      simpl_bits.
      apply H21.
      simpl_bits.
      reflexivity.
      simpl_bits.
      unfold Mmult.
      rewrite Mmult_unsafe_bits_l.
      simpl_bits.
      apply H21.
Qed.

Lemma Qop_unitary_mult_unsafe: forall (m1 m2: Matrix),
  MMeqbits m1 m2 -> Qop_unitary m1 -> Qop_unitary m2 -> Qop_unitary (Mmult_unsafe m1 m2).
Proof.
  intros m1 m2.
  specialize Qop_unitary_mult as Hm.
  unfold Mmult in Hm.
  apply Hm.
Qed.

Lemma Qop_unitary_TMprod: forall (m1 m2: Matrix),
  Qop_unitary m1 -> Qop_unitary m2 -> Qop_unitary (TMproduct m1 m2).
Proof.
  intros m1 m2 [H1l H1r] [H2l H2r].
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r, Mmult in *.
  rewrite TMproduct_Mconjtrans.
  specialize TMproduct_mult as Htp.
  unfold Mmult in *.
  repeat rewrite <- Htp.
  rewrite H1l.
  rewrite H1r.
  rewrite H2l.
  rewrite H2r.
  repeat rewrite TMproduct_eye.
  simpl_bits.
  split.
  all: repeat simpl_bits; reflexivity.
Qed.

(* ============================================================================================== *)
(* single qubit rotation operators ============================================================== *)

Local Open Scope R_scope.

Definition Qop_ry (theta: R): Matrix := {|
  Mbits := 1;
  Minner := fun i j =>
    match i, j with
    | 0, 0 =>   cos (theta / 2) | 0, 1 => - sin (theta / 2)
    | 1, 0 =>   sin (theta / 2) | 1, 1 =>   cos (theta / 2)
    | _, _ => 0
    end;
  |}.

Lemma Qop_ry_unitary: forall (theta: R), Qop_unitary (Qop_ry theta).
Proof.
  intros.
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r.
  simpl.
  unfold Mmult, Qop_ry, Mconjtrans, Mmult_unsafe, eye; simpl.
  split.
  { apply Mequal_domain.
    - unfold Moutoufindex_zero.
      intros.
      destruct i as [|[|i] ], j as [|[|j] ].
      1-2, 4-5: unfold Msize in *; unfold pow_2 in *; repeat simpl in *; lia.
      all: unfold Msize, pow_2, Mmult_inner in *;
      repeat simpl_bits;
      repeat simpl in *;
      intros;
      dps_unfold;
      unfold Cconj, Cplus;
      repeat unfold func_sum_suppl;
      lca.
    - unfold Moutoufindex_zero.
      intros.
      destruct i as [|[|i] ], j as [|[|j] ].
      1-2, 4-5: unfold Msize in *; unfold pow_2 in *; repeat simpl in *; lia.
      all: simpl.
      1-4: reflexivity.
      destruct (i =? j); [reflexivity|reflexivity].
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|i] ], j as [|[|j] ].
      all: unfold Cmult, Cplus; simpl; simpl_tri; try lca.
      + specialize (sin2_cos2 (theta / 2)) as Hsc.
        unfold Rsqr in Hsc.
        lca.
      + specialize (sin2_cos2 (theta / 2)) as Hsc.
        unfold Rsqr in Hsc.
        lca.
      + destruct (i =? j); [lca|lca]. }
  { apply Mequal_domain.
    all: unfold Moutoufindex_zero, Mmult_inner, Msize, pow_2; dps_unfold; simpl.
    - intros.
      destruct H.
      + destruct i as [|[|i] ].
        all: try lia; try lca.
      + destruct j as [|[|j] ].
        all: try lia; try lca.
    - intros.
      destruct H.
      + destruct i as [|[|i] ], j as [|[|j] ].
        all: try lia; try lca.
        destruct (S (S i) =? S (S j)).
        replace (S (S i) <? 2) with false.
        all: try lca.
        symmetry; apply Nat.ltb_ge; lia.
      + destruct i as [|[|i] ], j as [|[|j] ].
        all: try lia; try lca.
        destruct (S (S i) =? S (S j)).
        replace (S (S i) <? 2) with false.
        all: try lca.
        symmetry; apply Nat.ltb_ge; lia.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|i] ], j as [|[|j] ].
      all: unfold Cmult, Cplus; simpl; simpl_tri; try lca.
      + specialize (sin2_cos2 (theta / 2)) as Hsc.
        unfold Rsqr in Hsc.
        lca.
      + specialize (sin2_cos2 (theta / 2)) as Hsc.
        unfold Rsqr in Hsc.
        lca.
      + destruct (i =? j); [lca|lca]. }
Qed.

Definition Qop_rz (theta: R): Matrix := {|
  Mbits := 1;
  Minner := fun i j =>
    if i =? 0 then if j =? 0 then Cexp (Cmake 0%R (- theta / 2)) else          0%R
    else if j =? 0 then                            0%R           else Cexp (Cmake 0%R (theta / 2));
  |}.

Lemma Qop_rz_unitary: forall (theta: R), Qop_unitary (Qop_rz theta).
Proof.
  intros.
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r.
  simpl.
  unfold Mmult, Qop_ry, Mconjtrans, Mmult_unsafe, eye.
  split.
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|i], j as [|j].
        + unfold Cmult, Cplus.
          repeat simpl_tri.
          specialize (sin2_cos2 (theta / 2%R)) as Hsc.
          unfold Rsqr in Hsc.
          simpl.
          lca.
        + unfold Cmult, Cplus.
          simpl_tri.
          lca.
        + unfold Cmult, Cplus.
          simpl_tri.
          lca.
        + assert (i = 0%nat) by lia.
          assert (j = 0%nat) by lia.
          subst i j.
          unfold Cmult, Cplus.
          repeat simpl_tri.
          specialize (sin2_cos2 (theta / 2%R)) as Hsc.
          unfold Rsqr in Hsc.
          lca. }
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|i], j as [|j].
        + unfold Cmult, Cplus.
          repeat simpl_tri.
          specialize (sin2_cos2 (theta / 2%R)) as Hsc.
          unfold Rsqr in Hsc.
          lca.
        + unfold Cmult, Cplus.
          simpl_tri.
          lca.
        + unfold Cmult, Cplus.
          simpl_tri.
          lca.
        + assert (i = 0%nat) by lia.
          assert (j = 0%nat) by lia.
          subst i j.
          unfold Cmult, Cplus.
          repeat simpl_tri.
          specialize (sin2_cos2 (theta / 2%R)) as Hsc.
          unfold Rsqr in Hsc.
          lca. }
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

Lemma Qop_rot_bits: forall (theta phi lambda: R), Mbits (Qop_rot theta phi lambda) = 1%nat.
Proof.
  intros.
  reflexivity.
Qed.

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

Lemma Qop_sq_unitary: forall (n t: nat) (op: Matrix) (Ht: _) (Hop: _), Qop_unitary op -> Qop_unitary (Qop_sq n t op Ht Hop).
Proof.
  intros n t op Ht Hop [H1 H2].
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r, Qop_sq in *.
  simpl.
  unfold Mmult.
  repeat rewrite TMproduct_Mconjtrans.
  specialize TMproduct_mult as Htm.
  specialize Qop_unitary_eye as Heye.
  specialize Mmult_eye_l as Heyel.
  specialize Mmult_eye_r as Heyer.
  unfold Qop_unitary, Mmult in *.
  repeat rewrite <- Htm.
  rewrite H1.
  rewrite H2.
  repeat rewrite Heyer.
  repeat rewrite eye_conjtrans.
  repeat rewrite Heyer.
  repeat rewrite TMproduct_eye.
  split; reflexivity.
  all: simpl_bits; reflexivity.
Qed.

Lemma Qop_sq_split_l: forall (n1 n2 t: nat) (op: Matrix) (Ht: _) (Hop: _) (Ht': t < n1),
  Qop_sq (n1 + n2) t op Ht Hop = TMproduct (Qop_sq n1 t op Ht' Hop) (eye n2).
Proof.
  intros.
  induction n2 as [|n2].
  - rewrite TMproduct_eye0_r.
    unfold Qop_sq.
    rewrite Nat.add_0_r.
    reflexivity.
  - unfold Qop_sq in *.
    replace (n1 + S n2 - t - 1)%nat with ((n1 - t - 1) + (n2 + 1))%nat by lia.
    replace (S n2)%nat with (n2 + 1)%nat by lia.
    rewrite <- (TMproduct_eye (n1 - t - 1) (n2 + 1)).
    repeat rewrite TMproduct_assoc.
    reflexivity.
Qed.

Lemma Qop_sq_split_r: forall (n1 n2 t: nat) (op: Matrix) (Ht: _) (Hop: _) (Ht'': _),
  n1 <= t -> Qop_sq (n1 + n2) t op Ht Hop = TMproduct (eye n1) (Qop_sq n2 (t - n1) op Ht'' Hop).
Proof.
  intros.
  induction n1 as [|n1].
  - simpl.
    rewrite TMproduct_eye0_l.
    unfold Qop_sq.
    rewrite Nat.sub_0_r.
    reflexivity.
  - unfold Qop_sq in *.
    replace t with ((S n1) + (t - S n1))%nat at 1 by lia.
    rewrite <- (TMproduct_eye (S n1)).
    repeat rewrite TMproduct_assoc.
    replace (S n1 + n2 - t - 1)%nat with (n2 - (t - S n1) - 1)%nat by lia.
    reflexivity.
Qed.

Definition Qop_sq_general (n t: nat) (op: Matrix) (Hop: Mbits op = 1): Matrix.
Proof.
  destruct (lt_dec t n).
  - apply (Qop_sq n t op l Hop).
  - apply (eye n).
Defined.

Lemma Qop_sq_genetal_bits: forall (n t: nat) (op: Matrix) (Hop: _), Mbits (Qop_sq_general n t op Hop) = n.
Proof.
  intros.
  unfold Qop_sq_general.
  destruct (lt_dec t n).
  - apply Qop_sq_bits.
  - apply eye_bits.
Qed.

Lemma Qop_sq_general_unitary: forall (n t: nat) (op: Matrix) (Hop: _), Qop_unitary op -> Qop_unitary (Qop_sq_general n t op Hop).
Proof.
  intros.
  unfold Qop_sq_general.
  destruct (lt_dec t n).
  - apply Qop_sq_unitary.
    apply H.
  - apply Qop_unitary_eye.
Qed.

(* ============================================================================================== *)
(* projection operators ========================================================================= *)

Definition Projection (m: Matrix) := (forall H, Mmult m m H = m) /\ Qop_Hermitian m /\ Cge_0 (Mtrace m).

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

Fact Qproj0_bits: Mbits Qproj0 = 1.
Proof. reflexivity. Qed.

Fact Qproj1_bits: Mbits Qproj1 = 1.
Proof. reflexivity. Qed.

Lemma Qproj0_mult: forall H, Mmult Qproj0 Qproj0 H = Qproj0.
Proof.
  intros.
  apply Mequal.
  - simpl_bits.
    reflexivity.
  - intros.
    simpl_bits.
    unfold Mmult, Mmult_unsafe, Mmult_inner.
    dps_unfold.
    simpl.
    rewrite Cmult_0_r.
    destruct i as [|i], j as [|j].
    all: lca.
Qed.

Lemma Qproj1_mult: forall H, Mmult Qproj1 Qproj1 H = Qproj1.
Proof.
  intros.
  apply Mequal_unsafe.
  - simpl_bits.
    reflexivity.
  - intros.
    simpl_bits.
    unfold Mmult, Mmult_unsafe, Mmult_inner.
    dps_unfold.
    simpl in *.
    rewrite Cmult_0_r.
    destruct i as [|i], j as [|j].
    lca.
    assert (j = 0) by lia; lca.
    assert (i = 0) by lia; subst i; lca.
    assert (i = 0) by lia.
    assert (j = 0) by lia.
    subst i j.
    lca.
Qed.

Lemma Qproj_sum_eye: forall H, Mplus Qproj0 Qproj1 H = eye 1.
Proof.
  intros.
  apply Mequal_unsafe.
  - simpl_bits.
    reflexivity.
  - intros.
    simpl_bits.
    simpl in *.
    unfold Mplus, Mbop_unsafe, Qproj0, Qproj1, eye.
    simpl.
    destruct i as [|i], j as [|j].
    + lca.
    + lca.
    + assert (i = 0) by lia.
      subst i.
      lca.
    + assert (i = 0) by lia.
      assert (j = 0) by lia.
      subst i j.
      lca.
Qed.

Lemma Qproj0_Hermitian: Qop_Hermitian Qproj0.
Proof.
  unfold Qop_Hermitian, Mconjtrans, Qproj0.
  simpl.
  apply Mequal.
  - reflexivity.
  - simpl_bits.
    simpl.
    intros.
    destruct i as [|i], j as [|j].
    all: lca.
Qed.

Lemma Qproj1_Hermitian: Qop_Hermitian Qproj1.
Proof.
  unfold Qop_Hermitian, Mconjtrans, Qproj1.
  simpl.
  apply Mequal_unsafe.
  - reflexivity.
  - simpl_bits.
    simpl.
    intros.
    destruct i as [|i], j as [|j].
    lca.
    assert (j = 0) by lia; subst j; lca.
    assert (i = 0) by lia; subst i; lca.
    assert (j = 0) by lia; subst j;
    assert (i = 0) by lia; subst i; lca.
Qed.

Lemma Qproj0_pure: exists (qst: ColVec) (H: _), Qproj0 = VVmult qst (CVconjtrans qst) H.
Proof.
  intros.
  exists {| CVbits := 1; CVinner := fun x => 1 - x |}.
  assert (CReqbits {| CVbits := 1; CVinner := fun x : nat => 1 - x |}
    (CVconjtrans {| CVbits := 1; CVinner := fun x : nat => 1 - x |})) as H0.
  { simpl_bits; reflexivity. }
  exists H0.
  unfold eye, VVmult, VVmult_unsafe, CVconjtrans.
  simpl.
  apply Mequal_unsafe.
  - reflexivity.
  - intros.
    simpl_bits.
    simpl in *.
    destruct i as [|[|i] ], j as [|[|j] ].
    all: try lca; lia.
Qed.

Lemma Qproj1_pure: exists (qst: ColVec) (H: _), Qproj1 = VVmult qst (CVconjtrans qst) H.
Proof.
  intros.
  exists {| CVbits := 1; CVinner := fun x => x |}.
  assert (CReqbits {| CVbits := 1; CVinner := fun x : nat => x |}
    (CVconjtrans {| CVbits := 1; CVinner := fun x : nat => x |})) as H0.
  { simpl_bits; reflexivity. }
  exists H0.
  unfold eye, VVmult, VVmult_unsafe, CVconjtrans.
  simpl.
  apply Mequal_unsafe.
  - reflexivity.
  - intros.
    simpl_bits.
    simpl in *.
    destruct i as [|[|i] ], j as [|[|j] ].
    all: try lca; lia.
Qed.

Lemma Qproj0_proj: Projection Qproj0.
Proof.
  split; [|split].
  - intros.
    apply Qproj0_mult.
  - intros.
    apply Qproj0_Hermitian.
  - unfold Mtrace, Qproj0.
    unfold func_sum, func_sum2.
    repeat unfold func_sum_suppl.
    simpl.
    split; [simpl;lra|simpl;lra].
Qed.

Lemma Qproj1_proj: Projection Qproj1.
Proof.
  split; [|split].
  - intros.
    apply Qproj1_mult.
  - intros.
    apply Qproj1_Hermitian.
  - unfold Mtrace, Qproj1.
    unfold func_sum, func_sum2.
    repeat unfold func_sum_suppl.
    simpl.
    split; [simpl;lra|simpl;lra].
Qed.

Definition Qproj0_n_t (n t: nat) (Ht: t < n) := Qop_sq n t Qproj0 Ht Qproj0_bits.

Definition Qproj1_n_t (n t: nat) (Ht: t < n) := Qop_sq n t Qproj1 Ht Qproj1_bits.

Lemma Qproj0_n_t_bits: forall (n t: nat) (Ht: _), Mbits (Qproj0_n_t n t Ht) = n.
Proof.
  intros.
  unfold Qproj0_n_t.
  apply Qop_sq_bits.
Qed.

Lemma Qproj1_n_t_bits: forall (n t: nat) (Ht: _), Mbits (Qproj1_n_t n t Ht) = n.
Proof.
  intros.
  unfold Qproj1_n_t.
  apply Qop_sq_bits.
Qed.

Lemma Qproj0_n_t_mult: forall (n t: nat) (Ht1 Ht2 Ht: _) (H: _),
  Mmult (Qproj0_n_t n t Ht1) (Qproj0_n_t n t Ht2) H = (Qproj0_n_t n t Ht).
Proof.
  intros.
  unfold Qproj0_n_t, Qproj1_n_t, Qop_sq in *.
  repeat erewrite <- TMproduct_mult.
  repeat rewrite Mmult_eye_r.
  rewrite Qproj0_mult.
  reflexivity.
  Unshelve.
  all: simpl_bits; reflexivity.
Qed.

Lemma Qproj1_n_t_mult: forall (n t: nat) (Ht1 Ht2 Ht: _) (H: _),
  Mmult (Qproj1_n_t n t Ht1) (Qproj1_n_t n t Ht2) H = (Qproj1_n_t n t Ht).
Proof.
  intros.
  unfold Qproj0_n_t, Qproj1_n_t, Qop_sq in *.
  repeat erewrite <- TMproduct_mult.
  repeat rewrite Mmult_eye_r.
  rewrite Qproj1_mult.
  reflexivity.
  Unshelve.
  all: simpl_bits; reflexivity.
Qed.

Lemma Qproj_n_sum_eye: forall (n t: nat) (Ht1 Ht2: _) (H01: _),
  Mplus (Qproj0_n_t n t Ht1) (Qproj1_n_t n t Ht2) H01 = eye n.
Proof.
  intros.
  unfold Qproj0_n_t, Qproj1_n_t, Qop_sq in *.
  erewrite TMproduct_plus_l.
  erewrite TMproduct_plus_r.
  rewrite Qproj_sum_eye.
  repeat rewrite TMproduct_eye.
  replace (t + 1 + (n - t - 1))%nat with n by lia.
  reflexivity.
  Unshelve.
  all: repeat simpl_bits; reflexivity.
Qed.

Lemma Qproj_eye_minus_0n: forall (n t: nat) (Ht: _) (Hminus: _),
  Qproj1_n_t n t Ht = Mminus (eye n) (Qproj0_n_t n t Ht) Hminus.
Proof.
  intros.
  eapply Mplus_Mminus_eq_l.
  erewrite Mplus_comm.
  eapply Qproj_n_sum_eye.
  Unshelve.
  all: simpl_bits; reflexivity.
Qed.

Lemma Qproj0_n_t_Hermitian: forall (n t: nat) (Ht: _), Qop_Hermitian (Qproj0_n_t n t Ht).
Proof.
  intros.
  specialize Qproj0_Hermitian as H0.
  unfold Qop_Hermitian, Qproj0_n_t, Qop_sq in *.
  repeat rewrite TMproduct_Mconjtrans.
  repeat rewrite Qop_Hermitian_eye.
  rewrite H0.
  reflexivity.
Qed.

Lemma Qproj1_n_t_Hermitian: forall (n t: nat) (Ht: _), Qop_Hermitian (Qproj1_n_t n t Ht).
Proof.
  intros.
  specialize Qproj1_Hermitian as H1.
  unfold Qop_Hermitian, Qproj1_n_t, Qop_sq in *.
  repeat rewrite TMproduct_Mconjtrans.
  repeat rewrite Qop_Hermitian_eye.
  rewrite H1.
  reflexivity.
Qed.

Lemma Qproj0_n_t_proj: forall (n t: nat) (Ht: _), Projection (Qproj0_n_t n t Ht).
Proof.
  intros.
  split; [|split].
  - intros.
    apply Qproj0_n_t_mult.
  - intros.
    apply Qproj0_n_t_Hermitian.
  - intros.
    unfold Qproj0_n_t, Qop_sq.
    repeat rewrite TMproduct_trace.
    repeat apply Cge_0_mult.
    apply eye_trace_pos.
    specialize Qproj0_proj as [_ [_ H] ].
    apply H.
    apply eye_trace_pos.
Qed.

Lemma Qproj1_n_t_proj: forall (n t: nat) (Ht: _), Projection (Qproj1_n_t n t Ht).
Proof.
  intros.
  split; [|split].
  - intros.
    apply Qproj1_n_t_mult.
  - intros.
    apply Qproj1_n_t_Hermitian.
  - intros.
    unfold Qproj1_n_t, Qop_sq.
    repeat rewrite TMproduct_trace.
    repeat apply Cge_0_mult.
    apply eye_trace_pos.
    specialize Qproj1_proj as [_ [_ H] ].
    apply H.
    apply eye_trace_pos.
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

Lemma Qop_swap2_unitary: Qop_unitary Qop_swap2.
Proof.
  intros.
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r.
  simpl.
  unfold Mmult, Qop_ry, Mconjtrans, Mmult_unsafe, eye.
  split.
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|[|i] ] ], j as [|[|[|j] ] ].
      1-3,5-7,9-11: simpl; unfold Cmult; simpl; unfold Cplus; repeat simpl_tri; lca.
      1-3: assert (j = 0%nat) by lia; subst j; unfold Cmult; unfold Cplus; simpl; repeat simpl_tri; lca.
      1-3: assert (i = 0%nat) by lia; subst i; unfold Cmult; unfold Cplus; simpl; repeat simpl_tri; lca.
      assert (i = 0%nat) by lia; assert (j = 0%nat) by lia.
      subst i j. unfold Cmult; unfold Cplus; simpl. repeat simpl_tri. lca. }
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|[|i] ] ], j as [|[|[|j] ] ].
      1-3,5-7,9-11: simpl; unfold Cmult; simpl; unfold Cplus; repeat simpl_tri; lca.
      1-3: assert (j = 0%nat) by lia; subst j; unfold Cmult; unfold Cplus; simpl; repeat simpl_tri; lca.
      1-3: assert (i = 0%nat) by lia; subst i; unfold Cmult; unfold Cplus; simpl; repeat simpl_tri; lca.
      assert (i = 0%nat) by lia; assert (j = 0%nat) by lia.
      subst i j. unfold Cmult; unfold Cplus; simpl. repeat simpl_tri. lca. }
Qed.

Fixpoint Qop_swap1n_suppl (n'': nat): Matrix := match n'' with
  | O => Qop_swap2
  | S n''' => (Mmult_unsafe
      (Mmult_unsafe
        (TMproduct Qop_swap2 (eye n''))
        (TMproduct (eye 1) (Qop_swap1n_suppl n''')))
      (TMproduct Qop_swap2 (eye n'')))
end.

Lemma Qop_swap1n_suppl_bits: forall (n'': nat), Mbits (Qop_swap1n_suppl n'') = (2 + n'')%nat.
Proof.
  destruct n'' as [|n'''].
  - reflexivity.
  - reflexivity.
Qed.

Definition Qop_swap1n (n: nat) (H: n > 1): Matrix.
Proof.
  destruct n as [|n'] eqn: En.
  exact (eye 0).
  destruct n' as [|n''] eqn: En'.
  exact (eye 1).
  exact (Qop_swap1n_suppl n'').
Defined.

Lemma Qop_swap1n_bits: forall (n: nat) (H: _), Mbits (Qop_swap1n n H) = n.
Proof.
  destruct n as [|[|[|n ] ] ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma Qop_swap1n_unitary: forall (n: nat) (H: _), Qop_unitary (Qop_swap1n n H).
Proof.
  unfold Qop_swap1n.
  destruct n as [|[|n] ].
  - lia.
  - lia.
  - induction n.
    + intros.
      simpl.
      apply Qop_swap2_unitary.
    + assert (S (S n) > 1) as Hssn by lia.
      specialize (IHn Hssn).
      intros.
      unfold Mmult.
      simpl in *.
      apply Qop_unitary_mult_unsafe.
      simpl_bits.
      reflexivity.
      apply Qop_unitary_mult_unsafe.
      simpl_bits.
      simpl.
      rewrite Qop_swap1n_suppl_bits.
      reflexivity.
      apply Qop_unitary_TMprod.
      apply Qop_swap2_unitary.
      apply Qop_unitary_eye.
      apply Qop_unitary_TMprod.
      apply Qop_unitary_eye.
      apply IHn.
      apply Qop_unitary_TMprod.
      apply Qop_swap2_unitary.
      apply Qop_unitary_eye.
Qed.

Definition Qop_swap (n q1 q2: nat) (H1: q1 < n) (H2: q2 < n): Matrix.
Proof.
  destruct (lt_eq_lt_dec q1 q2) as [ [H|H]|H].
  - assert (q2 - q1 + 1 > 1) as Hgt by lia.
    exact (TMproduct (TMproduct (eye q1) (Qop_swap1n (q2 - q1 + 1) Hgt)) (eye (n - q2 - 1))).
  - apply (eye n).
  - assert (q1 - q2 + 1 > 1) as Hgt by lia.
    apply (TMproduct (TMproduct (eye q2) (Qop_swap1n (q1 - q2 + 1) Hgt)) (eye (n - q1 - 1))).
Defined.

Lemma Qop_swap_bits: forall (n q1 q2: nat) (H1: _) (H2: _), Mbits (Qop_swap n q1 q2 H1 H2) = n.
Proof.
  intros.
  unfold Qop_swap.
  destruct (lt_eq_lt_dec q1 q2) as [ [H|H]|H].
  - simpl.
    rewrite Qop_swap1n_bits.
    lia.
  - reflexivity.
  - simpl.
    rewrite Qop_swap1n_bits.
    lia.
Qed.

Lemma Qop_swap_unitary: forall (n q1 q2: nat) (H1: _) (H2: _), Qop_unitary (Qop_swap n q1 q2 H1 H2).
Proof.
  intros.
  unfold Qop_swap.
  destruct (lt_eq_lt_dec q1 q2) as [ [H|H]|H].
  - simpl.
    repeat apply Qop_unitary_TMprod.
    apply Qop_unitary_eye.
    apply Qop_swap1n_unitary.
    apply Qop_unitary_eye.
  - apply Qop_unitary_eye.
  - simpl.
    repeat apply Qop_unitary_TMprod.
    apply Qop_unitary_eye.
    apply Qop_swap1n_unitary.
    apply Qop_unitary_eye.
Qed.

Definition Qop_swap_op (n q1 q2: nat) (op: Matrix)
  (H1: q1 < n) (H2: q2 < n) (Hop: Mbits op = n): Matrix.
Proof.
  assert (MMeqbits (Qop_swap n q1 q2 H1 H2) op) as Hswapop.
  { unfold MMeqbits.
    rewrite Qop_swap_bits.
    lia. }
  assert (MMeqbits (Mmult (Qop_swap n q1 q2 H1 H2) op Hswapop) (Qop_swap n q1 q2 H1 H2)) as Hm'.
  { simpl_bits.
    reflexivity. }
  exact (Mmult (Mmult (Qop_swap n q1 q2 H1 H2) op Hswapop) (Qop_swap n q1 q2 H1 H2) Hm').
Defined.

Lemma Qop_swap_op_bits: forall (n q1 q2: nat) (op: Matrix) (H1: _) (H2: _) (Hop: _),
  Mbits (Qop_swap_op n q1 q2 op H1 H2 Hop) = n.
Proof.
  intros.
  unfold Qop_swap_op, Mmult.
  simpl_bits.
  apply Qop_swap_bits.
Qed.

Lemma Qop_swap_op_unitary: forall (n q1 q2: nat) (op: Matrix) (H1: _) (H2: _) (Hop: _),
  Qop_unitary op -> Qop_unitary (Qop_swap_op n q1 q2 op H1 H2 Hop).
Proof.
  intros.
  unfold Qop_swap_op, Mmult.
  repeat apply Qop_unitary_mult_unsafe.
  simpl_bits.
  reflexivity.
  unfold MMeqbits.
  rewrite Qop_swap_bits.
  symmetry.
  apply Hop.
  apply Qop_swap_unitary.
  apply H.
  apply Qop_swap_unitary.
Qed.

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

Lemma Qop_cnot_ct_unitary: Qop_unitary Qop_cnot_ct.
Proof.
  intros.
  unfold Qop_unitary, Qop_unitary_l, Qop_unitary_r.
  simpl.
  unfold Mmult, Qop_ry, Mconjtrans, Mmult_unsafe, eye.
  split.
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|[|i] ] ], j as [|[|[|j] ] ].
      1-3,5-7,9-11: unfold Cmult, Cplus; repeat simpl_tri; lca.
      1-3: assert (j = 0%nat) by lia; subst j; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      1-3: assert (i = 0%nat) by lia; subst i; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      assert (i = 0%nat) by lia; assert (j = 0%nat) by lia.
      subst i j. unfold Cmult, Cplus. repeat simpl_tri. lca. }
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|[|i] ] ], j as [|[|[|j] ] ].
      1-3,5-7,9-11: unfold Cmult, Cplus; repeat simpl_tri; lca.
      1-3: assert (j = 0%nat) by lia; subst j; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      1-3: assert (i = 0%nat) by lia; subst i; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      assert (i = 0%nat) by lia; assert (j = 0%nat) by lia.
      subst i j. unfold Cmult, Cplus. repeat simpl_tri. lca. }
Qed.

Lemma Qop_cnot_tc_unitary: Qop_unitary Qop_cnot_tc.
Proof.
  intros.
  unfold Qop_unitary.
  simpl.
  unfold Mmult, Qop_ry, Mconjtrans, Mmult_unsafe, eye.
  split.
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|[|i] ] ], j as [|[|[|j] ] ].
      1-3,5-7,9-11: unfold Cmult, Cplus; repeat simpl_tri; lca.
      1-3: assert (j = 0%nat) by lia; subst j; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      1-3: assert (i = 0%nat) by lia; subst i; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      assert (i = 0%nat) by lia; assert (j = 0%nat) by lia.
      subst i j. unfold Cmult, Cplus. repeat simpl_tri. lca. }
  { apply Mequal_unsafe.
    - reflexivity.
    - unfold Mmult_inner.
      repeat simpl_bits.
      simpl.
      intros.
      dps_unfold.
      unfold Cconj.
      destruct i as [|[|[|i] ] ], j as [|[|[|j] ] ].
      1-3,5-7,9-11: unfold Cmult, Cplus; repeat simpl_tri; lca.
      1-3: assert (j = 0%nat) by lia; subst j; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      1-3: assert (i = 0%nat) by lia; subst i; unfold Cmult, Cplus; simpl; repeat simpl_tri; lca.
      assert (i = 0%nat) by lia; assert (j = 0%nat) by lia.
      subst i j. unfold Cmult, Cplus. repeat simpl_tri. lca. }
Qed.

Definition Qop_cnot_ct_n (n: nat): Matrix.
Proof.
  destruct n as [|[|n''] ].
  - exact (eye 0).
  - exact (eye 1).
  - exact (TMproduct Qop_cnot_ct (eye n'')).
Defined.

Lemma Qop_cnot_ct_n_bits: forall (n: nat), Mbits (Qop_cnot_ct_n n) = n.
Proof.
  destruct n as [|[|n''] ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma Qop_cnot_ct_n_unitary: forall (n: nat), Qop_unitary (Qop_cnot_ct_n n).
Proof.
  unfold Qop_cnot_ct_n.
  destruct n as [|[|n''] ].
  - apply Qop_unitary_eye.
  - apply Qop_unitary_eye.
  - apply Qop_unitary_TMprod.
    apply Qop_cnot_ct_unitary.
    apply Qop_unitary_eye.
Qed.

Definition Qop_cnot_tc_n (n: nat): Matrix.
Proof.
  destruct n as [|[|n''] ].
  - exact (eye 0).
  - exact (eye 1).
  - exact (TMproduct Qop_cnot_tc (eye n'')).
Defined.

Lemma Qop_cnot_tc_n_bits: forall (n: nat), Mbits (Qop_cnot_tc_n n) = n.
Proof.
  destruct n as [|[|n''] ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma Qop_cnot_tc_n_unitary: forall (n: nat), Qop_unitary (Qop_cnot_tc_n n).
Proof.
  unfold Qop_cnot_tc_n.
  destruct n as [|[|n''] ].
  - apply Qop_unitary_eye.
  - apply Qop_unitary_eye.
  - apply Qop_unitary_TMprod.
    apply Qop_cnot_tc_unitary.
    apply Qop_unitary_eye.
Qed.

Definition Qop_cnot (n qc qt: nat) (Hn: n >= 2) (Hc: qc < n) (Ht: qt < n): Matrix.
Proof.
  assert (0 < n) as H0 by lia.
  assert (1 < n) as H1 by lia.
  { destruct (Nat.eq_dec qc 0) as [Hqc0|Hqc0].
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply (Qop_cnot_ct_n n). }
      { apply (Qop_swap_op n 1 qt (Qop_cnot_ct_n n) H1 Ht (Qop_cnot_ct_n_bits n)). } }
  (* qc = 1 *)
  { destruct (Nat.eq_dec qc 1) as [Hqc1|Hqc1].
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply (Qop_cnot_tc_n n). }
      { apply (Qop_swap_op n 0 qt (Qop_cnot_tc_n n) H0 Ht (Qop_cnot_tc_n_bits n)). } }
  (* qc = otherwise *)
  { (* qt = 0 *)
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply (Qop_swap_op n 1 qc (Qop_cnot_tc_n n) H1 Hc (Qop_cnot_tc_n_bits n)). }
    (* qt = 1 *)
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply (Qop_swap_op n 0 qc (Qop_cnot_ct_n n) H0 Hc (Qop_cnot_ct_n_bits n)). }
    (* qt = otherwise *)
    { refine (
        Qop_swap_op n 1 qt (
          Qop_swap_op n 0 qc ( Qop_cnot_ct_n n) H0 Hc (Qop_cnot_ct_n_bits n)) H1 Ht _
          ).
      apply Qop_swap_op_bits.
    } } } } } }
Defined.

Lemma Qop_cnot_bits: forall (n qc qt: nat) (Hn: _) (Hc: _) (Ht: _),
  Mbits (Qop_cnot n qc qt Hn Hc Ht) = n.
Proof.
  intros.
  unfold Qop_cnot.
  { destruct (Nat.eq_dec qc 0) as [Hqc0|Hqc0].
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply Qop_cnot_ct_n_bits. }
      { apply Qop_swap_op_bits. } }
  (* qc = 1 *)
  { destruct (Nat.eq_dec qc 1) as [Hqc1|Hqc1].
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply Qop_cnot_tc_n_bits. }
      { apply Qop_swap_op_bits. } }
  (* qc = otherwise *)
  { (* qt = 0 *)
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply Qop_swap_op_bits. }
    (* qt = 1 *)
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply Qop_swap_op_bits. }
    (* qt = otherwise *)
    { apply Qop_swap_op_bits. } } } } } }
Qed.

Lemma Qop_cnot_unitary: forall (n qc qt: nat) (Hn: _) (Hc: _) (Ht: _),
  Qop_unitary (Qop_cnot n qc qt Hn Hc Ht).
Proof.
  intros.
  unfold Qop_cnot.
  { destruct (Nat.eq_dec qc 0) as [Hqc0|Hqc0].
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply Qop_cnot_ct_n_unitary. }
      { apply Qop_swap_op_unitary.
        apply Qop_cnot_ct_n_unitary. } }
  (* qc = 1 *)
  { destruct (Nat.eq_dec qc 1) as [Hqc1|Hqc1].
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply Qop_cnot_tc_n_unitary. }
      { apply Qop_swap_op_unitary.
        apply Qop_cnot_tc_n_unitary. } }
  (* qc = otherwise *)
  { (* qt = 0 *)
    { destruct (Nat.eq_dec qt 0) as [Hqt0|Hqt0].
      { apply Qop_swap_op_unitary.
        apply Qop_cnot_tc_n_unitary. }
    (* qt = 1 *)
    { destruct (Nat.eq_dec qt 1) as [Hqt1|Hqt1].
      { apply Qop_swap_op_unitary.
        apply Qop_cnot_ct_n_unitary. }
    (* qt = otherwise *)
    { repeat apply Qop_swap_op_unitary.
      apply Qop_cnot_ct_n_unitary. } } } } } }
Qed.

Definition Qop_cnot_general (n qc qt: nat): Matrix.
Proof.
  destruct (ge_dec n 2), (lt_dec qc n), (lt_dec qt n).
  apply (Qop_cnot n qc qt g l l0).
  all: apply (eye n).
Defined.

Lemma Qop_cnot_general_bits: forall (n qc qt: nat), Mbits (Qop_cnot_general n qc qt) = n.
Proof.
  intros.
  unfold Qop_cnot_general.
  destruct (ge_dec n 2), (lt_dec qc n), (lt_dec qt n).
  apply Qop_cnot_bits.
  all: apply eye_bits.
Qed.

Lemma Qop_cnot_general_unitary: forall (n qc qt: nat), Qop_unitary (Qop_cnot_general n qc qt).
Proof.
  intros.
  unfold Qop_cnot_general.
  destruct (ge_dec n 2), (lt_dec qc n), (lt_dec qt n).
  apply Qop_cnot_unitary.
  all: apply Qop_unitary_eye.
Qed.

(* ============================================================================================== *)
(* quantum qubit operator ======================================================================= *)

Inductive Qoperator: nat -> Matrix -> Prop :=
| Qoperator_single (n t: nat) (theta phi lambda: R) (H1: _) (H2: _): Qoperator n (Qop_sq n t (Qop_rot theta phi lambda) H1 H2)
| Qoperator_cnot (n qc qt: nat) (Hn: _) (Hc: _) (Ht: _): Qoperator n (Qop_cnot n qc qt Hn Hc Ht)
| Qoperator_seq (n: nat) (Qop1 Qop2: Matrix) (Heq: _): Qoperator n Qop1 -> Qoperator n Qop2 -> Qoperator n (Mmult Qop1 Qop2 Heq).

Lemma Qoperator_unitary: forall (n: nat) (qop: Matrix),
  Qoperator n qop -> Qop_unitary qop.
Proof.
  intros.
  induction H.
  - apply Qop_sq_unitary.
    apply Qop_rot_unitary.
  - apply Qop_cnot_unitary.
  - apply Qop_unitary_mult.
    apply IHQoperator1.
    apply IHQoperator2.
Qed.

