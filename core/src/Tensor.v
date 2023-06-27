Require Export Matrix.
Import ListNotations.

Declare Scope T_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.


(* tensor product of matrices =================================================================== *)

Definition TMproduct (m1 m2: Matrix): Matrix :=
  {|
    Mbits := Mbits m1 + Mbits m2;
    Minner := fun i j => Cmult (
      Minner m1 (i / Msize m2) (j / Msize m2)
    ) (
      Minner m2 (i mod Msize m2) (j mod Msize m2)
    )
  |}.

Lemma TMproduct_bits: forall (m1 m2: Matrix), Mbits (TMproduct m1 m2) = (Mbits m1 + Mbits m2)%nat.
Proof. reflexivity. Qed.

Property TMproduct_correct: forall
  (m1 m2 mt: Matrix) (i j: nat) (Hi: _) (Hj: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  (TMproduct m1 m2)[[i Hi|j Hj]] =
  m1[[(i / Msize m2) H1i|(j / Msize m2) H1j]] * m2[[(i mod Msize m2) H2i|(j mod Msize m2) H2j]].
Proof.
  unfold Mget. simpl.
  unfold TMproduct. simpl.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma TMproduct_assoc: forall (m1 m2 m3: Matrix),
  TMproduct (TMproduct m1 m2) m3 = TMproduct m1 (TMproduct m2 m3).
Proof.
  intros.
  apply Mequal.
  - repeat rewrite TMproduct_bits.
    lia.
  - unfold TMproduct, Msize, pow_2; simpl.
    specialize (pow_2_nonzero (Mbits m2)) as Hpow_m2.
    specialize (pow_2_nonzero (Mbits m3)) as Hpow_m3.
    intros.
    replace (2 ^ (Mbits m2 + Mbits m3))%nat with (2 ^ (Mbits m2) * 2 ^ (Mbits m3))%nat.
    repeat rewrite div_dist.
    repeat rewrite div_mod_mult.
    repeat rewrite <- mod_mult_mod.
    replace (2 ^ (Mbits m2) * 2 ^ (Mbits m3))%nat with (2 ^ (Mbits m3) * 2 ^ (Mbits m2))%nat.
    lca.
    1-7: lia.
    symmetry.
    apply Nat.pow_add_r.
Qed.

Lemma TMproduct_trace: forall (m1 m2: Matrix), Mtrace (TMproduct m1 m2) = Mtrace m1 * Mtrace m2.
Proof.
  intros.
  unfold TMproduct, Mtrace, Msize, pow_2.
  simpl.
  rewrite <- func_sum_dist.
  rewrite Nat.pow_add_r.
  reflexivity.
  specialize (pow_2_nonzero (Mbits m2)) as Hpow.
  lia.
Qed.

(* ============================================================================================== *)
(* tensor product of vectors ==================================================================== *)

Definition TRVproduct (r1 r2: RowVec): RowVec :=
  {|
    RVbits := RVbits r1 + RVbits r2;
    RVinner := fun j => Cmult (
      RVinner r1 (j / RVsize r2)
    ) (
      RVinner r2 (j mod RVsize r2)
    )
  |}.

Lemma TRVproduct_bits: forall (r1 r2: RowVec), RVbits (TRVproduct r1 r2) = (RVbits r1 + RVbits r2)%nat.
Proof. reflexivity. Qed.

Definition TCVproduct (c1 c2: ColVec): ColVec :=
  {|
    CVbits := CVbits c1 + CVbits c2;
    CVinner := fun i => Cmult (
      CVinner c1 (i / CVsize c2)
    ) (
      CVinner c2 (i mod CVsize c2)
    )
  |}.

Lemma TCVproduct_bits: forall (c1 c2: ColVec), CVbits (TCVproduct c1 c2) = (CVbits c1 + CVbits c2)%nat.
Proof. reflexivity. Qed.

Lemma TRVproduct_conjtrans: forall (r1 r2: RowVec),
  RVconjtrans (TRVproduct r1 r2) = TCVproduct (RVconjtrans r1) (RVconjtrans r2).
Proof.
  intros.
  apply CVequal.
  - rewrite RVconjtrans_bits.
    rewrite TRVproduct_bits.
    rewrite TCVproduct_bits.
    repeat rewrite RVconjtrans_bits.
    reflexivity.
  - intros.
    unfold RVconjtrans, TCVproduct, TRVproduct, RVsize, CVsize.
    simpl.
    apply Cconj_mult.
Qed.

Lemma TCVproduct_conjtrans: forall (c1 c2: ColVec),
  CVconjtrans (TCVproduct c1 c2) = TRVproduct (CVconjtrans c1) (CVconjtrans c2).
Proof.
  intros.
  apply RVequal.
  - rewrite CVconjtrans_bits.
    rewrite TCVproduct_bits.
    rewrite TRVproduct_bits.
    repeat rewrite CVconjtrans_bits.
    reflexivity.
  - intros.
    unfold CVconjtrans, TCVproduct, TRVproduct, RVsize, CVsize.
    simpl.
    apply Cconj_mult.
Qed.

(* ============================================================================================== *)
(* tactic of simplifying bits =================================================================== *)

Ltac simpl_bits :=
  unfold MMeqbits, MCeqbits, MReqbits in *;
  unfold RMeqbits, RCeqbits, RReqbits in *;
  unfold CMeqbits, CCeqbits, CReqbits in *;
  unfold Msize, RVsize, CVsize, pow_2 in *;
  repeat rewrite MVmult_bits_l in *;
  repeat rewrite MVmult_unsafe_bits_l in *;
  repeat rewrite VMmult_bits_r in *;
  repeat rewrite VVmult_bits_l in *;
  repeat rewrite CVconjtrans_bits in *;
  repeat rewrite RVconjtrans_bits in *;
  repeat rewrite Msmul_bits in *;
  repeat rewrite Mmult_unsafe_bits_l in *;
  repeat rewrite Mmult_bits_l in *;
  repeat rewrite Mplus_bits_l in *;
  repeat rewrite Mminus_bits_l in *;
  repeat rewrite Mbop_unsafe_bits_l in *;
  repeat rewrite Mconjtrans_bits in *;
  repeat rewrite eye_bits in *;
  repeat rewrite TRVproduct_bits in *;
  repeat rewrite TCVproduct_bits in *;
  repeat rewrite TMproduct_bits in *.

(* ============================================================================================== *)
(* relation between conjugate transpose and tensor product ====================================== *)

Lemma TMproduct_Mconjtrans: forall (m1 m2: Matrix),
  Mconjtrans (TMproduct m1 m2) = TMproduct (Mconjtrans m1) (Mconjtrans m2).
Proof.
  intros.
  unfold Mconjtrans, TMproduct.
  simpl.
  apply Mequal_unsafe.
  - reflexivity.
  - unfold Msize, pow_2, Cconj.
    simpl.
    rewrite Nat.pow_add_r.
    intros.
    lca.
Qed.

Lemma TRVproduct_RVconjtrans: forall (r1 r2: RowVec),
  RVconjtrans (TRVproduct r1 r2) = TCVproduct (RVconjtrans r1) (RVconjtrans r2).
Proof.
  intros.
  unfold RVconjtrans, TRVproduct.
  simpl.
  apply CVequal.
  - reflexivity.
  - repeat (simpl_bits; simpl).
    unfold Cconj.
    intros.
    lca.
Qed.

Lemma TCVproduct_CVconjtrans: forall (c1 c2: ColVec),
  CVconjtrans (TCVproduct c1 c2) = TRVproduct (CVconjtrans c1) (CVconjtrans c2).
Proof.
  intros.
  unfold CVconjtrans, TCVproduct.
  simpl.
  apply RVequal.
  - reflexivity.
  - repeat (simpl_bits; simpl).
    unfold Cconj.
    intros.
    lca.
Qed.

(* ============================================================================================== *)
(* relation between matric addition and tensor product ========================================== *)

Lemma TMproduct_plus_l: forall (m1 m2 m3: Matrix) (H12: _) (H1323: _),
  Mplus (TMproduct m1 m3) (TMproduct m2 m3) H1323 = TMproduct (Mplus m1 m2 H12) m3.
Proof.
  intros.
  apply Mequal.
  - repeat simpl_bits.
    reflexivity.
  - intros.
    unfold Mplus, TMproduct.
    lca.
Qed.

Lemma TMproduct_plus_r: forall (m1 m2 m3: Matrix) (H12: _) (H3132: _),
  Mplus (TMproduct m3 m1) (TMproduct m3 m2) H3132 = TMproduct m3 (Mplus m1 m2 H12).
Proof.
  intros.
  apply Mequal.
  - repeat simpl_bits.
    reflexivity.
  - intros.
    unfold Mplus, TMproduct.
    simpl_bits.
    simpl.
    repeat rewrite H12.
    lca.
Qed.

(* ============================================================================================== *)
(* relation between matrix multiplication and tensor product ==================================== *)

Lemma TMproduct_mult_l: forall
  (m1 m2 m3: Matrix) (H12: _) (H1234: _),
  TMproduct (Mmult m1 m3 H12) m2 = Mmult (TMproduct m1 m2) (TMproduct m3 (eye (Mbits m2))) H1234.
Proof.
  intros.
  apply Mequal.
  - repeat simpl_bits.
    lia.
  - intros.
    unfold Mmult, Mmult_unsafe, Mmult_inner, TMproduct.
    repeat simpl_bits.
    simpl.
    unfold dot_product_suppl.
    replace (2 ^ (Mbits m1 + Mbits m2))%nat with (2 ^ (Mbits m1) * 2 ^ (Mbits m2))%nat.
    pose (l1 := (2 ^ Mbits m1)%nat).
    pose (l2 := (2 ^ Mbits m2)%nat).
    replace (2 ^ Mbits m1)%nat with l1.
    replace (2 ^ Mbits m2)%nat with l2.
    replace (fun i0 : nat =>
      Minner m1 (i / l2) (i0 / l2) * Minner m2 (i mod l2) (i0 mod l2) *
      (Minner m3 (i0 / l2) (j / l2) * (if i0 mod l2 =? j mod l2 then 1 else 0))) with
      (fun i0 : nat => if i0 mod l2 =? j mod l2 then (
      Minner m1 (i / l2) (i0 / l2) * Minner m2 (i mod l2) (i0 mod l2) *
      (Minner m3 (i0 / l2) (j / l2))) else 0).
    rewrite func_sum_mod.
    replace (fun i0 : nat =>
      Minner m1 (i / l2) ((i0 * l2 + j mod l2) / l2) *
      Minner m2 (i mod l2) ((i0 * l2 + j mod l2) mod l2) *
      Minner m3 ((i0 * l2 + j mod l2) / l2) (j / l2)) with
      (fun i0 : nat =>
      Minner m1 (i / l2) i0 *
      Minner m2 (i mod l2) (j mod l2) *
      Minner m3 i0 (j / l2)).
      dps_unfold.
      symmetry.
      replace (
        func_sum_suppl (fun i0 : nat => Minner m1 (i / l2) i0 * Minner m3 i0 (j / l2)) 0 l1 *
        Minner m2 (i mod l2) (j mod l2)
      ) with (
        Minner m2 (i mod l2) (j mod l2) *
        func_sum_suppl (fun i0 : nat => Minner m1 (i / l2) i0 * Minner m3 i0 (j / l2)) 0 l1
      ) by lca.
      apply func_sum_suppl_scale.
      intros.
      lca.
      apply functional_extensionality.
      intros.
      replace ((x * l2 + j mod l2) / l2)%nat with x.
      replace ((x * l2 + j mod l2) mod l2) with (j mod l2).
      reflexivity.
      rewrite Nat.Div0.add_mod.
      rewrite Nat.Div0.mul_mod.
      rewrite Nat.Div0.mod_same.
      rewrite Nat.mul_0_r.
      rewrite Nat.Div0.mod_0_l.
      simpl.
      assert (l2 > 0) as Hl2.
      { unfold l2.
        apply pow_2_nonzero. }
      assert (j >= 0) as Hj by lia.
      assert (j mod l2 mod l2 = j mod l2) as Hmod.
      { apply Nat.mod_small.
        specialize (Nat.mod_bound_pos j l2 Hj Hl2) as Hmod. lia. }
      repeat rewrite Hmod.
      reflexivity.
      rewrite Nat.div_add_l.
      rewrite Nat.div_small.
      2: apply Nat.mod_bound_pos.
      1-5: unfold l2; specialize (pow_2_nonzero (Mbits m2)) as Hmm2; lia.
      apply functional_extensionality.
      intros.
      destruct (x mod l2 =? j mod l2).
      1-2: lca.
      unfold l2. reflexivity.
      unfold l1. reflexivity.
      symmetry.
      apply Nat.pow_add_r.
Qed.

Lemma TMproduct_mult_r: forall
  (m1 m2 m3: Matrix) (H12: _) (H1234: _),
  TMproduct m1 (Mmult m2 m3 H12) = Mmult (TMproduct m1 m2) (TMproduct (eye (Mbits m1)) m3) H1234.
Proof.
  intros.
  apply Mequal_unsafe.
  - repeat simpl_bits.
    lia.
  - intros.
    unfold Mmult, Mmult_unsafe, Mmult_inner, TMproduct.
    repeat simpl_bits.
    simpl.
    repeat rewrite <- H12.
    unfold dot_product_suppl.
    replace (2 ^ (Mbits m1 + Mbits m2))%nat with (2 ^ (Mbits m1) * 2 ^ (Mbits m2))%nat.
    pose (l1 := (2 ^ Mbits m1)%nat).
    pose (l2 := (2 ^ Mbits m2)%nat).
    replace (2 ^ Mbits m1)%nat with l1.
    replace (2 ^ Mbits m2)%nat with l2.
    replace (fun i0 : nat =>
      Minner m1 (i / l2) (i0 / l2) * Minner m2 (i mod l2) (i0 mod l2) *
      ((if i0 / l2 =? j / l2 then 1 else 0) * Minner m3 (i0 mod l2) (j mod l2))) with
      (fun i0 : nat => (if i0 / l2 =? j / l2 then
      Minner m1 (i / l2) (i0 / l2) * Minner m2 (i mod l2) (i0 mod l2) *
      Minner m3 (i0 mod l2) (j mod l2) else 0)).
    rewrite func_sum_div.
    rewrite func_sum_f with
      (f1 := (fun i0 : nat =>
      Minner m1 (i / l2) ((j / l2 * l2 + i0) / l2) *
      Minner m2 (i mod l2) ((j / l2 * l2 + i0) mod l2) *
      Minner m3 ((j / l2 * l2 + i0) mod l2) (j mod l2)))
      (f2 := (fun i0 : nat =>
      Minner m1 (i / l2) (j / l2) *
      Minner m2 (i mod l2) i0 *
      Minner m3 i0 (j mod l2))).
    unfold func_sum.
    unfold func_sum2.
    repeat rewrite Nat.sub_0_r.
    symmetry.
    apply func_sum_suppl_scale.
    intros.
    lca.
    intros.
    replace ((j / l2 * l2 + i0) mod l2) with i0.
    replace ((j / l2 * l2 + i0) / l2)%nat with (j / l2)%nat.
    reflexivity.
    rewrite Nat.div_add_l.
    replace (i0 / l2)%nat with O.
    lia.
    rewrite Nat.div_small.
    1-3: lia.
    rewrite Nat.Div0.add_mod.
    rewrite Nat.Div0.mul_mod.
    rewrite Nat.Div0.mod_same.
    rewrite Nat.mul_0_r.
    rewrite Nat.Div0.mod_0_l.
    simpl.
    repeat rewrite Nat.mod_small.
    1-4: nia.
    specialize (pow_2_nonzero (Mbits m2)) as Hpow.
    lia.
    rewrite Nat.pow_add_r in H0.
    lia.
    apply functional_extensionality.
    intros.
    destruct (x / l2 =? j / l2).
    1-2: lca.
    1-2: lia.
    symmetry.
    apply Nat.pow_add_r.
Qed.

Lemma TMproduct_mult: forall
  (m1 m2 m3 m4: Matrix) (H13: _) (H24: _) (H1234: _),
  TMproduct (Mmult m1 m3 H13) (Mmult m2 m4 H24) = Mmult (TMproduct m1 m2) (TMproduct m3 m4) H1234.
Proof.
  intros.
  unfold Mmult.
  assert (
    TMproduct m3 m4 =
    Mmult_unsafe (TMproduct m3 (eye (Mbits m4))) (TMproduct (eye (Mbits m3)) m4)
    ) as H34.
  { specialize TMproduct_mult_r as Hpr.
    unfold Mmult in Hpr.
    rewrite <- Hpr.
    specialize Mmult_eye_l as Heyel.
    unfold Mmult in Heyel.
    rewrite Heyel.
    all: repeat simpl_bits; reflexivity. }
  rewrite H34.
  specialize Mmult_assoc as Hmassoc.
  unfold Mmult in Hmassoc.
  rewrite <- Hmassoc.
  specialize TMproduct_mult_l as Hpl.
  unfold Mmult in Hpl.
  rewrite <- H24.
  rewrite <- Hpl.
  specialize TMproduct_mult_r as Hpr.
  unfold Mmult in Hpr.
  replace (Mbits m3) with (Mbits (Mmult_unsafe m1 m3)).
  rewrite <- Hpr.
  reflexivity.
  apply H24.
  all: repeat simpl_bits; lia.
Qed.

(* ============================================================================================== *)
(* relation between dot product and tensor product ============================================== *)

Lemma TVproduct_dot_product: forall (r1 r2: RowVec) (c1 c2: ColVec) (H1212: _) (H11: _) (H22: _),
  dot_product (TRVproduct r1 r2) (TCVproduct c1 c2) H1212 = (dot_product r1 c1 H11) * (dot_product r2 c2 H22).
Proof.
  intros.
  unfold dot_product, dot_product_unsafe, TCVproduct, dot_product_suppl.
  simpl_bits.
  simpl.
  simpl_bits.
  repeat rewrite H11.
  repeat rewrite H22.
  replace
    (fun i : nat =>
      RVinner r1 (i / 2 ^ CVbits c2) * RVinner r2 (i mod 2 ^ CVbits c2) *
      (CVinner c1 (i / 2 ^ CVbits c2) * CVinner c2 (i mod 2 ^ CVbits c2))) with
    (fun i : nat =>
      (fun j => (RVinner r1 j * CVinner c1 j)) (i / 2 ^ CVbits c2)%nat *
      (fun j => (RVinner r2 j * CVinner c2 j)) (i mod 2 ^ CVbits c2) ).
  replace (2 ^ (CVbits c1 + CVbits c2))%nat with (2 ^ CVbits c1 * 2 ^ CVbits c2)%nat.
  specialize (
    func_sum_dist (2 ^ CVbits c1) (2 ^ CVbits c2)
    (fun j => (RVinner r1 j * CVinner c1 j))
    (fun j => (RVinner r2 j * CVinner c2 j))
  ) as Hdist.
  simpl in Hdist.
  apply Hdist.
  specialize (pow_2_nonzero (CVbits c2)) as Hnz.
  lia.
  rewrite <- Nat.pow_add_r.
  reflexivity.
  apply functional_extensionality.
  intros.
  lca.
Qed.

(* ============================================================================================== *)
(* relation between outer product and tensor product ============================================ *)

Lemma TMVproduct_mult: forall (r1 r2: RowVec) (c1 c2: ColVec) (H1212: _) (H1: _) (H2: _),
  VVmult (TCVproduct c1 c2) (TRVproduct r1 r2) H1212 =
  TMproduct (VVmult c1 r1 H1) (VVmult c2 r2 H2).
Proof.
  unfold VVmult, TCVproduct, TRVproduct, TMproduct.
  simpl_bits.
  simpl.
  intros.
  apply Mequal.
  - reflexivity.
  - unfold Msize.
    simpl.
    intros.
    ring_simplify.
    repeat rewrite H1.
    repeat rewrite H2.
    reflexivity.
Qed.

(* ============================================================================================== *)
(* tensor product of identity matrices ========================================================== *)

Lemma TMproduct_eye: forall (n m: nat), TMproduct (eye n) (eye m) = eye (n + m).
Proof.
  intros.
  apply Mequal_unsafe.
  - repeat simpl_bits.
    reflexivity.
  - intros.
    unfold Minner, TMproduct, eye.
    simpl.
    unfold Msize, pow_2.
    simpl.
    destruct (i =? j) eqn: E.
    + apply Nat.eqb_eq in E.
      replace (i / 2 ^ m =? j / 2 ^ m) with true.
      replace (i mod 2 ^ m =? j mod 2 ^ m) with true.
      lca.
      symmetry.
      apply Nat.eqb_eq.
      rewrite E.
      reflexivity.
      symmetry.
      apply Nat.eqb_eq.
      rewrite E.
      reflexivity.
    + repeat simpl_bits.
      rewrite Nat.pow_add_r in *.
      apply Nat.eqb_neq in E.
      specialize (neq_iff_div_or_mod i j (2 ^ m)) as Hneq.
      eapply Hneq in E.
      destruct E as [Ediv|Emod].
      * apply <- Nat.eqb_neq in Ediv.
        rewrite Ediv.
        lca.
      * apply <- Nat.eqb_neq in Emod.
        rewrite Emod.
        lca.
      * lia.
Qed.

Lemma TMproduct_eye0_l: forall (m: Matrix), TMproduct (eye 0) m = m.
Proof.
  intros.
  apply Mequal_unsafe.
  - repeat simpl_bits.
    lia.
  - intros.
    repeat simpl_bits.
    unfold TMproduct, eye, Msize, pow_2.
    simpl in *.
    replace (i / 2 ^ Mbits m)%nat with O.
    replace (j / 2 ^ Mbits m)%nat with O.
    replace (i mod 2 ^ Mbits m)%nat with i.
    replace (j mod 2 ^ Mbits m)%nat with j.
    lca.
    symmetry.
    apply Nat.mod_small.
    apply H0.
    symmetry.
    apply Nat.mod_small.
    apply H.
    symmetry.
    apply Nat.div_small.
    apply H0.
    symmetry.
    apply Nat.div_small.
    apply H.
Qed.

Lemma TMproduct_eye0_r: forall (m: Matrix), TMproduct m (eye 0) = m.
Proof.
  intros.
  apply Mequal.
  - repeat simpl_bits.
    lia.
  - intros.
    repeat simpl_bits.
    unfold TMproduct, eye, Msize.
    simpl.
    repeat rewrite divmod_fst_n0m0.
    repeat rewrite Nat.add_0_r.
    lca.
Qed.

(* ============================================================================================== *)
