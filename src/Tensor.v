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

Lemma TMProduct_bits: forall (m1 m2: Matrix), Mbits (TMproduct m1 m2) = (Mbits m1 + Mbits m2)%nat.
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

Lemma TCVproduct_bits: forall (r1 r2: RowVec), RVbits (TRVproduct r1 r2) = (RVbits r1 + RVbits r2)%nat.
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

Lemma TRVproduct_bits: forall (c1 c2: ColVec), CVbits (TCVproduct c1 c2) = (CVbits c1 + CVbits c2)%nat.
Proof. reflexivity. Qed.

(* ============================================================================================== *)
(* tactic of simplifying bits =================================================================== *)

Ltac simpl_bits :=
  unfold MMeqbits in *;
  unfold Msize in *;
  repeat rewrite Mmult_bits_l in *;
  repeat rewrite Mconjtrans_bits in *;
  repeat rewrite eye_bits in *;
  repeat rewrite TMProduct_bits in *.

(* ============================================================================================== *)
(* distributive property of tensor product ====================================================== *)

Lemma Tproduct_dist_ll: forall
  (m1 m2 m3: Matrix) (H12: _) (H1234: _),
  TMproduct (Mmult m1 m3 H12) m2 = Mmult (TMproduct m1 m2) (TMproduct m3 (eye (Mbits m2))) H1234.
Proof.
  intros.
  apply Mequal.
  - repeat simpl_bits.
    lia.
  - intros.
    unfold Mmult.
    unfold Mmult_unsafe.
    unfold Mmult_inner.
    unfold TMproduct.
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
      rewrite Nat.add_mod.
      rewrite Nat.mul_mod.
      rewrite Nat.mod_same.
      rewrite Nat.mul_0_r.
      rewrite Nat.mod_0_l.
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
      unfold l2. specialize (pow_2_nonzero (Mbits m2)) as Hmm2. lia.
      unfold l2. specialize (pow_2_nonzero (Mbits m2)) as Hmm2. lia.
      unfold l2. specialize (pow_2_nonzero (Mbits m2)) as Hmm2. lia.
      unfold l2. specialize (pow_2_nonzero (Mbits m2)) as Hmm2. lia.
      rewrite Nat.div_add_l.
      rewrite Nat.div_small.
      lia.
      apply Nat.mod_bound_pos.
      lia.
      unfold l2. apply pow_2_nonzero.
      unfold l2. specialize (pow_2_nonzero (Mbits m2)) as Hmm2. lia.
      unfold l2. specialize (pow_2_nonzero (Mbits m2)) as Hmm2. lia.
      apply functional_extensionality.
      intros.
      destruct (x mod l2 =? j mod l2).
      lca. lca.
      unfold l2. reflexivity.
      unfold l1. reflexivity.
      symmetry.
      apply Nat.pow_add_r.
Qed.

(* ============================================================================================== *)

(* Definition trace, partial trace *)
