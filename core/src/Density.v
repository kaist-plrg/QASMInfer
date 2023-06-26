Require Export Qubit.

Declare Scope Den_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Open Scope M_scope.
Open Scope T_scope.
Open Scope Qst_scope.


(* normalized density matrix ==================================================================== *)

Definition Den_normalized (den: Matrix) := Mtrace den = 1.

Lemma TMproduct_normalized: forall (den1 den2: Matrix),
  Den_normalized den1 -> Den_normalized den2 -> Den_normalized (TMproduct den1 den2).
Proof.
  intros.
  unfold Den_normalized, Mtrace, TMproduct, Msize, pow_2 in *.
  simpl.
  rewrite Nat.pow_add_r.
  specialize (
    func_sum_dist
    (2 ^ Mbits den1)
    (2 ^ Mbits den2)
    (fun j => Minner den1 j j)
    (fun j => Minner den2 j j)
  ) as Hdist.
  simpl in *.
  rewrite Hdist.
  rewrite H.
  rewrite H0.
  lca.
  specialize (pow_2_nonzero (Mbits den2)) as Hnz.
  lia.
Qed.

(* ============================================================================================== *)
(* basic density matrix ========================================================================= *)

Definition Den_0: Matrix :=
  {|
    Mbits := 1;
    Minner := fun i j => match i, j with
    | 0, 0 => 1
    | _, _ => 0
    end;
  |}.

Definition Den_1: Matrix :=
  {|
    Mbits := 1;
    Minner := fun i j => match i, j with
    | 1, 1 => 1
    | _, _ => 0
    end;
  |}.

Lemma Den_0_Hermitian: Qop_Hermitian Den_0.
Proof.
  apply Mequal.
  - simpl_bits.
    reflexivity.
  - intros.
    unfold Mconjtrans, Den_0.
    simpl.
    destruct i as [|i], j as [|j].
    all: lca.
Qed.

Lemma Den_1_Hermitian: Qop_Hermitian Den_1.
Proof.
  apply Mequal.
  - simpl_bits.
    reflexivity.
  - intros.
    unfold Mconjtrans, Den_1, Msize, pow_2 in *.
    simpl in *.
    destruct i as [|i], j as [|j].
    lca.
    assert (j = 0) by lia; subst j; lca.
    assert (i = 0) by lia; subst i; lca.
    assert (j = 0) by lia; subst j;
    assert (i = 0) by lia; subst i; lca.
Qed.

Lemma Den_0_pure: forall H, Den_0 = VVmult Qst_0 (CVconjtrans Qst_0) H.
Proof.
  intros.
  apply Mequal.
  - reflexivity.
  - intros.
    simpl_bits.
    unfold VVmult, VVmult_unsafe, Den_0 in *.
    simpl in *.
    destruct i, j.
    lca.
    assert (j = 0) by lia; subst j; lca.
    assert (i = 0) by lia; subst i; lca.
    assert (j = 0) by lia; subst j;
    assert (i = 0) by lia; subst i; lca.
Qed.

Lemma Den_1_pure: forall H, Den_1 = VVmult Qst_1 (CVconjtrans Qst_1) H.
Proof.
  intros.
  apply Mequal.
  - reflexivity.
  - intros.
    simpl_bits.
    unfold VVmult, VVmult_unsafe, Den_1 in *.
    simpl in *.
    destruct i, j.
    lca.
    assert (j = 0) by lia; subst j; lca.
    assert (i = 0) by lia; subst i; lca.
    assert (j = 0) by lia; subst j;
    assert (i = 0) by lia; subst i; lca.
Qed.

Lemma Den_0_positive: Qop_positive Den_0.
Proof.
  assert (CReqbits Qst_0 (CVconjtrans Qst_0)) as Hcr by reflexivity.
  rewrite (Den_0_pure Hcr).
  unfold Qop_positive.
  intros.
  specialize dot_product_conjtrans as Hconj.
  unfold MVmult, VVmult, dot_product.
  simpl_bits.
  assert (
    dot_product_unsafe (CVconjtrans c) (MVmult_unsafe (VVmult_unsafe Qst_0 (CVconjtrans Qst_0)) c) =
    dot_product_unsafe (CVconjtrans c) Qst_0 * dot_product_unsafe (CVconjtrans Qst_0) c
  ) as Hassoc.
  { unfold dot_product_unsafe, CVconjtrans, MVmult_unsafe, MVmult_inner, VVmult_unsafe.
    dps_unfold.
    simpl_bits.
    repeat rewrite Hd.
    simpl.
    lca. }
  unfold dot_product in *.
  rewrite Hassoc.
  replace c with (RVconjtrans (CVconjtrans c)).
  rewrite <- Hconj.
  rewrite CRVconjtrans_twice.
  apply Cconj_mult_ge0.
  rewrite CVconjtrans_bits; lia.
  rewrite RVconjtrans_bits.
  repeat rewrite CVconjtrans_bits.
  lia.
  apply CRVconjtrans_twice.
Qed.

Lemma Den_1_positive: Qop_positive Den_1.
Proof.
  assert (CReqbits Qst_1 (CVconjtrans Qst_1)) as Hcr by reflexivity.
  rewrite (Den_1_pure Hcr).
  unfold Qop_positive.
  intros.
  specialize dot_product_conjtrans as Hconj.
  unfold MVmult, VVmult, dot_product.
  simpl_bits.
  assert (
    dot_product_unsafe (CVconjtrans c) (MVmult_unsafe (VVmult_unsafe Qst_1 (CVconjtrans Qst_1)) c) =
    dot_product_unsafe (CVconjtrans c) Qst_1 * dot_product_unsafe (CVconjtrans Qst_1) c
  ) as Hassoc.
  { unfold dot_product_unsafe, CVconjtrans, MVmult_unsafe, MVmult_inner, VVmult_unsafe.
    dps_unfold.
    simpl_bits.
    repeat rewrite Hd.
    simpl.
    lca. }
  unfold dot_product in *.
  rewrite Hassoc.
  replace c with (RVconjtrans (CVconjtrans c)).
  rewrite <- Hconj.
  rewrite CRVconjtrans_twice.
  apply Cconj_mult_ge0.
  rewrite CVconjtrans_bits; lia.
  rewrite RVconjtrans_bits.
  repeat rewrite CVconjtrans_bits.
  lia.
  apply CRVconjtrans_twice.
Qed.

Lemma Den_0_normalized: Den_normalized Den_0.
Proof. lca. Qed.

Lemma Den_1_normalized: Den_normalized Den_1.
Proof. lca. Qed.

(* ============================================================================================== *)
(* apply uop to density matrix ================================================================== *)

Definition Den_unitary (den uop: Matrix) (H1: _) (H2: _) :=
  (Mmult (Mmult uop den H1) (Mconjtrans uop) H2).

Lemma Den_unitary_bits: forall (den uop: Matrix) (H1: _) (H2: _),
  MMeqbits (Den_unitary den uop H1 H2) den.
Proof.
  intros.
  unfold Den_unitary.
  simpl_bits.
  apply H1.
Qed.

(* ============================================================================================== *)
(* probability ================================================================================== *)

Definition Den_prob (den: Matrix) (proj: Matrix) (H: MMeqbits den proj): C :=
  Mtrace (Mmult den proj H).

Definition Den_prob_0 (den: Matrix) (n t: nat) (Ht: t < n) (H: Mbits den = n): C.
  refine (Den_prob den (Qproj0_n_t n t Ht) _).
  simpl_bits.
  rewrite Qproj0_n_t_bits.
  apply H.
Defined.

Definition Den_prob_1 (den: Matrix) (n t: nat) (Ht: t < n) (H: Mbits den = n): C.
  refine (Den_prob den (Qproj1_n_t n t Ht) _).
  simpl_bits.
  rewrite Qproj1_n_t_bits.
  apply H.
Defined.

Lemma Den_prob_sum: forall (den: Matrix) (n t: nat) (Ht: _) (H: _),
  Mtrace den = 1 -> Den_prob_0 den n t Ht H + Den_prob_1 den n t Ht H = 1.
Proof.
  intros.
  unfold Den_prob_0, Den_prob_1, Den_prob.
  erewrite <- Mtrace_Mplus_dist.
  erewrite <- Mmult_dist_plus_r.
  specialize Mmult_eye_r as Heye.
  unfold Mmult in *.
  erewrite Qproj_n_sum_eye.
  rewrite Heye.
  rewrite H0.
  lca.
  Unshelve.
  1-3:simpl_bits; lia.
  simpl_bits.
  rewrite Qproj1_n_t_bits.
  apply Qproj0_n_t_bits.
  simpl_bits.
  rewrite Qproj0_n_t_bits.
  lia.
Qed.

Definition Den_expect (den observable: Matrix) (H: MMeqbits den observable) :=
  Mtrace (Mmult den observable H).

(* ============================================================================================== *)
(* measurement ================================================================================== *)

Definition Den_measure (den proj: Matrix) (Hd: MMeqbits den proj): Matrix.
Proof.
  refine (
    Msmul
      (Cinv (Den_prob den proj Hd))
      ( Mmult (
          Mmult proj den _
        ) proj _)
  ).
  Unshelve.
  all: simpl_bits; simpl; lia.
Defined.

Definition Den_measure_0 (den: Matrix) (n t: nat) (Ht: t < n) (Hd: Mbits den = n): Matrix.
  refine (Den_measure den (Qproj0_n_t n t Ht) _).
  all: simpl_bits; simpl; lia.
Defined.

Definition Den_measure_1 (den: Matrix) (n t: nat) (Ht: t < n) (Hd: Mbits den = n): Matrix.
  refine (Den_measure den (Qproj1_n_t n t Ht) _).
  all: simpl_bits; simpl; lia.
Defined.

Definition Den_measure_2
  (den: Matrix) (n t: nat)  (Ht: t < n) (Hd: Mbits den = n):
  {m0m1: (Matrix * Matrix) | MMeqbits (fst m0m1) (snd m0m1)}.
Proof.
  refine ( exist _ (
      Mmult (
        Mmult (Qproj0_n_t n t Ht) den _
      ) (Qproj0_n_t n t Ht) _,
      Mmult (
        Mmult (Qproj1_n_t n t Ht) den _
      ) (Qproj1_n_t n t Ht) _) _ ).
    Unshelve.
    all: simpl_bits; simpl; lia.
Defined.

Definition Den_measure_and_sum(den: Matrix) (n t: nat) (Ht: t < n) (Hd: Mbits den = n): Matrix.
Proof.
  destruct (Den_measure_2 den n t Ht Hd) as [ [m0 m1] Hm0m1].
  exact (Mplus m0 m1 Hm0m1).
Defined.

Lemma Den_measure_bits: forall (den proj: Matrix) H, MMeqbits (Den_measure den proj H) den.
Proof.
  intros.
  unfold Den_measure, Mmult.
  simpl_bits.
  lia.
Qed.

Lemma Den_measure_0_bits: forall (den: Matrix) (n t: nat) (Ht: _) (Hd: _),
  Mbits (Den_measure_0 den n t Ht Hd) = n.
Proof.
  intros.
  unfold Den_measure_0.
  rewrite Den_measure_bits.
  apply Hd.
Qed.

Lemma Den_measure_1_bits: forall (den: Matrix) (n t: nat) (Ht: _) (Hd: _),
  Mbits (Den_measure_1 den n t Ht Hd) = n.
Proof.
  intros.
  unfold Den_measure_1.
  rewrite Den_measure_bits.
  apply Hd.
Qed.

Lemma Den_measure_and_sum_bits: forall (den: Matrix) (n t: nat) (Ht: _) (Hd: _),
  Mbits (Den_measure_and_sum den n t Ht Hd) = n.
Proof.
  intros.
  unfold Den_measure, Mmult, Mplus, Mbop_unsafe, Mmult_unsafe.
  simpl.
  lia.
Qed.

(* projection on 01001001.. is a projection on single  real: i.e. self-adjoint *)
Definition Den_proj_uop (den proj uop: Matrix) (H: MMeqbits den uop) (H2: MMeqbits proj den): Matrix.
Proof.
  refine (
    Mplus (
      Den_unitary (
        Mmult ( Mmult
        proj den _) proj
        _
      ) uop _ _
    ) (
      Mmult ( Mmult
      (Mminus (eye (Mbits proj)) proj _) den _) (Mminus (eye (Mbits proj)) proj _)
      _
    ) _
  ).
  Unshelve.
  all: simpl_bits; simpl; lia.
Defined.

(* ============================================================================================== *)
(* density matrix at the initial state ========================================================== *)

Inductive InitialDensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_empty: InitialDensityMatrix 0 (eye 0)
| DensityMatrix_0: InitialDensityMatrix 1 Den_0
| DensityMatrix_1: InitialDensityMatrix 1 Den_1
| DensityMatrix_TMproduct (n1 n2: nat) (den1 den2: Matrix):
  InitialDensityMatrix n1 den1 ->
  InitialDensityMatrix n2 den2 ->
  InitialDensityMatrix (n1 + n2) (TMproduct den1 den2).

Lemma InitialDensityMatrix_bits: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> Mbits den = n.
Proof.
  intros.
  induction H.
  1-3: simpl_bits; reflexivity.
  simpl_bits.
  lia.
Qed.

Lemma InitialDensityMatrix_trace_real: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> Cimag (Mtrace den) = 0%R.
Proof.
  intros.
  induction H.
  - simpl; lra.
  - simpl; lra.
  - simpl; lra.
  - rewrite TMproduct_trace.
    unfold Cimag, Cmult in *.
    rewrite IHInitialDensityMatrix1.
    rewrite IHInitialDensityMatrix2.
    simpl.
    lra.
Qed.

Lemma InitialDensityMatrix_trace_pos: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> (Creal (Mtrace den) >= 0)%R.
Proof.
  intros.
  induction H.
  - simpl; lra.
  - simpl; lra.
  - simpl; lra.
  - rewrite TMproduct_trace.
    specialize InitialDensityMatrix_trace_real as Hreal.
    unfold Creal, Cimag, Cmult in *.
    simpl.
    rewrite (Hreal n1).
    ring_simplify.
    nra.
    apply H.
Qed.

Lemma InitialDensityMatrix_prob0_real: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  InitialDensityMatrix n den -> Cimag (Den_prob_0 den n t Ht Hd) = 0%R.
Proof.
  intros.
  revert Ht Hd.
  revert t.
  induction H.
  - lia.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_0, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_1, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    specialize TMproduct_mult as Htm.
    specialize Mmult_eye_r as Heyer.
    specialize InitialDensityMatrix_trace_real as Hreal.
    unfold Den_prob_0, Den_prob, Mmult, Qproj0_n_t in *.
    destruct (lt_dec t n1).
    * erewrite Qop_sq_split_l.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      unfold Cimag, Cmult in *.
      assert (Mbits den1 = n1) as Hbit1.
      { apply InitialDensityMatrix_bits.
        apply H. }
      specialize (IHInitialDensityMatrix1 t l Hbit1).
      rewrite IHInitialDensityMatrix1.
      simpl.
      ring_simplify.
      rewrite Heyer.
      rewrite (Hreal n2).
      lra.
      apply H0.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H0.
      symmetry.
      apply InitialDensityMatrix_bits.
      apply H0.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply InitialDensityMatrix_bits.
      apply H.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H0.
      simpl_bits.
      rewrite Qop_sq_bits.
      simpl_bits.
      apply Hd.
    * erewrite Qop_sq_split_r.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      unfold Cimag, Cmult in *.
      rewrite Heyer.
      simpl.
      rewrite (Hreal n1 den1).
      ring_simplify.
      erewrite IHInitialDensityMatrix2.
      ring.
      apply InitialDensityMatrix_bits.
      apply H0.
      apply H.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H.
      symmetry.
      apply InitialDensityMatrix_bits.
      apply H.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply InitialDensityMatrix_bits.
      apply H0.
      repeat simpl_bits.
      rewrite Qop_sq_bits.
      apply Hd.
      lia.
      Unshelve.
      lia.
Qed.

Lemma InitialDensityMatrix_prob0_pos: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  InitialDensityMatrix n den -> (Creal (Den_prob_0 den n t Ht Hd) >= 0)%R.
Proof.
  intros.
  revert Ht Hd.
  revert t.
  induction H.
  - intros.
    simpl.
    lra.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_0, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_0, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    assert (Mbits den1 = n1) as Hb1.
    { apply InitialDensityMatrix_bits.
      apply H. }
    assert (Mbits den2 = n2) as Hb2.
    { apply InitialDensityMatrix_bits.
      apply H0. }
    specialize TMproduct_mult as Htm.
    specialize Mmult_eye_r as Hmer.
    specialize InitialDensityMatrix_prob0_real as Hidmpr.
    unfold Den_prob_0, Den_prob, Mmult, Qproj0_n_t in *.
    destruct (lt_dec t n1).
    + erewrite Qop_sq_split_l.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      apply Creal_mult_ge0.
      apply IHInitialDensityMatrix1.
      apply Hb1.
      rewrite Hmer.
      apply (InitialDensityMatrix_trace_pos n2).
      apply H0.
      simpl_bits.
      apply Hb2.
      symmetry.
      apply Hb2.
      eapply InitialDensityMatrix_prob0_real.
      apply H.
      rewrite Hmer.
      eapply InitialDensityMatrix_trace_real.
      apply H0.
      simpl_bits.
      apply Hb2.
      symmetry.
      apply Hb2.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply Hb1.
      simpl_bits.
      apply Hb2.
      repeat simpl_bits.
      rewrite Qop_sq_bits.
      apply Hd.
    + erewrite Qop_sq_split_r.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      apply Creal_mult_ge0.
      rewrite Hmer.
      eapply InitialDensityMatrix_trace_pos.
      apply H.
      simpl_bits.
      apply Hb1.
      1-2: auto.
      rewrite Hmer.
      eapply InitialDensityMatrix_trace_real.
      apply H.
      1-2: auto.
      eapply InitialDensityMatrix_prob0_real.
      1-2: auto.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply Hb2.
      repeat simpl_bits.
      rewrite Qop_sq_bits.
      apply Hd.
      lia.
      Unshelve.
      all: lia.
Qed.

Lemma InitialDensityMatrix_prob0_real_pos: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  InitialDensityMatrix n den -> Cge_0 (Den_prob_0 den n t Ht Hd).
Proof.
  intros.
  split.
  - apply InitialDensityMatrix_prob0_pos.
    apply H.
  - apply InitialDensityMatrix_prob0_real.
    apply H.
Qed.

Lemma InitialDensityMatrix_prob1_real: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  InitialDensityMatrix n den -> Cimag (Den_prob_1 den n t Ht Hd) = 0%R.
Proof.
  intros.
  revert Ht Hd.
  revert t.
  induction H.
  - lia.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_0, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_1, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    specialize TMproduct_mult as Htm.
    specialize Mmult_eye_r as Heyer.
    specialize InitialDensityMatrix_trace_real as Hreal.
    unfold Den_prob_1, Den_prob, Mmult, Qproj1_n_t in *.
    destruct (lt_dec t n1).
    * erewrite Qop_sq_split_l.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      unfold Cimag, Cmult in *.
      assert (Mbits den1 = n1) as Hbit1.
      { apply InitialDensityMatrix_bits.
        apply H. }
      specialize (IHInitialDensityMatrix1 t l Hbit1).
      rewrite IHInitialDensityMatrix1.
      simpl.
      ring_simplify.
      rewrite Heyer.
      rewrite (Hreal n2).
      lra.
      apply H0.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H0.
      symmetry.
      apply InitialDensityMatrix_bits.
      apply H0.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply InitialDensityMatrix_bits.
      apply H.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H0.
      simpl_bits.
      rewrite Qop_sq_bits.
      simpl_bits.
      apply Hd.
    * erewrite Qop_sq_split_r.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      unfold Cimag, Cmult in *.
      rewrite Heyer.
      simpl.
      rewrite (Hreal n1 den1).
      ring_simplify.
      erewrite IHInitialDensityMatrix2.
      ring.
      apply InitialDensityMatrix_bits.
      apply H0.
      apply H.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H.
      symmetry.
      apply InitialDensityMatrix_bits.
      apply H.
      simpl_bits.
      apply InitialDensityMatrix_bits.
      apply H.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply InitialDensityMatrix_bits.
      apply H0.
      repeat simpl_bits.
      rewrite Qop_sq_bits.
      apply Hd.
      lia.
      Unshelve.
      lia.
Qed.

Lemma InitialDensityMatrix_prob1_pos: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  InitialDensityMatrix n den -> (Creal (Den_prob_1 den n t Ht Hd) >= 0)%R.
Proof.
  intros.
  revert Ht Hd.
  revert t.
  induction H.
  - intros.
    simpl.
    lra.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_0, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    assert (t = 0) by lia.
    subst t.
    unfold Den_prob_0, Den_prob, Mmult.
    simpl.
    lra.
  - intros.
    assert (Mbits den1 = n1) as Hb1.
    { apply InitialDensityMatrix_bits.
      apply H. }
    assert (Mbits den2 = n2) as Hb2.
    { apply InitialDensityMatrix_bits.
      apply H0. }
    specialize TMproduct_mult as Htm.
    specialize Mmult_eye_r as Hmer.
    specialize InitialDensityMatrix_prob0_real as Hidmpr.
    unfold Den_prob_1, Den_prob, Mmult, Qproj1_n_t in *.
    destruct (lt_dec t n1).
    + erewrite Qop_sq_split_l.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      apply Creal_mult_ge0.
      apply IHInitialDensityMatrix1.
      apply Hb1.
      rewrite Hmer.
      apply (InitialDensityMatrix_trace_pos n2).
      apply H0.
      simpl_bits.
      apply Hb2.
      symmetry.
      apply Hb2.
      eapply InitialDensityMatrix_prob1_real.
      apply H.
      rewrite Hmer.
      eapply InitialDensityMatrix_trace_real.
      apply H0.
      simpl_bits.
      apply Hb2.
      symmetry.
      apply Hb2.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply Hb1.
      simpl_bits.
      apply Hb2.
      repeat simpl_bits.
      rewrite Qop_sq_bits.
      apply Hd.
    + erewrite Qop_sq_split_r.
      rewrite <- Htm.
      rewrite TMproduct_trace.
      apply Creal_mult_ge0.
      rewrite Hmer.
      eapply InitialDensityMatrix_trace_pos.
      apply H.
      simpl_bits.
      apply Hb1.
      1-2: auto.
      rewrite Hmer.
      eapply InitialDensityMatrix_trace_real.
      apply H.
      1-2: auto.
      eapply InitialDensityMatrix_prob1_real.
      1-2: auto.
      simpl_bits.
      rewrite Qop_sq_bits.
      apply Hb2.
      repeat simpl_bits.
      rewrite Qop_sq_bits.
      apply Hd.
      lia.
      Unshelve.
      all: lia.
Qed.

Lemma InitialDensityMatrix_prob1_real_pos: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  InitialDensityMatrix n den -> Cge_0 (Den_prob_1 den n t Ht Hd).
Proof.
  intros.
  split.
  - apply InitialDensityMatrix_prob1_pos.
    apply H.
  - apply InitialDensityMatrix_prob1_real.
    apply H.
Qed.

Lemma InitialDensityMatrix_pure: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den ->
  exists (qst: ColVec) (H: _),
  den = VVmult qst (CVconjtrans qst) H.
Proof.
  intros.
  induction H.
  - exists {| CVbits := 0; CVinner := fun _ => 1 |}.
    assert (CReqbits
      {| CVbits := 0; CVinner := fun _ : nat => 1 |}
      (CVconjtrans {| CVbits := 0; CVinner := fun _ : nat => 0 |})) as H0.
    { simpl_bits; reflexivity. }
    exists H0.
    unfold eye, VVmult, VVmult_unsafe, CVconjtrans.
    simpl.
    apply Mequal.
    + reflexivity.
    + intros.
      simpl_bits.
      simpl in *.
      assert (i = 0) by lia; subst i.
      assert (j = 0) by lia; subst j.
      simpl.
      lca.
  - exists Qst_0.
    assert (CReqbits Qst_0 (CVconjtrans Qst_0)) as He by reflexivity.
    exists He.
    apply Den_0_pure.
  - exists Qst_1.
    assert (CReqbits Qst_1 (CVconjtrans Qst_1)) as He by reflexivity.
    exists He.
    apply Den_1_pure.
  - destruct IHInitialDensityMatrix1 as [qst1 [H1 IH1] ].
    destruct IHInitialDensityMatrix2 as [qst2 [H2 IH2] ].
    exists (TCVproduct qst1 qst2).
    assert (CReqbits (TCVproduct qst1 qst2) (CVconjtrans (TCVproduct qst1 qst2))) as He.
    { simpl_bits. reflexivity. }
    exists He.
    specialize TMVproduct_mult as Htmv.
    unfold VVmult in *.
    rewrite TCVproduct_conjtrans.
    rewrite Htmv.
    rewrite <- IH1.
    rewrite <- IH2.
    reflexivity.
    all: repeat simpl_bits; reflexivity.
Qed.

Lemma InitialDensityMatrix_positive: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> Qop_positive den.
Proof.
  intros.
  apply InitialDensityMatrix_pure in H.
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

(* ============================================================================================== *)
(* density matrix =============================================================================== *)

Inductive DensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_init (n: nat) (den: Matrix): InitialDensityMatrix n den -> DensityMatrix n den
| DensityMatrix_unitary (n: nat) (den uop: Matrix) (H1: _) (H2: _):
  DensityMatrix n den ->
  Qop_unitary uop ->
  DensityMatrix n (Den_unitary den uop H1 H2)
(* | DensityMatrix_measure (den: Matrix) (n t: nat) (Ht: _) (Hd: _):
  DensityMatrix n den ->
  DensityMatrix n (Den_measure_and_sumden n t Ht Hd) *)
| DensityMatrix_measure_0 (den: Matrix) (n t: nat) (Ht: _) (Hd: _):
  DensityMatrix n den ->
  DensityMatrix n (Den_measure_0 den n t Ht Hd)
| DensityMatrix_measure_1 (den: Matrix) (n t: nat) (Ht: _) (Hd: _):
  DensityMatrix n den ->
  DensityMatrix n (Den_measure_1 den n t Ht Hd).

(* Lemma DensityMatrix_prob0_real: forall (n t: nat) (den: Matrix) (Ht: _) (Hd: _),
  DensityMatrix n den -> Cimag (Den_prob_0 den n t Ht Hd) = 0%R.
Proof.
  intros.
  revert Ht Hd.
  revert t.
  specialize Mtrace_Mmult_comm as Htrcomm.
  specialize Mmult_assoc as Hassoc.
  specialize Mconjtrans_mult as Hct.
  induction H.
  - intros.
    apply InitialDensityMatrix_prob0_real.
    apply H.
  - intros.
    apply Cconj_real.
    unfold Qop_Hermitian, Den_unitary, Den_prob_0, Den_prob, Mmult in *.
    rewrite Mtrace_Cconj.
    repeat rewrite Hct.
    rewrite Mconjtrans_twice.
    rewrite Hassoc at 1.
    rewrite Htrcomm.
    repeat rewrite Hassoc.
    rewrite <- Hassoc.
    rewrite Htrcomm.
    rewrite <- Hassoc. *)


(* ============================================================================================== *)
(* density matrices are Hermitian =============================================================== *)

Lemma DensityMatrix_prob_real_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den ->
  (forall t0 Ht0 Hd0, Cimag (Den_prob_0 den n t0 Ht0 Hd0) = 0%R) /\
  (forall t1 Ht1 Hd1, Cimag (Den_prob_1 den n t1 Ht1 Hd1) = 0%R) /\
  Qop_Hermitian den.
Proof.
  intros n den H.
  induction H.
  - split; [|split ].
    + intros.
      apply InitialDensityMatrix_prob0_real.
      apply H.
    + intros.
      apply InitialDensityMatrix_prob1_real.
      apply H.
    + induction H.
      * unfold Qop_Hermitian, eye, Mconjtrans.
        apply Mequal.
        { reflexivity. }
        { intros.
          simpl_bits.
          simpl in *.
          assert (i = 0) by lia; subst i.
          assert (j = 0) by lia; subst j.
          simpl.
          lca. }
      * apply Den_0_Hermitian.
      * apply Den_1_Hermitian.
      * apply TMproduct_Hermitian.
        apply IHInitialDensityMatrix1.
        apply IHInitialDensityMatrix2.
  - destruct IHDensityMatrix as [IH0 [IH1 IHH] ].
    specialize Mtrace_Mmult_comm as Htrcomm.
    specialize Mmult_assoc as Hassoc.
    specialize Mconjtrans_mult as Hct.
    split; [|split].
    + intros.
      apply Cconj_real.
      unfold Qop_Hermitian, Den_unitary, Den_prob_0, Den_prob, Mmult in *.
      rewrite Mtrace_Cconj.
      repeat rewrite Hct.
      rewrite Mconjtrans_twice.
      rewrite IHH.
      rewrite Qproj0_n_t_Hermitian.
      rewrite Htrcomm at 1.
      replace
      (Mmult_unsafe uop (Mmult_unsafe den (Mconjtrans uop))) with
      (Mmult_unsafe (Mmult_unsafe uop den) (Mconjtrans uop)).
      reflexivity.
      apply Hassoc.
      all: simpl_bits; repeat rewrite Qproj0_n_t_bits; auto.
    + intros.
      apply Cconj_real.
      unfold Qop_Hermitian, Den_unitary, Den_prob_1, Den_prob, Mmult in *.
      rewrite Mtrace_Cconj.
      repeat rewrite Hct.
      rewrite Mconjtrans_twice.
      rewrite IHH.
      rewrite Qproj1_n_t_Hermitian.
      rewrite Htrcomm at 1.
      replace
      (Mmult_unsafe uop (Mmult_unsafe den (Mconjtrans uop))) with
      (Mmult_unsafe (Mmult_unsafe uop den) (Mconjtrans uop)).
      reflexivity.
      apply Hassoc.
      all: simpl_bits; repeat rewrite Qproj1_n_t_bits; auto.
    + intros.
      unfold Qop_Hermitian, Den_unitary.
      unfold Mmult in *.
      repeat rewrite Hct.
      rewrite IHH.
      rewrite Mconjtrans_twice.
      rewrite Hassoc.
      reflexivity.
      all: simpl_bits; lia.
  - destruct IHDensityMatrix as [IH0 [IH1 IHH] ].
    specialize Mtrace_Mmult_comm as Htrcomm.
    specialize Mmult_assoc as Hassoc.
    specialize Mconjtrans_mult as Hct.
    specialize Mmult_smul_comm_l as Hms.
    specialize Qproj0_n_t_mult as Hpp.
    split; [|split].
    + intros.
      unfold Den_measure_0, Den_measure, Den_prob, Den_prob_0, Den_prob, Mmult in *.
      rewrite Hms.
      rewrite Mtrace_Msmul.
      apply Cmult_real.
      apply Cimag_0_inv.
      auto.
      repeat rewrite Hassoc.
      rewrite Htrcomm.
      repeat rewrite Hassoc.
      rewrite Hpp.





Lemma DensityMatrix_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_Hermitian den.
Proof.
  intros.
  induction H.
  - induction H.
    + unfold Qop_Hermitian, eye, Mconjtrans.
      apply Mequal.
      * reflexivity.
      * intros.
        simpl_bits.
        simpl in *.
        assert (i = 0) by lia; subst i.
        assert (j = 0) by lia; subst j.
        simpl.
        lca.
    + apply Den_0_Hermitian.
    + apply Den_1_Hermitian.
    + apply TMproduct_Hermitian.
      apply IHInitialDensityMatrix1.
      apply IHInitialDensityMatrix2.
  - unfold Qop_Hermitian, Den_unitary.
    specialize Mconjtrans_mult as Hconjtrans.
    specialize Mmult_assoc as Hassoc.
    unfold Mmult in *.
    repeat rewrite Hconjtrans.
    rewrite IHDensityMatrix.
    rewrite Mconjtrans_twice.
    rewrite Hassoc.
    reflexivity.
    all: simpl_bits; lia.
  - specialize Mconjtrans_plus as Hconjplus.
    specialize Mconjtrans_mult as Hconjmult.
    specialize Mmult_assoc as Hassoc.
    unfold Qop_Hermitian, Den_measure, Den_measure_2, Mmult, Mplus in *.
    rewrite Hconjplus.
    repeat rewrite Hconjmult.
    repeat rewrite TMproduct_Mconjtrans.
    repeat rewrite Qop_Hermitian_eye.
    rewrite Qproj0_n_t_Hermitian.
    rewrite Qproj1_n_t_Hermitian.
    rewrite IHDensityMatrix.
    repeat rewrite Hassoc.
    reflexivity.
    all: repeat simpl_bits; repeat rewrite Qproj0_n_t_bits; repeat rewrite Qproj1_n_t_bits; lia.
  - specialize Mconjtrans_mult as Hconjmult.
    specialize Mmult_assoc as Hassoc.
    unfold Den_measure_0, Den_prob, Mmult in *.
    apply Msmul_Hermitian.
    unfold Qop_Hermitian.
    repeat rewrite Hconjmult.
    rewrite Qproj0_n_t_Hermitian.
    rewrite IHDensityMatrix.
    repeat rewrite Hassoc.
    reflexivity.
    1-10: repeat simpl_bits; repeat rewrite Qproj0_n_t_bits; repeat rewrite Qproj1_n_t_bits; lia.
    apply Cimag_0_inv.
    apply
    unfold Cinv, Creal.
    simpl.
    lra.
  - specialize Mconjtrans_mult as Hconjmult.
    specialize Mmult_assoc as Hassoc.
    unfold Den_measure_1, Den_prob, Mmult in *.
    apply Msmul_Hermitian.
    unfold Qop_Hermitian.
    repeat rewrite Hconjmult.
    rewrite Qproj1_n_t_Hermitian.
    rewrite IHDensityMatrix.
    repeat rewrite Hassoc.
    reflexivity.
    1-10: repeat simpl_bits; repeat rewrite Qproj0_n_t_bits; repeat rewrite Qproj1_n_t_bits; lia.
    unfold Cinv, Creal.
    simpl.
    lra.
Qed.

(* ============================================================================================== *)
(* density matrices are normalized ============================================================== *)

Lemma DensityMatrix_normalized: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Den_normalized den.
Proof.
  intros.
  induction H.
  - induction H.
    + unfold Den_normalized, eye, Mtrace, func_sum, func_sum2, func_sum_suppl.
      lca.
    + apply Den_0_normalized.
    + apply Den_1_normalized.
    + apply TMproduct_normalized.
      apply IHInitialDensityMatrix1.
      apply IHInitialDensityMatrix2.
  - unfold Den_normalized, Den_unitary.
    erewrite Mtrace_Mmult_comm.
    erewrite <- Mmult_assoc.
    destruct H0 as [Hu1 Hu2].
    specialize Mmult_eye_l as Heyel.
    unfold Qop_unitary_l, Qop_unitary_r, Mmult in *.
    rewrite Hu2.
    rewrite H1.
    rewrite Heyel.
    apply IHDensityMatrix.
    Unshelve.
    1-3: simpl_bits; reflexivity.
    simpl_bits; lia.
    simpl_bits. lia.
  - specialize Qproj_eye_minus_0n as Hproj.
    specialize Mtrace_Mplus_dist as Htraceplus.
    specialize Mtrace_Mminus_dist as Htraceminus.
    specialize Mmult_dist_minus_l as Hdml.
    specialize Mmult_dist_minus_r as Hdmr.
    specialize Mmult_assoc as Hma.
    specialize Mtrace_Mmult_comm as Htmc.
    specialize Mmult_eye_r as Heyer.
    specialize Mmult_eye_l as Heyel.
    specialize Qproj0_n_t_mult as Hpm.
    unfold Den_normalized, Den_measure, Den_measure_2, Mmult, Mplus, Mminus in *.
    rewrite Hproj.
    repeat rewrite Hdml.
    repeat rewrite Hdmr.
    repeat rewrite Hma.
    repeat rewrite Heyer.
    repeat rewrite Heyel.
    repeat rewrite Htraceplus.
    repeat rewrite Htraceminus.
    rewrite <- Hma.
    rewrite Htmc.
    rewrite <- Hma.
    rewrite Hpm.
    ring_simplify.
    rewrite Htmc.
    rewrite IHDensityMatrix.
    lca.
    all: repeat simpl_bits; repeat rewrite Qproj0_n_t_bits; lia.
  - specialize Mtrace_Mmult_comm as Hcomm.
    specialize Mmult_assoc as Hassoc.
    specialize Qproj0_n_t_mult as H0nt.
    unfold Den_normalized, Den_measure_0, Den_prob, Mmult, Mplus, Mminus in *.
    rewrite Mtrace_Msmul.
    replace (Mtrace (Mmult_unsafe (Mmult_unsafe (Qproj0_n_t n t Ht) den) (Qproj0_n_t n t Ht))) with
      (Mtrace (Mmult_unsafe (Qproj0_n_t n t Ht) (Mmult_unsafe (Qproj0_n_t n t Ht) den))).
    rewrite <- Hassoc.
    rewrite H0nt.
    rewrite Hcomm.
    lca.
    rewrite Hcomm.
    rewrite
Qed.

(* ============================================================================================== *)
(* density matrices are positive ================================================================ *)

Lemma DensityMatrix_positive: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_positive den.
Proof.
  intros.
  induction H.
  - eapply InitialDensityMatrix_positive.
    apply H.
  - unfold Qop_positive, Den_unitary in *.
    intros.
    specialize Mmult_assoc as Hma.
    specialize MMVmult_assoc as Hva.
    specialize VMVmult_assoc as Hvva.
    specialize CVconjtrans_mult as Hccm.
    unfold MVmult, VMmult, Mmult, dot_product.
    repeat simpl_bits.
    unfold MVmult, VMmult, Mmult, dot_product in *.
    rewrite Hma.
    repeat rewrite Hva.
    rewrite Hvva.
    replace uop with (Mconjtrans (Mconjtrans uop)).
    rewrite <- Hccm.
    rewrite Mconjtrans_twice.
    apply IHDensityMatrix.
    unfold MVmult_unsafe.
    simpl.
    lia.
    simpl_bits.
    unfold MVmult_unsafe.
    reflexivity.
    1-2: simpl_bits; lia.
    apply Mconjtrans_twice.
    all: unfold MVmult_unsafe; simpl; simpl_bits; lia.
  - specialize Qop_positive_plus as Hplus.
    specialize Mmult_assoc as Hma.
    specialize MMVmult_assoc as Hva.
    specialize VMVmult_assoc as Hvva.
    specialize CVconjtrans_mult as Hccm.
    unfold Qop_positive in *.
    intros.
    simpl_bits.
    unfold Den_measure, Den_measure_2, Mmult, Mplus, VMmult, MVmult, dot_product in *.
    simpl_bits.
    apply Hplus.
    unfold Mmult_unsafe; simpl; lia.
    intros.
    repeat rewrite Hva.
    rewrite Hvva.
    replace
      (VMmult_unsafe (CVconjtrans c0) (Qproj0_n_t n t Ht)) with
      (VMmult_unsafe (CVconjtrans c0) (Mconjtrans (Qproj0_n_t n t Ht))).
    rewrite <- Hccm.
    apply IHDensityMatrix.
    1-4: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
    replace (Mconjtrans (Qproj0_n_t n t Ht)) with (Qproj0_n_t n t Ht).
    reflexivity.
    symmetry.
    apply Qproj0_n_t_Hermitian.
    1-12: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
    intros.
    repeat rewrite Hva.
    rewrite Hvva.
    replace
      (VMmult_unsafe (CVconjtrans c0) (Qproj1_n_t n t Ht)) with
      (VMmult_unsafe (CVconjtrans c0) (Mconjtrans (Qproj1_n_t n t Ht))).
    rewrite <- Hccm.
    apply IHDensityMatrix.
    1-4: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
    replace (Mconjtrans (Qproj1_n_t n t Ht)) with (Qproj1_n_t n t Ht).
    reflexivity.
    symmetry.
    apply Qproj1_n_t_Hermitian.
    all: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
  - specialize Mmult_assoc as Hma.
    specialize MMVmult_assoc as Hva.
    specialize VMVmult_assoc as Hvva.
    specialize CVconjtrans_mult as Hccm.
    unfold Qop_positive in *.
    intros.
    simpl_bits.
    unfold Den_measure_0, Den_prob, Mmult, Mplus, VMmult, MVmult, dot_product in *.
    simpl_bits.
    unfold Mmult_unsafe; simpl; lia.
    intros.
    repeat rewrite Hva.
    rewrite Hvva.
    replace
      (VMmult_unsafe (CVconjtrans c0) (Qproj0_n_t n t Ht)) with
      (VMmult_unsafe (CVconjtrans c0) (Mconjtrans (Qproj0_n_t n t Ht))).
    rewrite <- Hccm.
    apply IHDensityMatrix.
    1-4: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
    replace (Mconjtrans (Qproj0_n_t n t Ht)) with (Qproj0_n_t n t Ht).
    reflexivity.
    symmetry.
    apply Qproj0_n_t_Hermitian.
    1-12: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
    intros.
    repeat rewrite Hva.
    rewrite Hvva.
    replace
      (VMmult_unsafe (CVconjtrans c0) (Qproj1_n_t n t Ht)) with
      (VMmult_unsafe (CVconjtrans c0) (Mconjtrans (Qproj1_n_t n t Ht))).
    rewrite <- Hccm.
    apply IHDensityMatrix.
    1-4: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
    replace (Mconjtrans (Qproj1_n_t n t Ht)) with (Qproj1_n_t n t Ht).
    reflexivity.
    symmetry.
    apply Qproj1_n_t_Hermitian.
    all: unfold MVmult_unsafe, VMmult_unsafe in *; simpl_bits; simpl in *; lia.
Qed.

(* ============================================================================================== *)
(* QASM 2.0 density matrix initialzation (zeros) ================================================ *)

Fixpoint Den_0_init (n: nat): Matrix :=
  match n with
  | O => eye O
  | S n' => TMproduct Den_0 (Den_0_init n')
  end.

Lemma Den_0_init_bits: forall n, Mbits (Den_0_init n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Den_0_init_DensityMatrix: forall n, DensityMatrix n (Den_0_init n).
Proof.
  intros.
  apply DensityMatrix_init.
  induction n.
  - simpl.
    apply DensityMatrix_empty.
  - simpl.
    replace (S n) with (1 + n)%nat by lia.
    apply DensityMatrix_TMproduct.
    apply DensityMatrix_0.
    apply IHn.
Qed.

(* ============================================================================================== *)

