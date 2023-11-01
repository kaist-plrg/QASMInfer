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
  apply Mequal_unsafe.
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
  apply Mequal_unsafe.
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
  apply Mequal_unsafe.
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

Lemma Den_unitary_Mconjtrans: forall (den uop: Matrix) (H1: _) (H2: _),
  Mconjtrans (Den_unitary den uop H1 H2) = Den_unitary (Mconjtrans den) uop H1 H2.
Proof.
  intros.
  specialize Mconjtrans_mult as Hcm.
  specialize Mconjtrans_twice as Hct.
  specialize Mmult_assoc as Hassoc.
  unfold Den_unitary, Mmult in *; simpl.
  erewrite Hcm.
  rewrite Hct.
  rewrite Hcm.
  symmetry.
  apply Hassoc.
  all: simpl_bits; try lia.
  symmetry.
  apply Mmult_unsafe_bits_l.
Qed.

Lemma Den_unitary_positive: forall (den uop: Matrix) (H1: _) (H2: _),
  Qop_positive den -> Qop_positive (Den_unitary den uop H1 H2).
Proof.
  intros.
  unfold Den_unitary.
  apply Qop_positive_mult_r.
  apply H.
Qed.

(* ============================================================================================== *)
(* apply reset to density matrix ================================================================ *)

Definition Den_reset (den: Matrix) (t: nat) (Ht: t < Mbits den): Matrix.
Proof.
  refine (
    Mplus
      (Mmult (Mmult (Qproj0_n_t (Mbits den) t Ht) den _) (Qproj0_n_t (Mbits den) t Ht) _)
      (Den_unitary
        (Mmult (Mmult (Qproj1_n_t (Mbits den) t Ht) den _) (Qproj1_n_t (Mbits den) t Ht) _)
        (Qop_sq (Mbits den) t (Qop_rot PI 0 PI) _ _) _ _)
      _
  ).
  Unshelve.
  all: try unfold MMeqbits.
  - simpl_bits.
    rewrite Den_unitary_bits.
    repeat simpl_bits.
    reflexivity.
  - apply Qproj0_n_t_bits.
  - repeat simpl_bits.
    reflexivity.
  - apply Qproj1_n_t_bits.
  - repeat simpl_bits.
    reflexivity.
  - lia.
  - apply Qop_rot_bits.
  - repeat simpl_bits.
    rewrite Qop_sq_bits.
    unfold Mmult.
    simpl_bits.
    symmetry.
    apply Qproj1_n_t_bits.
  - unfold Mmult, Mplus.
    simpl_bits.
    rewrite Qop_sq_bits.
    reflexivity.
Defined.

Lemma Den_reset_bits : forall (den: Matrix) (t: nat) (Ht: t < Mbits den),
  MMeqbits (Den_reset den t Ht) den.
Proof.
  intros.
  unfold Den_reset, Mmult.
  repeat simpl_bits.
  apply Qproj0_n_t_bits.
Qed.

Lemma Den_reset_Mconjtrans : forall (den: Matrix) (t: nat) (Ht: t < Mbits den),
  Mconjtrans (Den_reset den t Ht) = (Den_reset (Mconjtrans den) t Ht).
Proof.
  intros.
  specialize Mconjtrans_mult as Hcm.
  specialize Mmult_assoc as Hassoc.
  specialize Den_unitary_Mconjtrans as Hcu.
  specialize Qproj0_n_t_proj as Hp0.
  specialize Qproj1_n_t_proj as Hp1.
  assert (
    forall (n t : nat) (Ht : t < n), Mconjtrans (Qproj0_n_t n t Ht) = Qproj0_n_t n t Ht
  ) as Hcp0 by eapply Hp0.
  assert (
    forall (n t : nat) (Ht : t < n), Mconjtrans (Qproj1_n_t n t Ht) = Qproj1_n_t n t Ht
  ) as Hcp1 by eapply Hp1.
  unfold Den_reset; simpl; simpl_bits.
  erewrite Mconjtrans_plus.
  unfold Mmult, Mplus in *; simpl.
  repeat erewrite Hcm.
  repeat rewrite Hcu.
  repeat rewrite Hcp0.
  erewrite <- Hassoc.
  unfold Den_unitary, Qproj0_n_t, Mmult, Qop_sq in *; simpl; simpl_bits.
  repeat rewrite Hcm.
  erewrite Hcp1.
  repeat rewrite Hassoc.
  reflexivity.
  Unshelve.
  all: simpl_bits; simpl; try lia.
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

Lemma InitialDensityMatrix_prob_real_Hermitian: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> (forall proj, Projection proj ->
  (forall Hd, (Cimag (Den_prob den proj Hd) = 0%R))) /\ Qop_Hermitian den.
Proof.
  intros.
  specialize Mconjtrans_mult as Hcm.
  specialize Mtrace_Mmult_comm as Hcomm.
  induction H.
  - split.
    + intros.
      destruct H as [Hp [HH _] ].
      unfold Den_prob.
      rewrite Mmult_eye_l.
      apply Cconj_real.
      rewrite Mtrace_Cconj.
      rewrite HH.
      reflexivity.
      simpl_bits.
      apply Hd.
    + apply Qop_Hermitian_eye.
  - split.
    + intros.
      destruct H as [Hp [HH _] ].
      unfold Den_prob.
      apply Cconj_real.
      rewrite Mtrace_Cconj.
      unfold Mmult in *.
      rewrite Hcm.
      rewrite HH.
      rewrite Den_0_Hermitian.
      rewrite Hcomm.
      reflexivity.
      all: simpl_bits; auto.
    + unfold Qop_Hermitian, eye, Mconjtrans.
      simpl.
      apply Mequal.
      * reflexivity.
      * simpl_bits.
        simpl.
        intros.
        destruct i as [|[|i] ], j as [|[|j] ].
        all: lca.
  - split.
    + intros.
      destruct H as [Hp [HH _] ].
      unfold Den_prob.
      apply Cconj_real.
      rewrite Mtrace_Cconj.
      unfold Mmult in *.
      rewrite Hcm.
      rewrite HH.
      rewrite Den_1_Hermitian.
      rewrite Hcomm.
      reflexivity.
      all: simpl_bits; auto.
    + unfold Qop_Hermitian, eye, Mconjtrans.
      simpl.
      apply Mequal.
      * reflexivity.
      * simpl_bits.
        simpl.
        intros.
        destruct i as [|[|i] ], j as [|[|j] ].
        all: lca.
  - split.
    + intros.
      destruct H1 as [Hp [HH _] ].
      unfold Den_prob.
      apply Cconj_real.
      rewrite Mtrace_Cconj.
      unfold Mmult in *.
      rewrite Hcm.
      rewrite TMproduct_Hermitian.
      rewrite HH.
      rewrite Hcomm.
      reflexivity.
      all: simpl_bits; auto.
      destruct IHInitialDensityMatrix1 as [_ HH1].
      apply HH1.
      destruct IHInitialDensityMatrix2 as [_ HH2].
      apply HH2.
    + apply TMproduct_Hermitian.
      destruct IHInitialDensityMatrix1 as [_ HH1].
      apply HH1.
      destruct IHInitialDensityMatrix2 as [_ HH2].
      apply HH2.
Qed.

Lemma InitialDensityMatrix_prob_real: forall (n: nat) (den proj: Matrix),
  InitialDensityMatrix n den -> Projection proj -> (forall Hd, (Cimag (Den_prob den proj Hd) = 0%R)).
Proof.
  intros.
  destruct (InitialDensityMatrix_prob_real_Hermitian n den).
  apply H.
  apply H1.
  apply H0.
Qed.

Lemma InitialDensityMatrix_Hermitian: forall (n: nat) (den proj: Matrix),
  InitialDensityMatrix n den -> Projection proj -> Qop_Hermitian den.
Proof.
  intros.
  destruct (InitialDensityMatrix_prob_real_Hermitian n den).
  apply H.
  apply H2.
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
    apply Mequal_unsafe.
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
  apply Qop_positive_pure.
  eapply InitialDensityMatrix_pure.
  apply H.
Qed.

Lemma InitialDensityMatrix_prob_pos: forall (n: nat) (den proj: Matrix),
  InitialDensityMatrix n den -> Projection proj -> (forall Hd, Cge_0 (Den_prob den proj Hd)).
Proof.
  intros.
  destruct H0 as [Hp1 [Hp2 Hp3] ].
  assert (MMeqbits proj proj) as Hpp by reflexivity.
  specialize (Hp1 Hpp).
  specialize Mmult_assoc as Hassoc.
  specialize Mtrace_Mmult_comm as Hcomm.
  specialize Qop_positive_mult_l as Hposm.
  unfold Den_prob.
  unfold Mmult in *.
  rewrite <- Hp1.
  rewrite <- Hassoc.
  rewrite Hcomm.
  apply Qop_positive_trace.
  rewrite <- Hassoc.
  unfold Qop_Hermitian in Hp2.
  rewrite <- Hp2 at 1.
  apply Hposm.
  3: eapply InitialDensityMatrix_positive; apply H.
  all: try auto; simpl_bits; lia.
Qed.

Lemma InitialDensityMatrix_normalized: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> Den_normalized den.
Proof.
  intros.
  induction H.
  + unfold Den_normalized, eye, Mtrace, func_sum, func_sum2, func_sum_suppl.
    lca.
  + apply Den_0_normalized.
  + apply Den_1_normalized.
  + apply TMproduct_normalized.
    apply IHInitialDensityMatrix1.
    apply IHInitialDensityMatrix2.
Qed.

(* ============================================================================================== *)
(* density matrix =============================================================================== *)

Inductive DensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_init (n: nat) (den: Matrix): InitialDensityMatrix n den -> DensityMatrix n den
| DensityMatrix_unitary (n: nat) (den uop: Matrix) (H1: _) (H2: _):
    DensityMatrix n den ->
    Qop_unitary uop ->
    DensityMatrix n (Den_unitary den uop H1 H2)
| DensityMatrix_measure (n: nat) (den proj: Matrix) (Hd: _):
    DensityMatrix n den ->
    Projection proj ->
    Den_prob den proj Hd <> 0 ->
    DensityMatrix n (Den_measure den proj Hd)
| DensityMatrix_reset (n: nat) (den: Matrix) (t: nat) (Ht: t < Mbits den):
    DensityMatrix n den ->
    DensityMatrix n (Den_reset den t Ht).

(* ============================================================================================== *)
(* density matrices are Hermitian =============================================================== *)

Lemma DensityMatrix_prob_real_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> (forall proj, Projection proj ->
  (forall Hd, (Cimag (Den_prob den proj Hd) = 0%R))) /\ Qop_Hermitian den.
Proof.
  intros.
  induction H.
  - eapply InitialDensityMatrix_prob_real_Hermitian.
    apply H.
  - split.
    + specialize Mconjtrans_mult as Hcm.
      specialize Mtrace_Mmult_comm as Hcomm.
      specialize Mmult_assoc as Hassoc.
      unfold Den_unitary, Den_prob, Mmult in *.
      intros.
      simpl_bits.
      assert (Mbits den = Mbits proj) as Hdp by lia.
      destruct IHDensityMatrix as [IH1 IH2].
      specialize (IH1 proj H3 Hdp).
      destruct H3 as [Hp1 [Hp2 Hp3] ].
      apply Cconj_real.
      rewrite Mtrace_Cconj.
      repeat rewrite Hcm.
      repeat rewrite Mconjtrans_twice.
      repeat rewrite Hp2.
      rewrite IH2.
      rewrite Hcomm.
      repeat rewrite Hassoc.
      reflexivity.
      all: simpl_bits; lia.
    + specialize Mconjtrans_mult as Hcm.
      specialize Mmult_assoc as Hassoc.
      unfold Den_unitary, Mmult, Qop_Hermitian in *.
      intros.
      simpl_bits.
      destruct IHDensityMatrix as [IH1 IH2].
      repeat rewrite Hcm.
      repeat rewrite Mconjtrans_twice.
      rewrite IH2.
      repeat rewrite Hassoc.
      reflexivity.
      all: simpl_bits; lia.
  - split.
    + specialize Mconjtrans_mult as Hcm.
      specialize Mtrace_Mmult_comm as Hcomm.
      specialize Mmult_assoc as Hassoc.
      specialize Mconjtrans_Msmul as Hcs.
      unfold Den_unitary, Den_measure, Den_prob, Mmult in *.
      intros.
      simpl_bits.
      assert (Mbits den = Mbits proj) as Hdp by lia.
      apply Cconj_real.
      rewrite Mtrace_Cconj.
      repeat rewrite Hcm.
      rewrite Hcs.
      rewrite Hcomm.
      rewrite Creal_conj.
      repeat rewrite Hcm.
      destruct H0 as [Hp01 [Hp02 Hp03] ].
      destruct H2 as [Hp11 [Hp12 Hp13] ].
      rewrite Hp02.
      rewrite Hp12.
      destruct IHDensityMatrix as [IH1 IH2].
      rewrite IH2.
      rewrite Hassoc.
      reflexivity.
      1-10: simpl_bits; lia.
      apply Cimag_0_inv.
      destruct IHDensityMatrix as [IH1 IH2].
      apply IH1.
      apply H0.
      all: repeat simpl_bits; lia.
    + specialize Mconjtrans_mult as Hcm.
      specialize Mtrace_Mmult_comm as Hcomm.
      specialize Mmult_assoc as Hassoc.
      specialize Mconjtrans_Msmul as Hcs.
      unfold Den_unitary, Den_measure, Den_prob, Mmult, Qop_Hermitian in *.
      intros.
      simpl_bits.
      assert (Mbits den = Mbits proj) as Hdp by lia.
      rewrite Hcs.
      repeat rewrite Hcm.
      rewrite Creal_conj.
      destruct H0 as [Hp01 [Hp02 Hp03] ].
      rewrite Hp02.
      destruct IHDensityMatrix as [IH1 IH2].
      rewrite IH2.
      rewrite Hassoc.
      reflexivity.
      1-4: simpl_bits; lia.
      apply Cimag_0_inv.
      destruct IHDensityMatrix as [IH1 IH2].
      apply IH1.
      apply H0.
      all: repeat simpl_bits; lia.
  - split.
    + intros.
      specialize Mtrace_Mmult_comm as Hcomm.
      apply Cconj_real.
      unfold Den_prob.
      rewrite Mtrace_Cconj.
      erewrite Mconjtrans_mult.
      destruct H0 as [Hp1 [Hp2 Hp3] ].
      unfold Mmult in *.
      rewrite Hp2.
      rewrite Hcomm.
      assert (Mconjtrans den = den) as Hden by apply IHDensityMatrix.
      rewrite Den_reset_Mconjtrans.
      unfold Den_reset, Mplus, Mmult; simpl.
      rewrite Hden.
      reflexivity.
      Unshelve.
      all: simpl_bits; lia.
    + unfold Qop_Hermitian.
      rewrite Den_reset_Mconjtrans.
      assert (Mconjtrans den = den) as Hden by apply IHDensityMatrix.
      unfold Den_reset, Mplus, Mmult; simpl.
      rewrite Hden.
      reflexivity.
Qed.

Lemma DensityMatrix_prob_real: forall (n: nat) (den proj: Matrix),
  DensityMatrix n den -> Projection proj -> (forall Hd, (Cimag (Den_prob den proj Hd) = 0%R)).
Proof.
  intros.
  destruct (DensityMatrix_prob_real_Hermitian n den) as [Hr _].
  apply H.
  apply Hr.
  apply H0.
Qed.

Lemma DensityMatrix_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_Hermitian den.
Proof.
  intros.
  destruct (DensityMatrix_prob_real_Hermitian n den) as [_ Hd].
  apply H.
  apply Hd.
Qed.

(* ============================================================================================== *)
(* density matrices are positive ================================================================ *)

Lemma DensityMatrix_prob_pos_positive: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> (forall proj, Projection proj ->
  (forall Hd, Cge_0 (Den_prob den proj Hd))) /\ Qop_positive den.
Proof.
  intros.
  induction H.
  - split.
    + intros.
      eapply InitialDensityMatrix_prob_pos.
      apply H.
      apply H0.
    + eapply InitialDensityMatrix_positive.
      apply H.
  - split.
    + specialize Mconjtrans_mult as Hcm.
      specialize Mtrace_Mmult_comm as Hcomm.
      specialize Mmult_assoc as Hassoc.
      specialize Qop_positive_mult_r as Hposm.
      specialize DensityMatrix_unitary as Hunitary.
      unfold Den_unitary, Den_prob, Mmult in *.
      intros.
      split.
      * simpl_bits.
        destruct H3 as [Hp1 [Hp2 Hp3] ].
        assert (MMeqbits proj proj) as Hpp by reflexivity.
        specialize (Hp1 Hpp).
        unfold Mmult in *.
        rewrite <- Hp1.
        rewrite <- Hassoc.
        rewrite Hcomm.
        apply Qop_positive_trace.
        rewrite <- Hassoc.
        unfold Qop_Hermitian in Hp2.
        rewrite <- Hp2 at 1.
        rewrite Hassoc.
        rewrite Hassoc.
        rewrite Hassoc.
        rewrite <- Hassoc.
        rewrite <- Hassoc.
        replace (Mmult_unsafe (Mconjtrans uop) proj) with (Mconjtrans (Mmult_unsafe (Mconjtrans proj) uop)).
        apply Hposm.
        1-2:try auto; repeat simpl_bits; lia.
        destruct IHDensityMatrix as [_ IH].
        apply IH.
        rewrite Hcm.
        rewrite Mconjtrans_twice.
        reflexivity.
        all: try auto; repeat simpl_bits; lia.
      * eapply DensityMatrix_prob_real.
        apply Hunitary.
        1-2: simpl_bits; lia.
        apply H.
        apply H0.
        apply H3.
    + specialize Mconjtrans_mult as Hcm.
      specialize Mmult_assoc as Hassoc.
      specialize Mtrace_Mmult_comm as Hcomm.
      specialize Qop_positive_mult_r as Hposm.
      specialize DensityMatrix_unitary as Hunitary.
      unfold Den_unitary, Den_prob, Mmult in *.
      intros.
      simpl_bits.
      apply Hposm.
      1-2: simpl_bits; lia.
      destruct IHDensityMatrix as [_ IH].
      apply IH.
  - split.
    + intros.
      specialize DensityMatrix_measure as Hmeasure.
      split.
      * specialize Mconjtrans_mult as Hcm.
        specialize Mtrace_Mmult_comm as Hcomm.
        specialize Mmult_assoc as Hassoc.
        specialize Mconjtrans_Msmul as Hcs.
        specialize Mmult_smul_comm_l as Hms.
        specialize Mtrace_Msmul as Hts.
        specialize Qop_positive_mult_Hermitian as HpH.
        unfold Den_unitary, Den_measure, Den_prob, Mmult in *.
        simpl_bits.
        rewrite Hms.
        rewrite Hts.
        apply Cge_0_mult.
        apply Cge_0_inv.
        destruct IHDensityMatrix as [IH _].
        apply IH.
        apply H0.
        simpl_bits; lia.
        destruct H2 as [Hp01 [Hp02 Hp03] ].
        unfold Mmult in *.
        erewrite <- Hp01.
        repeat rewrite <- Hassoc.
        rewrite Hcomm.
        apply Qop_positive_trace.
        rewrite <- Hassoc.
        apply HpH.
        1-2: simpl_bits; lia.
        apply HpH.
        1-2: simpl_bits; lia.
        destruct IHDensityMatrix as [_ IH].
        apply IH.
        destruct H0 as [_ [Hp _] ].
        apply Hp.
        apply Hp02.
        Unshelve.
        all: simpl_bits; lia.
      * eapply DensityMatrix_prob_real.
        apply Hmeasure.
        apply H.
        apply H0.
        apply H1.
        apply H2.
    + unfold Den_measure, Mmult.
      destruct IHDensityMatrix as [IH1 IH2].
      apply Qop_positive_smult.
      destruct H0 as [Hp1 [Hp2 Hp3] ].
      eapply Qop_positive_mult_Hermitian.
      apply IH2.
      apply Hp2.
      apply Cge_0_inv.
      apply IH1.
      apply H0.
      Unshelve.
      all: simpl_bits; lia.
  - destruct IHDensityMatrix as [IH1 IH2].
    specialize Qop_positive_mult_l as Hposm.
    specialize Mmult_assoc as Hassoc.
    specialize Mtrace_Mmult_comm as Hcomm.
    specialize Mconjtrans_mult as Hcm.
    assert(Qop_positive (Den_reset den t Ht)) as Hres.
    { unfold Den_reset; simpl.
      apply Qop_positive_plus.
      - unfold Mmult in *.
        replace
          (Qproj0_n_t (Mbits den) t Ht)
        with
          (Mconjtrans (Qproj0_n_t (Mbits den) t Ht))
        at 1 by apply Qproj0_n_t_Hermitian.
        apply Hposm.
        all: repeat simpl_bits; try lia; auto.
        apply Qproj0_n_t_bits.
      - unfold Mmult in *.
        apply Den_unitary_positive.
        replace
          (Qproj1_n_t (Mbits den) t Ht)
        with
          (Mconjtrans (Qproj1_n_t (Mbits den) t Ht))
        at 1 by apply Qproj1_n_t_Hermitian.
        apply Hposm.
        all: repeat simpl_bits; try lia; auto.
        apply Qproj1_n_t_bits.
    }
    split.
    + intros.
      unfold Den_prob.
      destruct H0 as [Hp1 [Hp2 Hp3] ].
      unfold Mmult in *.
      rewrite <- Hp1.
      rewrite <- Hcomm.
      rewrite Hassoc.
      rewrite Hcomm.
      apply Qop_positive_trace.
      replace proj with (Mconjtrans proj) at 1.
      apply Hposm.
      all: repeat simpl_bits; try lia; auto.
    + exact Hres.
Qed.


Lemma DensityMatrix_prob_pos: forall (n: nat) (den proj: Matrix) Hd,
  DensityMatrix n den -> Projection proj -> Cge_0 (Den_prob den proj Hd).
Proof.
  intros.
  destruct (DensityMatrix_prob_pos_positive n den) as [Hp _].
  apply H.
  apply Hp.
  apply H0.
Qed.

Lemma DensityMatrix_positive: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_positive den.
Proof.
  intros.
  destruct (DensityMatrix_prob_pos_positive n den) as [_ Hp].
  apply H.
  apply Hp.
Qed.

(* ============================================================================================== *)
(* density matrices are normalized ============================================================== *)

Lemma DensityMatrix_normalized: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Den_normalized den.
Proof.
  intros.
  induction H.
  - eapply InitialDensityMatrix_normalized.
    apply H.
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
  - specialize Mtrace_Msmul as Hts.
    specialize Mtrace_Mmult_comm as Hcomm.
    specialize Mmult_assoc as Hassoc.
    destruct H0 as [Hp1 [Hp2 Hp3] ].
    unfold Den_normalized, Den_measure, Den_prob, Mmult, Mplus, Mminus in *.
    rewrite Hts.
    rewrite Hcomm.
    replace (Mtrace (Mmult_unsafe (Mmult_unsafe proj den) proj)) with
    (Mtrace (Mmult_unsafe proj (Mmult_unsafe proj den))).
    rewrite <- Hassoc.
    rewrite Hp1.
    apply Cinv_mult.
    rewrite Hcomm.
    apply H1.
    1-7: simpl_bits; lia.
    apply Hcomm.
    all: simpl_bits; lia.
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

