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
  unfold Den_normalized, Mtrace, TMproduct, Msize in *.
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
    unfold Mconjtrans, Den_1, Msize in *.
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
(* probability ================================================================================== *)

Definition Den_prob (den: Matrix) (proj: Matrix) (H: MMeqbits den proj): R :=
  Creal (Mtrace (Mmult den proj H)).

(* ============================================================================================== *)
(* measurement ================================================================================== *)

Definition Den_measure (den: Matrix) (n t: nat)  (Ht: t < n) (Hd: Mbits den = n): Matrix.
Proof.
  refine (
    Mplus (
      Mmult (
        Mmult (Qproj0_n_t n t Ht) den _
      ) (Qproj0_n_t n t Ht) _
    ) (
      Mmult (
        Mmult (Qproj1_n_t n t Ht) den _
      ) (Qproj1_n_t n t Ht) _
    ) _
  ).
  Unshelve.
  all: simpl_bits; simpl; lia.
Defined.

(* projection on 01001001.. is a projection on single  real: i.e. self-adjoint
Definition Den_measure_op (den proj op: Matrix) (H: MMeqbits den op) (H2: MMeqbits proj den): Matrix.
Proof.
  refine (
    Mplus (
      Mmult ( Mmult
      proj den _) proj
      _
    ) (
      Mmult ( Mmult
      (Mminus (eye (Mbits proj)) proj _) den _) (Mminus (eye (Mbits proj)) proj _)
      _
    ) _
  ).
  Unshelve.
  all: simpl_bits; simpl; lia.
Qed. *)

(* ============================================================================================== *)
(* density matrix at the initial state ========================================================== *)

Inductive InitialDensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_0: InitialDensityMatrix 1 Den_0
| DensityMatrix_1: InitialDensityMatrix 1 Den_1
| DensityMatrix_TMproduct (n1 n2: nat) (den1 den2: Matrix):
  InitialDensityMatrix n1 den1 ->
  InitialDensityMatrix n2 den2 ->
  InitialDensityMatrix (n1 + n2) (TMproduct den1 den2).

Lemma InitialDensityMatrix_pure: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den ->
  exists (qst: ColVec) (H: _),
  den = VVmult qst (CVconjtrans qst) H.
Proof.
  intros.
  induction H.
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

(* ============================================================================================== *)
(* density matrix =============================================================================== *)

Inductive DensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_init (n: nat) (den: Matrix): InitialDensityMatrix n den -> DensityMatrix n den
| DensityMatrix_unitary (n: nat) (den uop: Matrix) (H1: _) (H2: _):
  DensityMatrix n den ->
  Qop_unitary uop ->
  DensityMatrix n (Mmult (Mmult uop den H1) (Mconjtrans uop) H2)
| DensityMatrix_measure (den: Matrix) (n t: nat) (Ht: _) (Hd: _):
  DensityMatrix n den ->
  DensityMatrix n (Den_measure den n t Ht Hd).

(* ============================================================================================== *)
(* density matrices are Hermitian =============================================================== *)

Lemma DensityMatrix_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_Hermitian den.
Proof.
  intros.
  induction H.
  - induction H.
    + apply Den_0_Hermitian.
    + apply Den_1_Hermitian.
    + apply TMproduct_Hermitian.
      apply IHInitialDensityMatrix1.
      apply IHInitialDensityMatrix2.
  - unfold Qop_Hermitian.
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
    unfold Qop_Hermitian, Den_measure, Mmult, Mplus in *.
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
Qed.

(* ============================================================================================== *)
(* density matrices are positive ================================================================ *)

(* Lemma DensityMatrix_positive: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_positive den.
Proof.
  intros.
  induction H.
  - apply Den_0_positive.
  - apply Den_1_positive.
  - *)

(* ============================================================================================== *)
(* density matrices are normalized ============================================================== *)

Lemma DensityMatrix_normalized: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Den_normalized den.
Proof.
  intros.
  induction H.
  - induction H.
    + apply Den_0_normalized.
    + apply Den_1_normalized.
    + apply TMproduct_normalized.
      apply IHInitialDensityMatrix1.
      apply IHInitialDensityMatrix2.
  - unfold Den_normalized.
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
    unfold Den_normalized, Den_measure, Mmult, Mplus, Mminus in *.
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
Qed.

(* ============================================================================================== *)

