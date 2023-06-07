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

Lemma Den_0_normalized: Den_normalized Den_0.
Proof. lca. Qed.

Lemma Den_1_normalized: Den_normalized Den_1.
Proof. lca. Qed.

(* ============================================================================================== *)
(* measurement ================================================================================== *)

Definition Den_measure (n t: nat) (den: Matrix) (Ht: t < n) (Hd: Mbits den = n): Matrix.
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
Qed.

(* ============================================================================================== *)
(* density matrix =============================================================================== *)

Inductive DensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_0: DensityMatrix 1 Den_0
| DensityMatrix_1: DensityMatrix 1 Den_1
| DensityMatrix_TMproduct (n1 n2: nat) (den1 den2: Matrix):
  DensityMatrix n1 den1 ->
  DensityMatrix n2 den2 ->
  DensityMatrix (n1 + n2) (TMproduct den1 den2)
| DensityMatrix_unitary (n: nat) (den uop: Matrix) (H1: _) (H2: _):
  DensityMatrix n den ->
  Qop_unitary uop ->
  DensityMatrix n (Mmult (Mmult uop den H1) (Mconjtrans uop) H2).

(* ============================================================================================== *)
(* normalization of density matrices ============================================================ *)

Lemma DensityMatrix_normalized: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Den_normalized den.
Proof.
  intros.
  induction H.
  - apply Den_0_normalized.
  - apply Den_1_normalized.
  - apply TMproduct_normalized.
    apply IHDensityMatrix1.
    apply IHDensityMatrix2.
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
Qed.

(* ============================================================================================== *)

