Require Export MatrixVector.
From Stdlib Require Import Program.Equality.

Open Scope Matrix_scope.

Definition tensor_product {m n: nat} (A: Matrix m) (B: Matrix n) : Matrix (m + n).
Proof.
  induction A.
  - exact (c .* B).
  - exact (rec_mat IHA1 IHA2 IHA3 IHA4).
Defined.

Notation "A ⊗ B" := (tensor_product A B) (at level 36) : Matrix_scope.

Section PROPERTIES.

Lemma tprod_scale_assoc: forall {m n} (A: Matrix m) (B: Matrix n) (c: Complex),
  c .* (A ⊗ B) = c .* A ⊗ B.
Proof.
  intros.
  induction A as [a | ].
  - simpl.
    rewrite mat_scale_scale_comm.
    reflexivity.
  - simpl. f_equal; assumption.
Qed.

Lemma tprod_assoc: forall {m n k} (A: Matrix m) (B: Matrix n) (C: Matrix k),
  mat_ccast (A ⊗ (B ⊗ C)) add_assoc = A ⊗ B ⊗ C.
Proof.
  intros.
  induction A as [a|m].
  - simpl. rewrite tprod_scale_assoc. mat_cast.
  - simpl. f_equal.
    + rewrite <- IHA1. mat_cast.
    + rewrite <- IHA2. mat_cast.
    + rewrite <- IHA3. mat_cast.
    + rewrite <- IHA4. mat_cast.
Qed.

Lemma tprod_assoc': forall {m n k} (A: Matrix m) (B: Matrix n) (C: Matrix k),
  mat_ccast (A ⊗ B ⊗ C) (eq_sym add_assoc) = A ⊗ (B ⊗ C).
Proof.
  intros.
  induction A as [a|m].
  - simpl. rewrite tprod_scale_assoc. apply mat_ccast_refl.
  - simpl. f_equal.
    + rewrite <- IHA1. mat_cast.
    + rewrite <- IHA2. mat_cast.
    + rewrite <- IHA3. mat_cast.
    + rewrite <- IHA4. mat_cast.
Qed.

Lemma tprod_assoc_JMeq: forall {m n k} (A: Matrix m) (B: Matrix n) (C: Matrix k),
  JMeq (A ⊗ B ⊗ C) (A ⊗ (B ⊗ C)).
Proof.
  intros.
  rewrite <- tprod_assoc.
  mat_cast. do_JMeq.
Qed.

Lemma tprod_eq: forall {m n} (A C: Matrix m) (B D: Matrix n), A = C -> B = D -> A ⊗ B = C ⊗ D.
Proof.
  intros. rewrite H, H0. reflexivity.
Qed.

Lemma tprod_JMeq: forall {a b c d} (A: Matrix a) (B: Matrix b) (C: Matrix c) (D: Matrix d),
  a = c -> b = d ->
  JMeq A C -> JMeq B D ->
  JMeq (A ⊗ B) (C ⊗ D).
Proof.
  intros.
  replace A with (mat_cast C (eq_sym H)).
  replace B with (mat_cast D (eq_sym H0)).
  - rewrite H. rewrite H0. reflexivity.
  - apply JMeq_eq. eapply JMeq_trans. do_JMeq.
    rewrite H2. reflexivity.
  - apply JMeq_eq. eapply JMeq_trans. do_JMeq.
    rewrite H1. reflexivity.
Qed.

Lemma tprod_add_dist_l: forall m n (A: Matrix m) (B C: Matrix n), A ⊗ (B + C) = A ⊗ B + A ⊗ C.
Proof.
  intros.
  induction A.
  - simpl.
    rewrite mat_scale_dist_l.
    reflexivity.
  - simpl.
    rewrite IHA1; rewrite IHA2; rewrite IHA3; rewrite IHA4.
    reflexivity.
Qed.

Lemma tprod_add_dist_r: forall m n (A B: Matrix m) (C: Matrix n), (A + B) ⊗ C = A ⊗ C + B ⊗ C.
Proof.
intros.
induction A.
- specialize (mat_0_inv B) as [b]; subst.
  simpl.
  rewrite mat_scale_dist_r.
  reflexivity.
- specialize (mat_S_inv B) as [B1 [B2 [B3 [B4]]]]; subst.
  simpl.
  all: try rewrite IHA1; try rewrite IHA2; try rewrite IHA3; try rewrite IHA4.
  reflexivity.
Qed.

Lemma tprod_0_r: forall m n (A: Matrix m), A ⊗ (mat_0: Matrix n) = mat_0.
Proof.
  induction A; simpl.
  - apply mat_0_scale.
  - f_equal; assumption.
Qed.

Lemma tprod_0_l: forall m n (A: Matrix n), (mat_0: Matrix m) ⊗ A = mat_0.
Proof.
  induction m; intros; simpl.
  - apply mat_scale_0.
  - f_equal; apply IHm.
Qed.

Lemma tprod_mul_0_rl: forall m n (A: Matrix m) (B C: Matrix n), (A ⊗ B) * (mat_0 ⊗ C) = mat_0.
Proof.
  intros.
  rewrite tprod_0_l.
  apply mat_mul_0_r.
Qed.

Lemma tprod_mul_eye_rr: forall m n (A C: Matrix m) (B: Matrix n), (A ⊗ B) * (C ⊗ mat_eye) = (A * C) ⊗ B.
Proof.
  induction A as [a | n'].
  - intros.
    specialize (mat_0_inv C) as [c]; subst.
    simpl.
    mat_sort.
    rewrite mat_mul_eye_r.
    f_equal.
    lca.
  - intros.
    specialize (mat_S_inv C) as [C1 [C2 [C3 [C4]]]]; subst.
    simpl.
    f_equal.
    all: try rewrite IHA1; try rewrite IHA2; try rewrite IHA3; try rewrite IHA4.
    all: rewrite tprod_add_dist_r.
    all: reflexivity.
Qed.

Lemma tprod_mul_eye_rl: forall m n (A: Matrix m) (B C: Matrix n), (A ⊗ B) * (mat_eye ⊗ C) = A ⊗ (B * C).
Proof.
  induction m as [| m'].
  - intros.
    specialize (mat_0_inv A) as [a]; subst.
    unfold mat_eye.
    simpl.
    mat_sort.
    lca.
  - intros.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4]]]]; subst.
    simpl.
    f_equal.
    all: rewrite IHm'.
    all: rewrite tprod_mul_0_rl.
    all: try apply mat_add_0_l; try apply mat_add_0_r.
  Qed.

Lemma tprod_mul: forall m n (A C: Matrix m) (B D: Matrix n), (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D).
Proof.
  intros.
  replace (C ⊗ D) with ((C ⊗ mat_eye) * (mat_eye ⊗ D)).
  rewrite mat_mul_assoc.
  rewrite tprod_mul_eye_rr.
  apply tprod_mul_eye_rl.
  rewrite tprod_mul_eye_rl.
  rewrite mat_mul_eye_l.
  reflexivity.
Qed.

Lemma tprod_conjtrans: forall m n (A: Matrix m) (B: Matrix n), (A ⊗ B)† = A† ⊗ B†.
Proof.
  induction A.
  - intros.
    simpl.
    apply mat_scale_conjtrans.
  - intros.
    simpl.
    f_equal; generalize B; assumption.
Qed.

Lemma tprod_0_l_impl: forall m n (A: Matrix m) (B: Matrix n), A = mat_0 -> A ⊗ B = mat_0.
Proof.
  intros.
  subst.
  apply tprod_0_l.
Qed.

Lemma tprod_0_r_impl: forall m n (A: Matrix m) (B: Matrix n), B = mat_0 -> A ⊗ B = mat_0.
Proof.
  intros.
  subst.
  apply tprod_0_r.
Qed.

Lemma tprod_eye_eye: forall m n, (@mat_eye m) ⊗ (@mat_eye n) = mat_eye.
Proof.
  intros.
  induction m.
  - simpl.
    apply mat_scale_1.
  - simpl.
    repeat rewrite IHm.
    repeat rewrite tprod_0_l.
    reflexivity.
Qed.

Lemma tprod_eye_eye_impl: forall m n (A: Matrix m) (B: Matrix n), A = mat_eye -> B = mat_eye -> A ⊗ B = mat_eye.
Proof.
  intros. subst. apply tprod_eye_eye.
Qed.

Lemma tprod_eye_eye_impl_l: forall m n (A: Matrix n), A = mat_eye -> (@mat_eye m) ⊗ A = mat_eye.
Proof.
  intros.
  apply tprod_eye_eye_impl; auto.
Qed.

Lemma tprod_eye_eye_impl_r: forall m n (A: Matrix m), A = mat_eye -> A ⊗ (@mat_eye n) = mat_eye.
Proof.
  intros.
  apply tprod_eye_eye_impl; auto.
Qed.

Lemma tprod_trace: forall m n (A: Matrix m) (B: Matrix n), \tr (A ⊗ B) = (\tr A * \tr B)%com.
Proof.
  intros.
  induction A.
  - simpl.
    apply mat_scale_trace.
  - simpl.
    rewrite IHA1; rewrite IHA4.
    lca.
Qed.

End PROPERTIES.

Ltac tprod_assoc := repeat (
  repeat rewrite tprod_assoc_JMeq;
  symmetry;
  repeat rewrite tprod_assoc_JMeq;
  apply tprod_JMeq; try reflexivity; try lia
).

Ltac mat_tprod := repeat (
  rewrite tprod_eye_eye ||
  rewrite tprod_0_l ||
  rewrite tprod_0_r ||
  rewrite tprod_mul ||
  auto
).

Ltac mat_conj := repeat (
  rewrite mat_add_conjtrans ||
  rewrite mat_mul_conjtrans ||
  rewrite mat_scale_conjtrans ||
  rewrite mat_conjtrans_involutive ||
  rewrite vec_dot_conj ||
  rewrite mat_vec_mul_conjtrans ||
  rewrite vec_mat_mul_conjtrans ||
  rewrite vec_conjtrans_involutive ||
  rewrite com_conj_add ||
  rewrite com_conj_mul ||
  rewrite com_conj_involutive ||
  rewrite tprod_conjtrans ||
  auto
).

Ltac mat_conj_in_all := repeat (
  rewrite mat_add_conjtrans in * ||
  rewrite mat_mul_conjtrans in * ||
  rewrite mat_scale_conjtrans in * ||
  rewrite mat_conjtrans_involutive in * ||
  rewrite vec_dot_conj in * ||
  rewrite mat_vec_mul_conjtrans in * ||
  rewrite vec_mat_mul_conjtrans in * ||
  rewrite vec_conjtrans_involutive in * ||
  rewrite com_conj_add in * ||
  rewrite com_conj_mul in * ||
  rewrite com_conj_involutive in * ||
  rewrite tprod_conjtrans in * ||
  auto
).
