Require Import QASMInfer.matrix.All.

Open Scope Matrix_scope.

Definition mat_positive {n} (A : Matrix n) : Prop := forall (v : Vector n), (v|† |* A |*| v) >= 0.

Section PROPERTIES.

Lemma mat_pure_positive : forall {n} (v : Vector n), mat_positive (v |✕| v|†).
Proof.
  unfold mat_positive.
  intros n v w.
  rewrite vec_vec_vec_mul_assoc.
  rewrite vec_vec_scale_dot_assoc.
  replace (v |† |*| w) with ((w|† |*| v)^*).
  apply com_conj_mul_ge0_r.
  mat_conj.
Qed.

Lemma mat_pure_positive_impl : forall {n} (A: Matrix n), (exists v, v |✕| v|† = A) -> mat_positive A.
Proof.
  intros.
  destruct H as [v H].
  subst.
  apply mat_pure_positive.
Qed.

Lemma mat_add_positive : forall {n} (A B : Matrix n), mat_positive A -> mat_positive B -> mat_positive (A + B).
Proof.
  unfold mat_positive.
  intros.
  mat_expand.
  apply com_ge0_add; auto.
Qed.

Lemma mat_mul_positive : forall {n} (A B : Matrix n), mat_positive A -> mat_positive (B * A * B†).
Proof.
  unfold mat_positive.
  intros.
  replace ((v |† |* (B * A * B †)) |*| v) with (((B† *| v) |† |* A |*| (B† *| v))); auto.
  rewrite <- vec_mat_vec_mul_assoc.
  mat_sort.
  mat_conj.
Qed.

Property mat_rec_positive_fst : forall {n} (A B C D : Matrix n), mat_positive (rec_mat A B C D) -> mat_positive A.
Proof.
  unfold mat_positive in *.
  intros.
  specialize (H (rec_vec v vec_zero)).
  simpl in H.
  mat_simpl_in_all.
Qed.

Property mat_rec_positive_snd : forall {n} (A B C D : Matrix n), mat_positive (rec_mat A B C D) -> mat_positive D.
Proof.
  unfold mat_positive in *.
  intros.
  specialize (H (rec_vec vec_zero v)).
  simpl in H.
  mat_simpl_in_all.
Qed.

Lemma mat_trace_positive : forall {n} (A : Matrix n), mat_positive A -> mat_trace A >= 0.
Proof.
  intros.
  induction A.
  - specialize (H (bas_vec 1)).
    simpl in *.
    replace c with (1 ^* * c * 1)%com; auto; lca.
  - simpl in *.
    apply mat_rec_positive_fst in H as H1.
    apply mat_rec_positive_snd in H as H2.
    apply com_ge0_add; auto.
Qed.

Lemma mat_scale_positive : forall {n} (A : Matrix n) (c : Complex), mat_positive A -> c >= 0 -> mat_positive (c .* A).
Proof.
  unfold mat_positive.
  intros.
  mat_sort.
  apply com_ge0_mul; auto.
Qed.

End PROPERTIES.


Section BASECASES.

Lemma mat_0_positive : forall {n}, mat_positive (@mat_0 n).
Proof.
  unfold mat_positive.
  intros.
  mat_simpl.
  split.
  all: simpl; lra.
Qed.

Lemma mat_eye_positive : forall {n}, mat_positive (@mat_eye n).
Proof.
  unfold mat_positive.
  intros.
  mat_simpl.
  apply vec_dot_conjtrans_ge0.
Qed.

End BASECASES.
