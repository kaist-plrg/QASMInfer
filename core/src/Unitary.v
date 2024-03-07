Require Export Hermitian.
Require Import Coq.Logic.Eqdep_dec.

Open Scope Matrix_scope.

Definition mat_unitary {n} (A : Matrix n) : Prop := A† * A = mat_eye /\ A * A† = mat_eye.

Section PROPERTIES.

Lemma mat_conjtrans_unitary: forall {n} (A : Matrix n), mat_unitary A -> mat_unitary (A†).
Proof.
  unfold mat_unitary.
  intros.
  destruct H.
  mat_conj.
Qed.

Lemma mat_mul_unitary: forall {n} (A B : Matrix n), mat_unitary A -> mat_unitary B -> mat_unitary (A * B).
Proof.
  unfold mat_unitary.
  intros.
  destruct H, H0.
  mat_conj.
  replace (B † * A † * (A * B)) with (B † * (A † * A) * B) by (mat_sort; reflexivity).
  replace (A * B * (B † * A †)) with (A * (B * B †) * A †) by (mat_sort; reflexivity).
  rewrite H; rewrite H2.
  mat_simpl.
Qed.

Lemma tprod_unitary: forall {m n} (A: Matrix m) (B: Matrix n),
  mat_unitary A -> mat_unitary B -> mat_unitary (A ⊗ B).
Proof.
  intros.
  unfold mat_unitary in *.
  destruct H as [HA1 HA2], H0 as [HB1 HB2].
  mat_conj.
  repeat rewrite tprod_mul.
  split; apply tprod_eye_eye_impl; assumption.
Qed.

Lemma unitary_inv_l: forall {n} (A B C: Matrix n),
  mat_unitary C -> C * A = B -> A = (C †) * B.
Proof.
  intros.
  apply (mat_eq_imp_mul_l (C †)) in H0.
  mat_sort_in_all.
  destruct H.
  rewrite H in H0.
  mat_simpl_in_all.
Qed.

Lemma unitary_inv_r: forall {n} (A B C: Matrix n),
  mat_unitary C -> A * C = B -> A = B * (C †).
Proof.
  intros.
  apply (mat_eq_imp_mul_r (C †)) in H0.
  mat_sort_rev_in_all.
  destruct H.
  rewrite H1 in H0.
  mat_simpl_in_all.
Qed.

Lemma unitary_cancelable_l: forall {n} (A B C: Matrix n),
  mat_unitary C -> C * A = C * B -> A = B.
Proof.
  intros.
  apply unitary_inv_l in H0.
  mat_sort_in_all.
  destruct H. rewrite H in H0.
  mat_simpl_in_all.
  exact H.
Qed.

Lemma unitary_cancelable_r: forall {n} (A B C: Matrix n),
  mat_unitary C -> A * C = B * C -> A = B.
Proof.
  intros.
  apply unitary_inv_r in H0.
  mat_sort_rev_in_all.
  destruct H. rewrite H1 in H0.
  mat_simpl_in_all.
  exact H.
Qed.

Lemma unitary_diagonal: forall {n} (U V: Matrix n),
  mat_unitary U -> mat_unitary V -> mat_unitary (rec_mat U mat_0 mat_0 V).
Proof.
  intros n U V [HU1 HU2] [HV1 HV2].
  split.
  all: mat_simpl.
  all: f_equal.
  all: try assumption.
  all: rewrite mat_0_Hermitian.
  all: mat_simpl.
Qed.

End PROPERTIES.


Section BASECASES.

Lemma mat_eye_unitary: forall {n}, mat_unitary (@mat_eye n).
Proof.
  unfold mat_unitary.
  intros.
  split.
  all: rewrite mat_eye_Hermitian; mat_simpl.
Qed.

End BASECASES.
