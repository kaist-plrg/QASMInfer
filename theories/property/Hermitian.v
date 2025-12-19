Require Import QASMInfer.matrix.All.
From Stdlib Require Import Logic.Eqdep_dec.

Open Scope Matrix_scope.

Definition mat_Hermitian {n} (A : Matrix n) : Prop := A† = A.

Section PROPERTIES.

Lemma mat_add_Hermitian: forall {n} (A B : Matrix n), mat_Hermitian A -> mat_Hermitian B -> mat_Hermitian (A + B).
Proof.
  intros.
  unfold mat_Hermitian in *.
  mat_conj.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma mat_scale_Hermitian: forall {n} (c : Complex) (A : Matrix n), mat_Hermitian A -> com_imag c = R0 -> mat_Hermitian (c .* A).
Proof.
  intros.
  unfold mat_Hermitian in *.
  mat_conj.
  f_equal; try assumption.
  apply com_conj_real.
  assumption.
Qed.

Lemma tprod_Hermitian: forall {m n} (A: Matrix m) (B: Matrix n), mat_Hermitian A -> mat_Hermitian B -> mat_Hermitian (A ⊗ B).
Proof.
  intros.
  unfold mat_Hermitian in *.
  rewrite tprod_conjtrans.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma mat_mul_conj_Hermitian: forall {n} (A B: Matrix n), mat_Hermitian A -> mat_Hermitian (B * A * B †).
Proof.
  intros.
  unfold mat_Hermitian in *.
  mat_conj. mat_sort.
Qed.

End PROPERTIES.


Section BASECASES.

Lemma mat_0_Hermitian: forall {n}, mat_Hermitian (@mat_0 n).
Proof.
  intros.
  unfold mat_Hermitian.
  induction n.
  - simpl; f_equal; lca.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma mat_eye_Hermitian: forall {n}, mat_Hermitian (@mat_eye n).
Proof.
  intros.
  unfold mat_Hermitian.
  induction n.
  - simpl; f_equal; lca.
  - simpl.
    rewrite IHn.
    rewrite mat_0_Hermitian.
    reflexivity.
Qed.

End BASECASES.

