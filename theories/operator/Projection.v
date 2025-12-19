Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.Single.

Open Scope Matrix_scope.

Definition mat_projection {n} (A: Matrix n) : Prop := A * A = A /\ mat_Hermitian A.

Section BASE.

Definition mat_proj0_base : Matrix 1 := rec_mat (bas_mat 1) (bas_mat 0)
                                                (bas_mat 0) (bas_mat 0).

Definition mat_proj1_base : Matrix 1 := rec_mat (bas_mat 0) (bas_mat 0)
                                                (bas_mat 0) (bas_mat 1).

(*
Maybe projection should take a size of padding before and after the base projection.
In the definition of the Qasmcore program, cnot instructions must have proofs of their validity
(target and control < size)
*)

Fixpoint mat_proj0 (n p: nat): Matrix n :=
  match n, p with
  | 0, _ => bas_mat 0  (* Actually there is no 1 * 1 projection *)
  | S _, 0 => mat_proj0_base ⊗ mat_eye
  | S n', S p' => (@mat_eye 1) ⊗ mat_proj0 n' p'
  end.

Fixpoint mat_proj1 (n p: nat): Matrix n :=
  match n, p with
  | 0, _ => bas_mat 1  (* Actually there is no 1 * 1 projection *)
  | S _, 0 => mat_proj1_base ⊗ mat_eye
  | S n', S p' => (@mat_eye 1) ⊗ mat_proj1 n' p'
  end.

Fixpoint mat_proj0_single (n p t: nat) (U: Matrix 1) : Matrix n :=
  match n, p, t with
  | 0, _, _ => mat_eye
  | S n', 0, S t' => mat_proj0_base ⊗ mat_single n' t' U
  | S n', S p', 0 => U ⊗ mat_eye
  | S n', S p', S t' => (@mat_eye 1) ⊗ mat_proj0_single n' p' t' U
  | _, _, _ => mat_eye
  end.

Fixpoint mat_proj1_single (n p t: nat) (U: Matrix 1) : Matrix n :=
  match n, p, t with
  | 0, _, _ => mat_eye
  | S n', 0, S t' => mat_proj1_base ⊗ mat_single n' t' U
  | S n', S p', 0 => U ⊗ mat_eye
  | S n', S p', S t' => (@mat_eye 1) ⊗ mat_proj1_single n' p' t' U
  | _, _, _ => mat_eye
  end.

End BASE.

Section PROPERTIES.

Lemma mat_projection_positive: forall {n} (A: Matrix n), mat_projection A -> mat_positive A.
Proof.
  intros.
  destruct H as [H0 H1].
  unfold mat_positive; intros.
  rewrite <- H0.
  replace ((v |† |* (A * A)) |*| v) with ((A *| v) |† |*| (A *| v)).
  apply vec_dot_conjtrans_ge0.
  mat_sort.
  mat_conj.
  f_equal.
  assumption.
Qed.

Lemma mat_projection_trace_ge0: forall {n} (A: Matrix n), mat_projection A -> mat_trace A >= 0.
Proof.
  intros.
  apply mat_projection_positive in H.
  apply mat_trace_positive.
  assumption.
Qed.

Lemma mat_eye_projection : forall {n}, mat_projection (@mat_eye n).
Proof.
  intros.
  unfold mat_projection.
  split.
  - apply mat_mul_eye_l.
  - apply mat_eye_Hermitian.
Qed.

Lemma tprod_projection : forall {n m} (A: Matrix n) (B: Matrix m),
  mat_projection A -> mat_projection B -> mat_projection (A ⊗ B).
Proof.
  intros.
  destruct H as [HA0 HA1], H0 as [HB0 HB1].
  split.
  - rewrite tprod_mul.
    rewrite HA0, HB0.
    reflexivity.
  - apply tprod_Hermitian.
    all: assumption.
Qed.

Lemma mat_single_projection : forall n t (U : Matrix 1), mat_projection U -> mat_projection (mat_single n t U).
Proof.
  intros.
  revert t.
  induction n.
  - intros.
    split.
    + simpl; f_equal; lca.
    + unfold mat_Hermitian; simpl; f_equal; lca.
  - intros.
    destruct t.
    + simpl.
      apply (@tprod_projection 1 n).
      assumption.
      apply mat_eye_projection.
    + simpl.
      mat_simpl.
      destruct (IHn t) as [IH0 IH1].
      split.
      all: simpl; mat_simpl.
      * f_equal; auto.
      * unfold mat_Hermitian.
        simpl; f_equal.
        all: auto.
        all: apply mat_0_Hermitian.
Qed.

Lemma mat_proj_base_sum : mat_proj0_base + mat_proj1_base = mat_eye.
Proof.
  unfold mat_proj0_base, mat_proj1_base.
  com_simpl.
Qed.

Lemma mat_proj0_base_mul : mat_proj0_base * mat_proj0_base = mat_proj0_base.
Proof.
  unfold mat_proj0_base; com_simpl.
Qed.

Lemma mat_proj1_base_mul : mat_proj1_base * mat_proj1_base = mat_proj1_base.
Proof.
  unfold mat_proj1_base; com_simpl.
Qed.

Lemma mat_proj0_base_Hermitian : mat_Hermitian mat_proj0_base.
Proof.
  unfold mat_proj0_base, mat_Hermitian.
  com_simpl.
Qed.

Lemma mat_proj1_base_Hermitian : mat_Hermitian mat_proj1_base.
Proof.
  unfold mat_proj1_base, mat_Hermitian; com_simpl.
Qed.

Lemma mat_proj0_base_positive : mat_positive mat_proj0_base.
Proof.
  apply mat_pure_positive_impl.
  exists (rec_vec (bas_vec 1) (bas_vec 0)).
  com_simpl.
Qed.

Lemma mat_proj1_base_positive : mat_positive mat_proj1_base.
Proof.
  apply mat_pure_positive_impl.
  exists (rec_vec (bas_vec 0) (bas_vec 1)).
  com_simpl.
Qed.

Lemma mat_proj0_base_trace : mat_trace mat_proj0_base >= 0.
Proof.
  unfold mat_proj0_base; com_simpl.
  split; simpl.
  all: lra.
Qed.

Lemma mat_proj1_base_trace : mat_trace mat_proj1_base >= 0.
Proof.
  unfold mat_proj1_base; com_simpl.
  split; simpl.
  all: lra.
Qed.

Lemma mat_proj0_base_projection : mat_projection mat_proj0_base.
Proof.
  split.
  - apply mat_proj0_base_mul.
  - apply mat_proj0_base_Hermitian.
Qed.

Lemma mat_proj1_base_projection : mat_projection mat_proj1_base.
Proof.
  split.
  - apply mat_proj1_base_mul.
  - apply mat_proj1_base_Hermitian.
Qed.

Lemma mat_proj_base_01_perp : mat_proj0_base * mat_proj1_base = mat_0.
Proof.
  com_simpl.
Qed.

Lemma mat_proj_base_10_perp : mat_proj1_base * mat_proj0_base = mat_0.
Proof.
  com_simpl.
Qed.

Lemma mat_proj_01_perp : forall n p, mat_proj0 n p * mat_proj1 n p = mat_0.
Proof.
  induction n.
  - intros; mat_simpl.
  - intros; destruct p.
    + mat_simpl.
    + mat_simpl.
      rewrite IHn.
      reflexivity.
Qed.

Lemma mat_proj_10_perp : forall n p, mat_proj1 n p * mat_proj0 n p = mat_0.
Proof.
  induction n.
  - intros; mat_simpl.
  - intros; destruct p.
    + mat_simpl.
    + mat_simpl.
      rewrite IHn.
      reflexivity.
Qed.

Lemma mat_proj0_projection: forall n p, mat_projection (mat_proj0 n p).
Proof.
  intros.
  revert p.
  induction n.
  - intros; split; [simpl|simpl].
    + f_equal; lca.
    + unfold mat_Hermitian; simpl; f_equal; lca.
  - intros; destruct p.
    + split.
      all: mat_simpl.
      unfold mat_Hermitian; simpl.
      f_equal.
      apply mat_eye_Hermitian.
      all: apply mat_0_Hermitian.
    + destruct (IHn p) as [IH0 IH1].
      split.
      all: mat_simpl.
      * f_equal.
        all: auto.
      * unfold mat_Hermitian; simpl.
        f_equal.
        all: try apply mat_0_Hermitian.
        all: auto.
Qed.

Lemma mat_proj1_projection: forall n p, mat_projection (mat_proj1 n p).
Proof.
  intros.
  revert p.
  induction n.
  - intros; split; [simpl|simpl].
    + f_equal; lca.
    + unfold mat_Hermitian; simpl; f_equal; lca.
  - intros; destruct p.
    + split.
      all: mat_simpl.
      unfold mat_Hermitian; simpl.
      f_equal.
      all: try apply mat_0_Hermitian.
      apply mat_eye_Hermitian.
    + destruct (IHn p) as [IH0 IH1].
      split.
      all: mat_simpl.
      * f_equal.
        all: auto.
      * unfold mat_Hermitian; simpl.
        f_equal.
        all: try apply mat_0_Hermitian.
        all: auto.
Qed.

Lemma mat_proj_sum : forall n p, mat_proj0 n p + mat_proj1 n p = mat_eye.
Proof.
  induction n.
  - intros.
    simpl.
    f_equal; lca.
  - intros; destruct p.
    + mat_simpl.
    + mat_simpl.
      f_equal.
      all: auto.
Qed.

End PROPERTIES.

