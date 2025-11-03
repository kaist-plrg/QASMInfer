Require Export Projection.
From Stdlib Require Import Logic.Eqdep_dec.

Open Scope Matrix_scope.

Definition den_normlized {n: nat} (A: Matrix n) : Prop := mat_trace A = 1.

Lemma tprod_normalized: forall {n m} (A: Matrix n) (B: Matrix m), den_normlized A -> den_normlized B -> den_normlized (A ⊗ B).
Proof.
  intros.
  unfold den_normlized in *.
  induction n.
  - specialize (mat_0_inv A) as [a HA].
    subst A.
    simpl in *.
    subst a.
    mat_simpl.
  - specialize (mat_S_inv A) as [A0 [A1 [A2 [A3 HA]]]].
    subst A.
    simpl in *.
    rewrite <- mat_add_trace in H.
    rewrite <- mat_add_trace.
    rewrite <- tprod_add_dist_r.
    apply IHn.
    assumption.
Qed.

Section INIT.

Definition den_init (n: nat): Matrix n.
Proof.
  induction n.
  - exact mat_eye.
  - exact (rec_mat IHn mat_0 mat_0 mat_0).
Defined.

Lemma den_init_Hermitian : forall n, mat_Hermitian (den_init n).
  induction n.
  - apply mat_eye_Hermitian.
  - unfold mat_Hermitian; simpl.
    mat_conj.
    rewrite mat_0_Hermitian.
    f_equal.
    assumption.
Qed.

Lemma den_init_positive : forall n, mat_positive (den_init n).
  induction n.
  - apply mat_eye_positive.
  - unfold mat_positive; simpl.
    intros.
    specialize (vec_S_inv v) as [v0 [v1 Hv]].
    subst v; simpl.
    mat_simpl.
Qed.

Lemma den_init_normalized : forall n, den_normlized (den_init n).
  induction n.
  - reflexivity.
  - unfold den_normlized; simpl.
    rewrite mat_trace_0.
    rewrite IHn.
    lca.
Qed.

End INIT.

Section UOP.

Definition den_uop {n: nat} (uop den: Matrix n) : Matrix n := uop * den * uop†.

Lemma den_uop_conj : forall {n: nat} (uop den: Matrix n), (den_uop uop den)† = den_uop uop (den†).
Proof.
  intros.
  unfold den_uop.
  mat_conj.
  mat_sort.
Qed.

Lemma den_uop_Hermitian : forall {n: nat} (uop den: Matrix n), mat_Hermitian den -> mat_Hermitian (den_uop uop den).
Proof.
  intros; unfold mat_Hermitian.
  rewrite den_uop_conj.
  rewrite H.
  reflexivity.
Qed.

Lemma den_uop_positive : forall {n: nat} (uop den: Matrix n), mat_positive den -> mat_positive (den_uop uop den).
Proof.
  intros; unfold den_uop.
  apply mat_mul_positive.
  assumption.
Qed.

Lemma den_uop_trace : forall {n: nat} (uop den: Matrix n), mat_unitary uop -> \tr (den_uop uop den) = \tr den.
Proof.
  intros; unfold den_uop.
  rewrite mat_mul_trace_comm.
  mat_sort.
  destruct H as [H _].
  rewrite H.
  mat_simpl.
Qed.

Lemma den_uop_normalized : forall {n: nat} (uop den: Matrix n),
  mat_unitary uop -> den_normlized den -> den_normlized (den_uop uop den).
Proof.
  intros; unfold den_normlized in *.
  rewrite den_uop_trace.
  all: assumption.
Qed.

End UOP.

Section MEASURE.

Definition den_prob {n: nat} (proj den: Matrix n) : Complex := \tr (den * proj).

Definition den_prob_0 {n: nat} (t: nat) (den: Matrix n) : Complex := den_prob (mat_proj0 n t) den.

Definition den_prob_1 {n: nat} (t: nat) (den: Matrix n) : Complex := den_prob (mat_proj1 n t) den.

Definition den_measure {n: nat} (proj den: Matrix n) : Matrix n := (/ den_prob proj den) .* (proj * den * proj).

Definition den_measure_0 {n: nat} (t: nat) (den: Matrix n) : Matrix n := den_measure (mat_proj0 n t) den.

Definition den_measure_1 {n: nat} (t: nat) (den: Matrix n) : Matrix n := den_measure (mat_proj1 n t) den.

Lemma den_measure_Hermitian : forall {n: nat} (proj den: Matrix n),
  mat_projection proj ->
  mat_Hermitian den ->
  mat_Hermitian (den_measure proj den).
Proof.
  intros n proj den [_ Hp] Hd.
  unfold den_measure, mat_Hermitian.
  assert (com_imag (den_prob proj den) = R0) as Hc.
  { unfold den_prob.
    apply com_conj_real_r.
    rewrite <- mat_trace_conjtrans.
    mat_conj.
    rewrite mat_mul_trace_comm.
    f_equal.
    rewrite Hp, Hd.
    reflexivity.
  }
  mat_conj.
  apply com_imag_0_inv in Hc.
  apply com_conj_real in Hc.
  rewrite Hc.
  f_equal.
  rewrite Hd, Hp.
  mat_sort.
Qed.

Lemma den_measure_positive : forall {n: nat} (proj den: Matrix n),
  mat_projection proj ->
  mat_positive den ->
  mat_positive (den_measure proj den).
Proof.
  intros n proj den [Hp Hph] Hd.
  unfold den_measure.
  assert (den_prob proj den >= 0) as Hc.
  { unfold den_prob.
    rewrite <- Hp; mat_sort.
    rewrite mat_mul_trace_comm; mat_sort.
    specialize (mat_mul_positive den proj) as H.
    apply H in Hd.
    rewrite Hph in Hd.
    apply mat_trace_positive.
    assumption.
  }
  apply mat_scale_positive.
  - replace (proj * den * proj) with (proj * den * proj †).
    apply mat_mul_positive.
    assumption.
    f_equal; assumption.
  - apply com_ge0_inv.
    assumption.
Qed.

Lemma den_measure_normalized : forall {n: nat} (proj den: Matrix n),
  mat_projection proj ->
  den_normlized den ->
  den_prob proj den <> 0 ->
  den_normlized (den_measure proj den).
Proof.
  intros n proj den [Hp _] Hd Hz.
  unfold den_measure, den_normlized in *.
  rewrite mat_scale_trace.
  rewrite mat_mul_trace_comm.
  rewrite mat_mul_assoc.
  rewrite Hp.
  unfold den_prob in *.
  rewrite mat_mul_trace_comm.
  apply com_inv_mult.
  rewrite mat_mul_trace_comm.
  assumption.
Qed.

End MEASURE.

Section RESET.

Definition den_reset {n: nat} (t: nat) (den: Matrix n) : Matrix n :=
  (mat_proj0 n t * den * mat_proj0 n t) + (
    den_uop (mat_single n t (mat_rot PI 0 PI)) (mat_proj1 n t * den * mat_proj1 n t)
  ).

Lemma den_reset_conj : forall {n: nat} (t: nat) (den: Matrix n), (den_reset t den)† = den_reset t (den†).
Proof.
  intros; unfold den_reset.
  mat_conj; mat_sort.
  1-2: apply mat_proj0_projection.
  rewrite den_uop_conj.
  f_equal.
  mat_conj; mat_sort.
  all: apply mat_proj1_projection.
Qed.

Lemma den_reset_Hermitian : forall {n: nat} (t: nat) (den: Matrix n), mat_Hermitian den -> mat_Hermitian (den_reset t den).
Proof.
  intros; unfold mat_Hermitian.
  rewrite den_reset_conj.
  rewrite H.
  reflexivity.
Qed.

Lemma den_reset_positive : forall {n: nat} (t: nat) (den: Matrix n), mat_positive den -> mat_positive (den_reset t den).
Proof.
  intros; unfold den_reset.
  apply mat_add_positive.
  - specialize (mat_proj0_projection n t) as [_ HP0].
    replace (mat_proj0 n t * den * mat_proj0 n t) with (mat_proj0 n t * den * mat_proj0 n t †).
    apply mat_mul_positive.
    assumption.
    rewrite HP0.
    mat_conj.
  - apply den_uop_positive.
    specialize (mat_proj1_projection n t) as [_ HP1].
    replace (mat_proj1 n t * den * mat_proj1 n t) with (mat_proj1 n t * den * mat_proj1 n t †).
    apply mat_mul_positive.
    assumption.
    rewrite HP1.
    mat_conj.
Qed.

Lemma den_reset_trace : forall {n: nat} (t: nat) (den: Matrix n), \tr (den_reset t den) = \tr den.
Proof.
  intros; unfold den_reset, den_uop; mat_simpl.
  rewrite mat_add_trace.
  rewrite mat_mul_trace_comm with (B := (mat_single n t (mat_rot PI 0 PI) †)).
  mat_sort.
  specialize (mat_single_unitary n t (mat_rot PI 0 PI)) as HU.
  specialize (mat_rot_unitary PI 0 PI) as HR.
  apply HU in HR.
  destruct HR as [HR _].
  rewrite HR.
  mat_simpl.
  rewrite mat_mul_trace_comm.
  rewrite mat_mul_trace_comm with (B := mat_proj1 n t).
  mat_sort.
  specialize (mat_proj0_projection n t) as [H0 _].
  specialize (mat_proj1_projection n t) as [H1 _].
  rewrite H0, H1.
  rewrite <- mat_add_trace.
  rewrite <- mat_mul_dist_r.
  rewrite mat_proj_sum.
  mat_simpl.
Qed.

Lemma den_reset_normalized : forall {n: nat} (t: nat) (den: Matrix n), den_normlized den -> den_normlized (den_reset t den).
Proof.
  intros; unfold den_normlized in *.
  rewrite den_reset_trace.
  assumption.
Qed.

End RESET.

Section Mix.

Definition den_mix {n: nat} (p0 p1: R) (den0 den1: Matrix n) : Matrix n := (p0 / (p0 + p1))%com .* den0 + (p1 / (p0 + p1))%com .* den1.

Lemma den_mix_Hermitian : forall {n: nat} (p0 p1: R) (den0 den1: Matrix n),
  mat_Hermitian den0 -> mat_Hermitian den1 -> mat_Hermitian (den_mix p0 p1 den0 den1).
Proof.
  intros; unfold mat_Hermitian, den_mix.
  mat_conj.
  repeat rewrite com_conj_real_l.
  rewrite H, H0.
  reflexivity.
  all: simpl; lra.
Qed.

Lemma den_mix_positive : forall {n: nat} (p0 p1: R) (den0 den1: Matrix n),
  mat_positive den0 -> mat_positive den1 -> (p0 > 0)%R -> (p1 > 0)%R -> mat_positive (den_mix p0 p1 den0 den1).
Proof.
  intros; unfold den_mix.
  apply mat_add_positive.
  all: apply mat_scale_positive; auto.
  all: apply com_ge0_mul.
  2,4: apply com_ge0_inv; apply com_ge0_add.
  all: apply com_real_ge0.
  all: lra.
Qed.

Lemma den_mix_normalized : forall {n: nat} (p0 p1: R) (den0 den1: Matrix n),
  den_normlized den0 -> den_normlized den1 -> (p0 > 0)%R -> (p1 > 0)%R -> den_normlized (den_mix p0 p1 den0 den1).
Proof.
  intros; unfold den_normlized, den_mix in *.
  rewrite mat_add_trace.
  repeat rewrite mat_scale_trace.
  rewrite H, H0.
  repeat rewrite com_mul_1_r.
  unfold com_div.
  rewrite <- com_mul_plus_distr_l.
  rewrite com_mul_comm.
  apply com_inv_mult.
  unfold RTC, com_add.
  simpl; injection; lra.
Qed.

End Mix.

Section VALID.

Inductive den_valid {n: nat} : Matrix n -> Prop :=
  | den_valid_init : den_valid (den_init n)

  | den_valid_uop : forall (uop den: Matrix n),
                    mat_unitary uop ->
                    den_valid den ->
                    den_valid (den_uop uop den)

  | den_valid_measure : forall (proj den: Matrix n),
                        mat_projection proj ->
                        den_valid den ->
                        den_prob proj den <> 0 ->
                        den_valid (den_measure proj den)

  | den_valid_reset : forall (t: nat) (den: Matrix n),
                      den_valid den ->
                      den_valid (den_reset t den)

  | den_valid_mix : forall (p0 p1: R) (den0 den1: Matrix n),
                    (p0 > 0)%R ->
                    (p1 > 0)%R ->
                    den_valid den0 ->
                    den_valid den1 ->
                    den_valid (den_mix p0 p1 den0 den1).


Theorem den_valid_Hermitian : forall {n: nat} (den: Matrix n), den_valid den -> mat_Hermitian den.
Proof.
  intros n den H.
  induction H.
  - apply den_init_Hermitian.
  - apply den_uop_Hermitian; assumption.
  - apply den_measure_Hermitian; assumption.
  - apply den_reset_Hermitian; assumption.
  - apply den_mix_Hermitian; assumption.
Qed.

Theorem den_valid_positive : forall {n: nat} (den: Matrix n), den_valid den -> mat_positive den.
Proof.
  intros n den H.
  induction H.
  - apply den_init_positive.
  - apply den_uop_positive; assumption.
  - apply den_measure_positive; assumption.
  - apply den_reset_positive; assumption.
  - apply den_mix_positive; assumption.
Qed.

Theorem den_valid_normalized : forall {n: nat} (den: Matrix n), den_valid den -> den_normlized den.
Proof.
  intros n den H.
  induction H.
  - apply den_init_normalized.
  - apply den_uop_normalized; assumption.
  - apply den_measure_normalized; assumption.
  - apply den_reset_normalized; assumption.
  - apply den_mix_normalized; assumption.
Qed.

End VALID.
