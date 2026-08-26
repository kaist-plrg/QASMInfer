Require Import QASMInfer.matrix.All.
Require Import QASMInfer.program.All.

From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

Import ListNotations.

Open Scope R_scope.
Open Scope Complex_scope.

Section DOMEGA_ARITHMETIC.

Record DOmega : Type := {
  domega_d0 : Z;
  domega_d1 : Z;
  domega_d2 : Z;
  domega_d3 : Z;
  domega_k : nat
}.

Definition domega_make (d0 d1 d2 d3 : Z) (k : nat) : DOmega :=
  {| domega_d0 := d0;
     domega_d1 := d1;
     domega_d2 := d2;
     domega_d3 := d3;
     domega_k := k |}.

Fixpoint pow2 (k : nat) : Z :=
  match k with
  | O => 1%Z
  | S k' => (2 * pow2 k')%Z
  end.

Definition rpow2 (k : nat) : R :=
  IZR (pow2 k).

Definition domega_coeff (d : Z) (k : nat) : R :=
  (IZR d / rpow2 k)%R.

Definition domega_zero : DOmega := domega_make 0%Z 0%Z 0%Z 0%Z 0.
Definition domega_one : DOmega := domega_make 1%Z 0%Z 0%Z 0%Z 0.
Definition domega_w : DOmega := domega_make 0%Z 1%Z 0%Z 0%Z 0.
Definition domega_w2 : DOmega := domega_make 0%Z 0%Z 1%Z 0%Z 0.
Definition domega_w3 : DOmega := domega_make 0%Z 0%Z 0%Z 1%Z 0.

Definition domega_neg (x : DOmega) : DOmega :=
  domega_make
    (- domega_d0 x)%Z
    (- domega_d1 x)%Z
    (- domega_d2 x)%Z
    (- domega_d3 x)%Z
    (domega_k x).

Definition domega_minus_one : DOmega :=
  domega_neg domega_one.

Definition domega_minus_i : DOmega :=
  domega_neg domega_w2.

Definition domega_h_scalar : DOmega :=
  domega_make 0%Z 1%Z 0%Z (-1)%Z 1.

Definition domega_half_one_plus_i : DOmega :=
  domega_make 1%Z 0%Z 1%Z 0%Z 1.

Definition domega_half_one_minus_i : DOmega :=
  domega_make 1%Z 0%Z (-1)%Z 0%Z 1.

Definition domega_common_k (x y : DOmega) : nat :=
  Nat.max (domega_k x) (domega_k y).

Definition domega_align (target_k : nat) (x : DOmega) (d : Z) : Z :=
  (d * pow2 (target_k - domega_k x))%Z.

Definition domega_add (x y : DOmega) : DOmega :=
  let k := domega_common_k x y in
  domega_make
    (domega_align k x (domega_d0 x) + domega_align k y (domega_d0 y))%Z
    (domega_align k x (domega_d1 x) + domega_align k y (domega_d1 y))%Z
    (domega_align k x (domega_d2 x) + domega_align k y (domega_d2 y))%Z
    (domega_align k x (domega_d3 x) + domega_align k y (domega_d3 y))%Z
    k.

Definition domega_sub (x y : DOmega) : DOmega :=
  domega_add x (domega_neg y).

Definition domega_div2 (x : DOmega) : DOmega :=
  domega_make
    (domega_d0 x)
    (domega_d1 x)
    (domega_d2 x)
    (domega_d3 x)
    (S (domega_k x)).

Definition domega_mul (x y : DOmega) : DOmega :=
  let a0 := domega_d0 x in
  let a1 := domega_d1 x in
  let a2 := domega_d2 x in
  let a3 := domega_d3 x in
  let b0 := domega_d0 y in
  let b1 := domega_d1 y in
  let b2 := domega_d2 y in
  let b3 := domega_d3 y in
  let p0 := (a0 * b0)%Z in
  let p1 := (a0 * b1 + a1 * b0)%Z in
  let p2 := (a0 * b2 + a1 * b1 + a2 * b0)%Z in
  let p3 := (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)%Z in
  let p4 := (a1 * b3 + a2 * b2 + a3 * b1)%Z in
  let p5 := (a2 * b3 + a3 * b2)%Z in
  let p6 := (a3 * b3)%Z in
  domega_make
    (p0 - p4)%Z
    (p1 - p5)%Z
    (p2 - p6)%Z
    p3
    (domega_k x + domega_k y).

Definition domega_eqb (x y : DOmega) : bool :=
  let k := domega_common_k x y in
  Z.eqb (domega_align k x (domega_d0 x)) (domega_align k y (domega_d0 y))
  && Z.eqb (domega_align k x (domega_d1 x)) (domega_align k y (domega_d1 y))
  && Z.eqb (domega_align k x (domega_d2 x)) (domega_align k y (domega_d2 y))
  && Z.eqb (domega_align k x (domega_d3 x)) (domega_align k y (domega_d3 y)).

Definition omega : Complex :=
  com_iexp (PI / 4)%R.

Definition complex_of_domega (x : DOmega) : Complex :=
  (RTC (domega_coeff (domega_d0 x) (domega_k x))
   + RTC (domega_coeff (domega_d1 x) (domega_k x)) * omega
   + RTC (domega_coeff (domega_d2 x) (domega_k x)) * (omega * omega)
   + RTC (domega_coeff (domega_d3 x) (domega_k x))
     * (omega * omega * omega))%com.

Definition domega_equiv (x y : DOmega) : Prop :=
  complex_of_domega x = complex_of_domega y.

Lemma pow2_pos :
  forall k, (0 < pow2 k)%Z.
Proof.
  induction k as [| k IH].
  - simpl. lia.
  - simpl. change (0 < 2 * pow2 k)%Z.
    apply Z.mul_pos_pos; lia.
Qed.

Lemma pow2_nonzero :
  forall k, pow2 k <> 0%Z.
Proof.
  intros k H.
  pose proof (pow2_pos k).
  lia.
Qed.

Lemma rpow2_nonzero :
  forall k, rpow2 k <> 0%R.
Proof.
  intros k H.
  unfold rpow2 in H.
  apply eq_IZR in H.
  apply (pow2_nonzero k).
  assumption.
Qed.

Lemma pow2_add :
  forall k1 k2, pow2 (k1 + k2) = (pow2 k1 * pow2 k2)%Z.
Proof.
  induction k1 as [| k1 IH]; intros k2.
  - simpl.
    destruct (pow2 k2); reflexivity.
  - replace (S k1 + k2)%nat with (S (k1 + k2)) by lia.
    cbn [pow2].
    rewrite IH.
    lia.
Qed.

Lemma rpow2_add :
  forall k1 k2, rpow2 (k1 + k2) = (rpow2 k1 * rpow2 k2)%R.
Proof.
  intros k1 k2.
  unfold rpow2.
  rewrite pow2_add.
  rewrite mult_IZR.
  reflexivity.
Qed.

Lemma domega_common_k_le :
  forall x y,
  (domega_k x <= domega_common_k x y /\ domega_k y <= domega_common_k x y)%nat.
Proof.
  intros.
  split.
  - apply Nat.le_max_l.
  - apply Nat.le_max_r.
Qed.

Lemma domega_coeff_align :
  forall d k target_k,
    (k <= target_k)%nat ->
    domega_coeff (d * pow2 (target_k - k)) target_k =
    domega_coeff d k.
Proof.
  intros.
  unfold domega_coeff.
  rewrite mult_IZR.
  repeat rewrite Rdiv_def.
  rewrite Rmult_assoc.
  f_equal.
  replace (target_k)%nat with (target_k - k + k)%nat at 2 by lia.
  rewrite (rpow2_add (target_k - k) k).
  rewrite Rinv_mult, <- Rmult_assoc.
  rewrite Rmult_inv_r.
  - lra.
  - apply rpow2_nonzero.
Qed.

Lemma domega_coeff_align_eq :
  forall x y dx dy,
    domega_align (domega_common_k x y) x dx =
    domega_align (domega_common_k x y) y dy ->
    domega_coeff dx (domega_k x) =
    domega_coeff dy (domega_k y).
Proof.
  intros x y dx dy H.
  unfold domega_align in H.
  set (k := domega_common_k x y).
  destruct (domega_common_k_le x y) as [Hx Hy].
  rewrite <-
    (domega_coeff_align dx (domega_k x) k Hx).
  rewrite <-
    (domega_coeff_align dy (domega_k y) k Hy).
  fold k in H.
  unfold domega_align in H.
  rewrite H.
  reflexivity.
Qed.

Lemma domega_eqb_sound :
  forall x y,
    domega_eqb x y = true ->
    domega_equiv x y.
Proof.
  intros x y Heq.
  set (k := domega_common_k x y).
  destruct (domega_common_k_le x y) as [Hx Hy].
  unfold domega_eqb in Heq.
  fold k in Heq.
  repeat rewrite Bool.andb_true_iff in Heq.
  destruct Heq as [[[H0 H1] H2] H3].
  apply Z.eqb_eq in H0, H1, H2, H3.
  apply domega_coeff_align_eq in H0, H1, H2, H3.
  unfold domega_equiv, complex_of_domega.
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma deomga_equiv_eq :
  forall x y,
    domega_d0 x = domega_d0 y ->
    domega_d1 x = domega_d1 y ->
    domega_d2 x = domega_d2 y ->
    domega_d3 x = domega_d3 y ->
    domega_k x = domega_k y ->
    domega_equiv x y.
Proof.
  intros x y H0 H1 H2 H3 Hk.
  unfold domega_equiv, complex_of_domega.
  rewrite H0, H1, H2, H3, Hk.
  reflexivity.
Qed.

Lemma omega_pow2 :
  (omega * omega)%com = Ione.
Proof.
  unfold omega.
  rewrite <- com_iexp_mul.
  replace (PI / 4 + PI / 4)%R with (PI / 2)%R by field.
  apply com_iexp_PI2.
Qed.

Lemma omega_pow4 :
  omega * omega * omega * omega = -1.
Proof.
  rewrite omega_pow2.
  rewrite <- com_mul_assoc.
  rewrite omega_pow2.
  com_simpl.
Qed.

Lemma domega_coeff_add :
  forall a b k,
    domega_coeff (a + b)%Z k =
    (domega_coeff a k + domega_coeff b k)%R.
Proof.
  intros a b k.
  unfold domega_coeff.
  rewrite plus_IZR.
  lra.
Qed.

Lemma domega_coeff_neg :
  forall d k,
    domega_coeff (-d)%Z k = (- domega_coeff d k)%R.
Proof.
  intros d k.
  unfold domega_coeff.
  rewrite opp_IZR.
  field.
  apply rpow2_nonzero.
Qed.

Lemma domega_coeff_sub :
  forall a b k,
    domega_coeff (a - b)%Z k =
    (domega_coeff a k - domega_coeff b k)%R.
Proof.
  intros a b k.
  replace (a - b)%Z with (a + (-b))%Z by lia.
  rewrite domega_coeff_add.
  rewrite domega_coeff_neg.
  lra.
Qed.

Lemma domega_coeff_mul :
  forall a b k1 k2,
    domega_coeff (a * b)%Z (k1 + k2) =
    (domega_coeff a k1 * domega_coeff b k2)%R.
Proof.
  intros a b k1 k2.
  unfold domega_coeff.
  rewrite mult_IZR.
  rewrite rpow2_add.
  field.
  split; apply rpow2_nonzero.
Qed.

Lemma domega_coeff_add_align :
  forall dx dy kx ky target_k,
    (kx <= target_k)%nat ->
    (ky <= target_k)%nat ->
    domega_coeff
      (dx * pow2 (target_k - kx)
       + dy * pow2 (target_k - ky))%Z
      target_k
    =
    (domega_coeff dx kx + domega_coeff dy ky)%R.
Proof.
  intros dx dy kx ky target_k Hx Hy.

  unfold domega_coeff at 1.
  rewrite plus_IZR.
  rewrite Rdiv_plus_distr.

  replace (IZR (dx * pow2 (target_k - kx)) / rpow2 target_k)%R
    with (domega_coeff (dx * pow2 (target_k - kx)) target_k)%R by reflexivity.
  replace (IZR (dy * pow2 (target_k - ky)) / rpow2 target_k)%R
    with (domega_coeff (dy * pow2 (target_k - ky)) target_k)%R by reflexivity.

  rewrite (domega_coeff_align dx kx target_k Hx).
  rewrite (domega_coeff_align dy ky target_k Hy).

  reflexivity.
Qed.

Lemma complex_of_domega_add :
  forall x y,
    complex_of_domega (domega_add x y) =
    (complex_of_domega x + complex_of_domega y)%com.
Proof.
  intros x y.
  set (k := domega_common_k x y).
  destruct (domega_common_k_le x y) as [Hx Hy].
  unfold domega_add.
  fold k.
  unfold complex_of_domega, domega_align.
  simpl.

  (* d0,d1,d2,d3 각각 *)
  repeat rewrite domega_coeff_add_align by assumption.
  com_simpl.
Qed.

Lemma complex_of_domega_neg :
  forall x,
    complex_of_domega (domega_neg x) = (- complex_of_domega x)%com.
Proof.
  intros x.
  unfold complex_of_domega, domega_neg.
  simpl.
  repeat rewrite domega_coeff_neg.
  com_simpl.
Qed.

Lemma complex_of_domega_sub :
  forall x y,
    complex_of_domega (domega_sub x y) =
    (complex_of_domega x - complex_of_domega y)%com.
Proof.
  intros x y.
  unfold domega_sub.
  rewrite complex_of_domega_add.
  rewrite complex_of_domega_neg.
  com_simpl.
Qed.

Lemma complex_of_domega_zero :
  complex_of_domega domega_zero = Czero.
Proof.
  unfold complex_of_domega, domega_zero, domega_make, domega_coeff, rpow2.
  simpl.
  lca.
Qed.

Lemma complex_of_domega_one :
  complex_of_domega domega_one = Cone.
Proof.
  unfold complex_of_domega, domega_one, domega_make, domega_coeff, rpow2.
  simpl.
  lca.
Qed.

Lemma complex_of_domega_w :
  complex_of_domega domega_w = omega.
Proof.
  unfold complex_of_domega, domega_w, domega_make, domega_coeff, rpow2.
  simpl.
  lca.
Qed.

Lemma complex_of_domega_w2 :
  complex_of_domega domega_w2 = Ione.
Proof.
  unfold complex_of_domega, domega_w2, domega_make, domega_coeff, rpow2.
  simpl.
  repeat replace (0 / 1)%R with 0%R by lra.
  replace (1 / 1)%R with 1%R by lra.
  rewrite omega_pow2.
  lca.
Qed.

Lemma complex_of_domega_w3 :
  complex_of_domega domega_w3 = (omega * Ione)%com.
Proof.
  unfold complex_of_domega, domega_w3, domega_make, domega_coeff, rpow2.
  simpl.
  repeat replace (0 / 1)%R with 0%R by lra.
  replace (1 / 1)%R with 1%R by lra.
  rewrite omega_pow2.
  lca.
Qed.

Lemma complex_of_domega_neg_one :
  complex_of_domega domega_minus_one = (- Cone)%com.
Proof.
  unfold domega_minus_one.
  rewrite complex_of_domega_neg, complex_of_domega_one.
  lca.
Qed.

Lemma complex_of_domega_neg_w2 :
  complex_of_domega domega_minus_i = (- Ione)%com.
Proof.
  unfold domega_minus_i.
  rewrite complex_of_domega_neg, complex_of_domega_w2.
  lca.
Qed.

Lemma complex_of_domega_neg_w3 :
  complex_of_domega (domega_neg domega_w3) = (- (omega * Ione))%com.
Proof.
  rewrite complex_of_domega_neg, complex_of_domega_w3.
  lca.
Qed.

Lemma complex_of_domega_neg_w3_exp :
  complex_of_domega (domega_neg domega_w3) = com_iexp (- PI / 4).
Proof.
  rewrite complex_of_domega_neg_w3.
  replace (- PI / 4)%R with (-(PI / 4))%R by field.
  unfold omega, com_iexp.
  rewrite cos_neg, sin_neg, cos_PI4, sin_PI4.
  lca.
Qed.

Lemma domega_h_scalar_to_complex :
  complex_of_domega domega_h_scalar = (/ sqrt 2)%R.
Proof.
  unfold domega_h_scalar, complex_of_domega, domega_make, domega_coeff,
    rpow2.
  simpl.
  repeat replace (0 / 2)%R with 0%R by lra.
  repeat replace (1 / 2)%R with (/ 2)%R by lra.
  replace (-1 / 2)%R with (- / 2)%R by lra.
  rewrite omega_pow2.
  unfold omega, com_iexp.
  rewrite cos_PI4, sin_PI4.
  apply com_proj_eq; simpl.
  - field_simplify_eq; try solve [apply sqrt2_neq_0].
    replace (sqrt 2 ^ 2)%R with 2%R by
      (simpl; rewrite Rmult_1_r; rewrite sqrt_sqrt; lra).
    lra.
  - field_simplify_eq; try solve [apply sqrt2_neq_0].
    replace (sqrt 2 ^ 2)%R with 2%R by
      (simpl; rewrite Rmult_1_r; rewrite sqrt_sqrt; lra).
    lra.
Qed.

Lemma complex_of_domega_half_one_plus_i :
  complex_of_domega domega_half_one_plus_i =
  (RTC (1 / 2) * (Cone + Ione))%com.
Proof.
  unfold domega_half_one_plus_i, complex_of_domega, domega_make,
    domega_coeff, rpow2.
  simpl.
  repeat replace (0 / 2)%R with 0%R by lra.
  repeat replace (1 / 2)%R with (/ 2)%R by lra.
  rewrite omega_pow2.
  lca.
Qed.

Lemma complex_of_domega_half_one_minus_i :
  complex_of_domega domega_half_one_minus_i =
  (RTC (1 / 2) * (Cone - Ione))%com.
Proof.
  unfold domega_half_one_minus_i, complex_of_domega, domega_make,
    domega_coeff, rpow2.
  simpl.
  repeat replace (0 / 2)%R with 0%R by lra.
  repeat replace (1 / 2)%R with (/ 2)%R by lra.
  replace (-1 / 2)%R with (- / 2)%R by lra.
  rewrite omega_pow2.
  lca.
Qed.

Lemma gphase_neg_shift :
  forall a,
    (- gphase a)%com = gphase (PI + a).
Proof.
  intros a.
  unfold gphase, com_iexp.
  apply com_proj_eq; simpl.
  - rewrite cos_plus, cos_PI, sin_PI.
    lra.
  - rewrite sin_plus, cos_PI, sin_PI.
    lra.
Qed.

Lemma complex_of_domega_w_gphase :
  complex_of_domega domega_w = gphase (PI / 4).
Proof.
  rewrite complex_of_domega_w.
  reflexivity.
Qed.

Lemma complex_of_domega_w2_gphase :
  complex_of_domega domega_w2 = gphase (PI / 2).
Proof.
  rewrite complex_of_domega_w2.
  unfold gphase.
  symmetry.
  apply com_iexp_PI2.
Qed.

Lemma complex_of_domega_w3_gphase :
  complex_of_domega domega_w3 = gphase (3 * PI / 4).
Proof.
  unfold complex_of_domega, domega_w3, domega_make, domega_coeff,
    rpow2, gphase, omega.
  simpl.
  repeat replace ((0 / 1)%R) with 0%R by lra.
  replace ((1 / 1)%R) with 1%R by lra.
  com_simpl.
  repeat rewrite <- com_iexp_mul.
  replace (PI / 4 + PI / 4 + PI / 4)%R with (3 * PI / 4)%R
    by lra.
  reflexivity.
Qed.

Lemma complex_of_domega_mul :
  forall x y,
    complex_of_domega (domega_mul x y) =
    (complex_of_domega x * complex_of_domega y)%com.
Proof.
  intros x y.
  unfold domega_mul.
  unfold complex_of_domega.
  simpl.

  repeat rewrite domega_coeff_sub.
  repeat rewrite domega_coeff_add.
  repeat rewrite domega_coeff_mul.
  repeat rewrite omega_pow2.
  repeat rewrite com_Ione_sq'.
  repeat rewrite com_Ione_sq.
  apply com_proj_eq; simpl.
  all: rewrite cos_PI4, sin_PI4.
  all: field_simplify_eq; try solve [apply sqrt2_neq_0].
  all: replace (sqrt 2 ^ 2)%R with 2%R by
    (simpl; rewrite Rmult_1_r; rewrite sqrt_sqrt; lra).
  all: nra.
Qed.

Fixpoint domega_pow8 (n : nat) : DOmega :=
  match n with
  | 0 => domega_one
  | 1 => domega_w
  | 2 => domega_w2
  | 3 => domega_w3
  | 4 => domega_neg domega_one
  | 5 => domega_neg domega_w
  | 6 => domega_neg domega_w2
  | 7 => domega_neg domega_w3
  | S (S (S (S (S (S (S (S n'))))))) => domega_pow8 n'
  end.

Definition domega_phase_list : list DOmega :=
  [ domega_pow8 0; domega_pow8 1; domega_pow8 2; domega_pow8 3;
    domega_pow8 4; domega_pow8 5; domega_pow8 6; domega_pow8 7 ].

Lemma domega_phase_gphase :
  forall phase,
    In phase domega_phase_list ->
    exists lambda,
      complex_of_domega phase = gphase lambda.
Proof.
  intros phase Hin.
  simpl in Hin.
  repeat destruct Hin as [Hin | Hin]; subst; try contradiction.
  - exists 0%R.
    rewrite complex_of_domega_one.
    unfold gphase.
    rewrite com_iexp_0.
    reflexivity.
  - exists (PI / 4)%R.
    apply complex_of_domega_w_gphase.
  - exists (PI / 2)%R.
    apply complex_of_domega_w2_gphase.
  - exists (3 * PI / 4)%R.
    apply complex_of_domega_w3_gphase.
  - exists PI.
    rewrite complex_of_domega_neg, complex_of_domega_one.
    unfold gphase.
    rewrite com_iexp_PI.
    com_simpl.
  - exists (PI + PI / 4)%R.
    rewrite complex_of_domega_neg, complex_of_domega_w_gphase.
    apply gphase_neg_shift.
  - exists (PI + PI / 2)%R.
    rewrite complex_of_domega_neg, complex_of_domega_w2_gphase.
    apply gphase_neg_shift.
  - exists (PI + 3 * PI / 4)%R.
    rewrite complex_of_domega_neg, complex_of_domega_w3_gphase.
    apply gphase_neg_shift.
Qed.

End DOMEGA_ARITHMETIC.
