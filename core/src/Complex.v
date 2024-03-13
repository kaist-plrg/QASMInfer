Require Export Bool.
Require Export Arith.
Require Export NDiv0.
Require Export Reals.
Require Export Reals.Rtrigo_facts.
Require Export Psatz.
Require Export List.
Require Export Coq.Logic.ProofIrrelevance.
Require Export Coq.Logic.PropExtensionality.
Import ListNotations.
Require Import Classical_Prop.
Require Export FunctionalExtensionality.

Declare Scope Complex_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Bind Scope R_scope with R.
Open Scope Complex_scope.
Delimit Scope Complex_scope with com.


Definition Complex := (R * R)%type.

Definition Cmake (re im: R) := (re, im).

Definition Czero : Complex := (0, 0).
Definition Cone : Complex := (1, 0).
Definition Ione : Complex := (0, 1).

Definition RTC (x: R) : Complex := (x, 0).
Definition RTIm (y: R) : Complex := (0, y).
Definition NTC (n: nat) : Complex := (INR n, 0).

Coercion RTC : R >-> Complex.
Coercion NTC : nat >-> Complex.

Lemma com_proj_eq: forall (c1 c2: Complex),
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof.
  intros c1 c2 H1 H2.
  destruct c1, c2.
  simpl in *.
  subst.
  reflexivity.
Qed.

Lemma com_proj_neq_fst: forall (c1 c2: Complex), (fst c1 <> fst c2)%R -> c1 <> c2.
Proof.
  intros [r1 i1] [r2 i2] H.
  simpl in *.
  intro H'.
  inversion H'.
  lra.
Qed.

Ltac lca := eapply com_proj_eq; simpl; lra.

Definition com_add (x y : Complex) : Complex := (fst x + fst y, snd x + snd y).
Definition com_neg (x : Complex) : Complex := (-fst x, -snd x).
Definition com_sub (x y : Complex) : Complex := com_add x (com_neg y).
Definition com_mul (x y : Complex) : Complex := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition com_inv (x : Complex) : Complex := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition com_div (x y : Complex) : Complex := com_mul x (com_inv y).

Infix "+" := com_add : Complex_scope.
Notation "- x" := (com_neg x) : Complex_scope.
Infix "-" := com_sub : Complex_scope.
Infix "*" := com_mul : Complex_scope.
Notation "/ x" := (com_inv x) : Complex_scope.
Infix "/" := com_div : Complex_scope.

Definition com_abs_sq (x : Complex) : R := fst x ^ 2 + snd x ^ 2.
Definition com_abs (x : Complex) : R := sqrt (com_abs_sq x).

Definition com_exp (x : Complex) : Complex :=
  let r := fst x in
  let theta := snd x in
  (exp r) * ((cos theta) + RTIm (sin theta)).

Definition com_iexp (theta : R) : Complex := (cos theta) + RTIm (sin theta).

Lemma com_inv_mult: forall c: Complex, c <> 0 -> / c * c = 1.
Proof.
  intros [r i] H.
  unfold com_inv, com_mul.
  simpl.
  apply com_proj_eq.
  - simpl.
    repeat rewrite Rmult_1_r.
    field_simplify_eq.
    reflexivity.
    destruct (Req_dec r 0), (Req_dec i 0).
    + subst r i.
      contradiction.
    + nra.
    + nra.
    + nra.
  - simpl.
    repeat rewrite Rmult_1_r.
    field_simplify_eq.
    reflexivity.
    destruct (Req_dec r 0), (Req_dec i 0).
    + subst r i.
      contradiction.
    + nra.
    + nra.
    + nra.
Qed.

Definition com_real (z : Complex) : R := fst z.
Definition com_imag (z : Complex) : R := snd z.

Lemma com_real_plus: forall (z1 z2: Complex), com_real (z1 + z2) = (com_real z1 + com_real z2)%R.
Proof.
  intros [r1 i1] [r2 i2].
  unfold com_real.
  simpl.
  lra.
Qed.

Lemma com_imag_plus: forall (z1 z2: Complex), com_imag (z1 + z2) = (com_imag z1 + com_imag z2)%R.
Proof.
  intros [r1 i1] [r2 i2].
  unfold com_imag.
  simpl.
  lra.
Qed.

Lemma com_mul_real: forall (x y: Complex),
  com_imag x = 0 -> com_imag y = 0 ->
  x * y = ((com_real x * com_real y)%R, 0).
Proof.
  intros [r1 i1] [r2 i2].
  unfold com_real.
  simpl.
  intros.
  subst.
  lca.
Qed.

Lemma com_real_mult_ge0: forall (x y: Complex),
  com_real x >= 0 -> com_real y >= 0 -> com_imag x = 0 -> com_imag y = 0 -> com_real (x * y) >= 0.
Proof.
  intros.
  rewrite com_mul_real; try assumption.
  simpl.
  nra.
Qed.

Lemma com_imag_0_inv: forall (x: Complex), com_imag x = 0 -> com_imag (/ x) = 0.
Proof.
  intros [r1 i1].
  simpl.
  intros.
  nra.
Qed.

Lemma com_imag_0_plus: forall (x y: Complex), com_imag x = 0 -> com_imag y = 0 -> com_imag (x + y) = 0.
Proof.
  intros.
  rewrite com_imag_plus.
  lra.
Qed.

Lemma com_imag_0_mult: forall (x y: Complex), com_imag x = 0 -> com_imag y = 0 -> com_imag (x * y) = 0.
Proof.
  intros.
  rewrite com_mul_real; try assumption.
  reflexivity.
Qed.

Definition com_conj (x : Complex) : Complex := (fst x, (- snd x)%R).

Notation "x ^*" := (com_conj x) (at level 30) : Complex_scope.

Lemma com_conj_add: forall (x1 x2: Complex), (x1 + x2)^* = x1^* + x2^*.
Proof. intros. lca. Qed.

Lemma com_conj_sub: forall (x1 x2: Complex), (x1 - x2)^* = x1^* - x2^*.
Proof. intros. lca. Qed.

Lemma com_conj_mul: forall (x1 x2: Complex), (x1 * x2)^* = x1^* * x2^*.
Proof. intros. lca. Qed.

Lemma com_conj_involutive: forall (x: Complex), x^*^* = x.
Proof. intros. lca. Qed.

Lemma com_conj_real: forall (x: Complex), x^* = x <-> com_imag x = 0.
Proof.
  intros [r i].
  unfold com_conj.
  simpl.
  split; intros.
  - inversion H.
    lra.
  - subst.
    lca.
Qed.

Lemma com_conj_real_l : forall (x: Complex), com_imag x = 0 -> x^* = x.
Proof. apply com_conj_real. Qed.

Lemma com_conj_real_r : forall (x: Complex), x^* = x -> com_imag x = 0.
Proof. apply com_conj_real. Qed.

Lemma com_conj_Ione: Ione^* = - Ione.
Proof. lca. Qed.

Lemma com_nat_conj: forall (n: nat), n^* = n.
Proof.
  intros.
  apply com_conj_real.
  reflexivity.
Qed.

Lemma com_real_conj: forall (x: R), x^* = x.
Proof.
  intros.
  apply com_conj_real.
  reflexivity.
Qed.

Lemma com_sin_conj: forall (x: R), (sin x)^* = sin x.
Proof.
  intros.
  apply com_real_conj.
Qed.

Lemma com_cos_conj: forall (x: R), (cos x)^* = cos x.
Proof.
  intros.
  apply com_real_conj.
Qed.

Lemma com_RTIm_conj: forall (x: R), RTIm x ^* = - RTIm x.
Proof.
  intros.
  unfold com_conj.
  lca.
Qed.

Definition com_ge_0 (x: Complex) := com_real x >= 0 /\ com_imag x = 0.
Notation "x >= 0" := (com_ge_0 x) (at level 70, no associativity) : Complex_scope.

Lemma com_ge0_add: forall x y, x >= 0 -> y >= 0 -> (x + y) >= 0.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  unfold com_ge_0, com_real, com_imag in *.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma com_ge0_mul: forall x y, x >= 0 -> y >= 0 -> (x * y) >= 0.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  unfold com_ge_0, com_real, com_imag in *.
  split.
  - simpl. nra.
  - simpl. nra.
Qed.

Lemma com_ge0_inv: forall x, x >= 0 -> (/ x) >= 0.
Proof.
  intros [r i] [Hx1 Hx2].
  unfold com_ge_0, com_real, com_imag in *.
  simpl in *.
  subst i.
  destruct (Req_dec r 0).
  - nra.
  - assert (r > 0) by lra.
    split.
    + rewrite Rmult_0_l.
      rewrite Rplus_0_r.
      rewrite Rmult_1_r.
      unfold Rdiv.
      assert (r * r > 0) by nra.
      assert (/ (r * r) > 0).
      { apply Rinv_0_lt_compat.
        lra. }
      nra.
    + nra.
Qed.

Lemma com_real_ge0: forall x: R, (x >= R0)%R -> (x >= 0)%com.
Proof.
  intros.
  split.
  all: simpl; auto.
Qed.

Lemma com_conj_mul_ge0_l: forall (x: Complex), (x^* * x) >= 0.
Proof.
  intros.
  split.
  - unfold com_real, com_conj, com_mul.
    simpl.
    nra.
  - unfold com_real, com_conj, com_mul.
    simpl.
    nra.
Qed.

Lemma com_conj_mul_ge0_r: forall (x: Complex), (x * x^*) >= 0.
Proof.
  intros.
  rewrite <- (com_conj_involutive x) at 1.
  apply com_conj_mul_ge0_l.
Qed.

Lemma RTC_inj: forall (x y: R),
  RTC x = RTC y -> x = y.
Proof.
  intros x y H.
  now apply (f_equal fst) in H.
Qed.


Lemma com_add_assoc : forall x y z: Complex, com_add x (com_add y z) = com_add (com_add x y) z.
Proof. intros. lca. Qed.

Lemma com_add_comm : forall x y: Complex, com_add x y = com_add y x.
Proof. intros. lca. Qed.

Lemma com_add_0_l: forall (c: Complex), 0 + c = c.
Proof. intros. lca. Qed.

Lemma com_add_0_r: forall (c: Complex), c + 0 = c.
Proof. intros. lca. Qed.

Lemma com_mul_0_l: forall (c: Complex), 0 * c = 0.
Proof. intros. lca. Qed.

Lemma com_mul_0_r: forall (c: Complex), c * 0 = 0.
Proof. intros. lca. Qed.

Lemma com_mul_1_l: forall (c: Complex), 1 * c = c.
Proof. intros. lca. Qed.

Lemma com_mul_1_r: forall (c: Complex), c * 1 = c.
Proof. intros. lca. Qed.

Lemma com_add_opp_r : forall x y: Complex, com_sub x y = com_add x (com_neg y).
Proof. intros. lca. Qed.

Lemma com_mul_assoc : forall x y z: Complex, com_mul x (com_mul y z) = com_mul (com_mul x y) z.
Proof. intros. lca. Qed.

Lemma com_mul_comm : forall x y: Complex, com_mul x y = com_mul y x.
Proof. intros. lca. Qed.

Lemma com_mul_one_l : forall x: Complex, com_mul Cone x = x.
Proof. intros. lca. Qed.

Lemma com_mul_plus_distr_l : forall x y z: Complex, com_mul (com_add x y) z = com_add (com_mul x z) (com_mul y z).
Proof. intros. lca. Qed.

Lemma com_neg_involutive: forall (x: Complex), - (- x) = x.
Proof. intros. lca. Qed.

Lemma com_add_neg: forall (x y: Complex), x + (- y) = x - y.
Proof. intros. lca. Qed.

Lemma com_neg_conj_comm : forall (x: Complex), (- x)^* = - (x^*).
Proof. intros. lca. Qed.

Lemma com_neg_RTIm_comm : forall (x: R), RTIm (- x) = - RTIm x.
Proof. intros. lca. Qed.

Lemma com_neg_mul_comm : forall (x y: Complex), x * (- y) = - (x * y).
Proof. intros. lca. Qed.

Lemma com_Ione_sq: Ione * Ione = -1.
Proof. lca. Qed.

Lemma com_Ione_sq': forall x, x * Ione * Ione = - x.
Proof. intros. lca. Qed.

Lemma com_exp_conj_comm: forall (x: Complex), (com_exp x)^* = com_exp (x^*).
Proof.
  intros [r i].
  unfold com_exp; simpl.
  rewrite cos_neg, sin_neg.
  lca.
Qed.

Lemma com_iexp_conj_anticomm: forall (theta: R), (com_iexp theta)^* = com_iexp (- theta).
Proof.
  intros.
  unfold com_iexp.
  rewrite cos_neg, sin_neg.
  lca.
Qed.

Lemma com_exp_mul: forall (x y: Complex), com_exp (x + y) = com_exp x * com_exp y.
Proof.
  intros [r1 i1] [r2 i2].
  unfold com_exp, com_add, com_mul.
  simpl.
  rewrite cos_plus, sin_plus.
  f_equal.
  all: rewrite exp_plus; ring.
Qed.

Lemma com_iexp_mul: forall (x y : R), com_iexp (x + y) = com_iexp x * com_iexp y.
Proof.
  intros.
  unfold com_iexp, RTIm, com_add, com_mul.
  rewrite cos_plus, sin_plus; simpl.
  f_equal.
  all: ring.
Qed.

Lemma com_iexp_mul': forall c x y, c * com_iexp (x + y) = c * com_iexp x * com_iexp y.
Proof.
  intros.
  rewrite <- com_mul_assoc.
  rewrite com_iexp_mul.
  reflexivity.
Qed.

Lemma com_exp_0: com_exp 0 = 1.
Proof.
  unfold com_exp; simpl.
  rewrite cos_0, sin_0.
  rewrite exp_0.
  lca.
Qed.

Lemma com_iexp_0: com_iexp 0 = 1.
Proof.
  unfold com_iexp.
  rewrite cos_0, sin_0.
  lca.
Qed.

Lemma com_iexp_0_impl: forall (x: R), x = 0 -> com_iexp x = 1.
Proof. intros. subst. apply com_iexp_0. Qed.

Lemma com_iexp_inv_l: forall (x: R), com_iexp (- x) * com_iexp x = 1.
Proof.
  intros.
  rewrite <- com_iexp_mul.
  apply com_iexp_0_impl.
  lra.
Qed.

Lemma com_iexp_inv_l': forall c x, c * com_iexp (- x) * com_iexp x = c.
Proof.
  intros.
  rewrite <- com_mul_assoc.
  rewrite com_iexp_inv_l.
  lca.
Qed.

Lemma com_iexp_inv_r: forall (x: R), com_iexp x * com_iexp (- x) = 1.
Proof.
  intros.
  rewrite <- com_iexp_mul.
  apply com_iexp_0_impl.
  lra.
Qed.

Lemma com_iexp_inv_r': forall c x, c * com_iexp x * com_iexp (- x) = c.
Proof.
  intros.
  rewrite <- com_mul_assoc.
  rewrite com_iexp_inv_r.
  lca.
Qed.

Lemma com_sin2_cos2: forall (x: R), sin x * sin x + cos x * cos x = 1.
Proof.
  intros.
  specialize (sin2_cos2 x) as H.
  unfold Rsqr in H.
  lca.
Qed.

Lemma com_cos2_sin2: forall (x: R), cos x * cos x + sin x * sin x = 1.
Proof.
  intros.
  specialize (sin2_cos2 x) as H.
  unfold Rsqr in H.
  lca.
Qed.

Definition C_Ring: Ring_theory.ring_theory Czero Cone com_add com_mul com_sub com_neg eq.
Proof.
  constructor.
  - apply com_add_0_l.
  - apply com_add_comm.
  - apply com_add_assoc.
  - apply com_mul_one_l.
  - apply com_mul_comm.
  - apply com_mul_assoc.
  - apply com_mul_plus_distr_l.
  - apply com_add_opp_r.
  - intros. lca.
Qed.

Add Ring CRing: C_Ring.

Lemma com_add_cancel_l: forall x y z: Complex, y = z -> x + y = x + z.
Proof. intros. rewrite H. reflexivity. Qed.

Ltac com_simpl := repeat (
  rewrite com_add_0_l || rewrite com_add_0_r ||
  rewrite com_mul_0_l || rewrite com_mul_0_r ||
  rewrite com_mul_1_l || rewrite com_mul_1_r ||
  rewrite com_Ione_sq || rewrite com_Ione_sq' ||
  rewrite com_neg_involutive ||
  rewrite com_add_neg ||
  rewrite com_real_conj ||
  rewrite com_nat_conj ||
  rewrite com_conj_Ione ||
  rewrite com_conj_add || rewrite com_conj_sub || rewrite com_conj_mul ||
  rewrite com_conj_involutive ||
  rewrite com_sin_conj ||
  rewrite com_cos_conj ||
  rewrite com_neg_mul_comm ||
  rewrite com_neg_conj_comm ||
  rewrite com_exp_0 || rewrite com_iexp_0 ||
  rewrite com_iexp_inv_l || rewrite com_iexp_inv_l' || rewrite com_iexp_inv_r || rewrite com_iexp_inv_r' ||
  rewrite com_exp_conj_comm || rewrite com_iexp_conj_anticomm ||
  rewrite <- com_exp_mul || rewrite <- com_iexp_mul || rewrite <- com_iexp_mul' ||
  rewrite com_sin2_cos2 || rewrite com_cos2_sin2 ||
  lca || ring_simplify || simpl || auto
).

Ltac R_simpl := repeat (
  rewrite Rplus_0_l || rewrite Rplus_0_r ||
  rewrite Rmult_0_l || rewrite Rmult_0_r ||
  rewrite Rmult_1_l || rewrite Rmult_1_r ||
  rewrite Rmult_1_l || rewrite Rmult_1_r ||
  rewrite Ropp_0 || rewrite Ropp_involutive ||
  rewrite Ropp_plus_distr ||
  rewrite Ropp_mult_distr_l ||
  rewrite Ropp_mult_distr_r ||
  rewrite Ropp_involutive ||
  rewrite Rmult_plus_distr_l ||
  rewrite Rmult_plus_distr_r ||
  rewrite Rplus_assoc ||
  rewrite Rplus_opp_l ||
  rewrite Rplus_opp_r ||
  rewrite Rplus_0_l ||
  rewrite Rplus_0_r ||
  rewrite Rmult_assoc ||
  rewrite Rinv_l ||
  rewrite Rinv_r ||
  lra || ring_simplify || simpl || auto
).

Ltac ring_simplify_sub :=
  try ring_simplify;
  repeat match goal with
    | [ |- context[?E] ] => progress (ring_simplify E)
  end.

Definition C_Field: Field_theory.field_theory Czero Cone com_add com_mul com_sub com_neg com_div com_inv eq.
Proof.
  constructor.
  - exact C_Ring.
  - apply com_proj_neq_fst. simpl. lra.
  - unfold com_div. reflexivity.
  - apply com_inv_mult.
Qed.
