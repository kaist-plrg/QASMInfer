Require Export Util.

Declare Scope C_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Bind Scope R_scope with R.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Delimit Scope C_scope with C.


Definition C := (R * R)%type.

Definition Czero : C := (0, 0).
Definition Cone : C := (1, 0).

Definition RTC (x: R): C := (x, 0).
Definition NTC (n: nat): C := (INR n, 0).

Coercion RTC : R >-> C.
Coercion NTC : nat >-> C.

Lemma c_proj_eq: forall (c1 c2: C),
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof.
  intros c1 c2 H1 H2.
  destruct c1, c2.
  simpl in *.
  subst.
  reflexivity.
Qed.

Ltac lca := eapply c_proj_eq; simpl; lra.

Definition Cplus (x y : C) : C := (fst x + fst y, snd x + snd y).
Definition Copp (x : C) : C := (-fst x, -snd x).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition Cinv (x : C) : C := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).

Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.

Definition Cabs_sq (x : C) : R := fst x ^ 2 + snd x ^ 2.
Definition Cabs (x : C) : R := sqrt (Cabs_sq x).

Definition Carg (x : C) : R := atan2 (fst x) (snd x).

Definition Cexp (x : C): C :=
  let r := fst x in
  let theta := snd x in
  (exp r) * ((cos theta) + (0, sin theta)).

Definition Cln (x: C): C := (ln (Cabs x), Carg x).

Definition Cpow (cb ce: C): C := Cexp ((Cln cb) * ce).
Infix "^" := Cpow : C_scope.

Definition Creal (z : C) : R := fst z.

Definition Cimag (z : C) : R := snd z.

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Lemma Cconj_plus: forall (x1 x2: C), Cconj (x1 + x2) = Cconj x1 + Cconj x2.
Proof. intros. lca. Qed.

Lemma Cconj_mult: forall (x1 x2: C), Cconj (x1 * x2) = Cconj x1 * Cconj x2.
Proof. intros. lca. Qed.

Lemma RTC_inj: forall (x y: R),
  RTC x = RTC y -> x = y.
Proof.
  intros x y H.
  now apply (f_equal fst) in H.
Qed.


Lemma Cplus_assoc : forall x y z: C, Cplus x (Cplus y z) = Cplus (Cplus x y) z.
Proof. intros. lca. Qed.

Lemma Cplus_comm : forall x y: C, Cplus x y = Cplus y x.
Proof. intros. lca. Qed.

Lemma Cplus_0_l: forall (c: C), 0 + c = c.
Proof. intros. lca. Qed.

Lemma Cplus_0_r: forall (c: C), c + 0 = c.
Proof. intros. lca. Qed.

Lemma Cmult_0_l: forall (c: C), 0 * c = 0.
Proof. intros. lca. Qed.

Lemma Cmult_0_r: forall (c: C), c * 0 = 0.
Proof. intros. lca. Qed.

Lemma Cplus_opp_r : forall x y: C, Cminus x y = Cplus x (Copp y).
Proof. intros. lca. Qed.

Lemma Cmult_assoc : forall x y z: C, Cmult x (Cmult y z) = Cmult (Cmult x y) z.
Proof. intros. lca. Qed.

Lemma Cmult_comm : forall x y: C, Cmult x y = Cmult y x.
Proof. intros. lca. Qed.

Lemma Cmult_one_l : forall x: C, Cmult Cone x = x.
Proof. intros. lca. Qed.

Lemma Cmult_plus_distr_l : forall x y z: C, Cmult (Cplus x y) z = Cplus (Cmult x z) (Cmult y z).
Proof. intros. lca. Qed.

Definition C_Ring: Ring_theory.ring_theory Czero Cone Cplus Cmult Cminus Copp eq.
Proof.
  constructor.
  - apply Cplus_0_l.
  - apply Cplus_comm.
  - apply Cplus_assoc.
  - apply Cmult_one_l.
  - apply Cmult_comm.
  - apply Cmult_assoc.
  - apply Cmult_plus_distr_l.
  - apply Cplus_opp_r.
  - intros. lca.
Qed.

Add Ring CRing: C_Ring.

Lemma Cplus_cancel_l: forall x y z: C, y = z -> x + y = x + z.
Proof. intros. rewrite H. reflexivity. Qed.
