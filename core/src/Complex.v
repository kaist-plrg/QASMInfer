Require Export Util.
Require Export NDiv0.
Require Export FunctionalExtensionality.

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

Definition Cmake (re im: R) := (re, im).

Definition Czero : C := (0, 0).
Definition Cone : C := (1, 0).

Definition RTC (x: R): C := (x, 0).
Definition RTIm (y: R): C := (0, y).
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
  (exp r) * ((cos theta) + RTIm (sin theta)).

Definition Cln (x: C): C := Cmake (ln (Cabs x)) (Carg x).

Definition Cpow (cb ce: C): C := Cexp ((Cln cb) * ce).
Infix "^" := Cpow : C_scope.

Lemma Cinv_mult: forall c: C, c <> 0 -> / c * c = 1.
Proof.
  intros [r i] H.
  unfold Cinv, Cmult.
  simpl.
  apply c_proj_eq.
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

Definition Creal (z : C) : R := fst z.

Lemma Creal_plus: forall (z1 z2: C), (Creal (z1 + z2), 0) = (Creal z1 + Creal z2).
Proof.
  intros [r1 i1] [r2 i2].
  unfold Creal.
  simpl.
  lca.
Qed.

Definition Cimag (z : C) : R := snd z.

Lemma Cmult_real: forall (x y: C),
  Cimag x = 0 -> Cimag y = 0 -> Cimag (x * y) = 0.
Proof.
  intros [r1 i1] [r2 i2].
  unfold Creal.
  simpl.
  intros.
  nra.
Qed.

Lemma Creal_mult_ge0: forall (x y: C),
  Creal x >= 0 -> Creal y >= 0 -> Cimag x = 0 -> Cimag y = 0 -> Creal (x * y) >= 0.
Proof.
  intros [r1 i1] [r2 i2].
  unfold Creal.
  simpl.
  intros.
  nra.
Qed.

Lemma Cimag_0_inv: forall (x: C), Cimag x = 0 -> Cimag (/ x) = 0.
Proof.
  intros [r1 i1].
  unfold Cimag.
  simpl.
  intros.
  nra.
Qed.

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Lemma Cconj_plus: forall (x1 x2: C), Cconj (x1 + x2) = Cconj x1 + Cconj x2.
Proof. intros. lca. Qed.

Lemma Cconj_mult: forall (x1 x2: C), Cconj (x1 * x2) = Cconj x1 * Cconj x2.
Proof. intros. lca. Qed.

Lemma Cconj_twice: forall (x: C), Cconj (Cconj x) = x.
Proof. intros. lca. Qed.

Lemma Cconj_real: forall (x: C), Cconj x = x -> Cimag x = 0.
Proof.
  intros [r i].
  unfold Cconj.
  simpl.
  intros.
  inversion H.
  lra.
Qed.

Lemma Creal_conj: forall (x: C), Cimag x = 0 -> Cconj x = x.
Proof.
  intros [r i].
  unfold Cconj.
  simpl.
  intros.
  inversion H.
  lca.
Qed.

Definition Cge_0 (x: C) := Creal x >= 0 /\ Cimag x = 0.

Lemma Cge_0_plus: forall x y, Cge_0 x -> Cge_0 y -> Cge_0 (x + y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  unfold Cge_0, Creal, Cimag in *.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma Cge_0_mult: forall x y, Cge_0 x -> Cge_0 y -> Cge_0 (x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  unfold Cge_0, Creal, Cimag in *.
  split.
  - simpl. nra.
  - simpl. nra.
Qed.

Lemma Cge_0_inv: forall x, Cge_0 x -> Cge_0 (/ x).
Proof.
  intros [r i] [Hx1 Hx2].
  unfold Cge_0, Creal, Cimag in *.
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

Lemma Cconj_mult_ge0: forall (x: C), Cge_0 (x * Cconj x).
Proof.
  intros.
  split.
  - unfold Creal, Cconj, Cmult.
    simpl.
    nra.
  - unfold Creal, Cconj, Cmult.
    simpl.
    nra.
Qed.

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

Lemma Cmult_1_l: forall (c: C), 1 * c = c.
Proof. intros. lca. Qed.

Lemma Cmult_1_r: forall (c: C), c * 1 = c.
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

(* nat -> C functin sum ========================================================================= *)

Fixpoint func_sum_suppl (f: nat -> C) (m n: nat): C :=
  match n with
  | O => O
  | S n' => f (m + n')%nat + func_sum_suppl f m n'
  end.

Definition func_sum2 (f: nat -> C) (m n: nat): C := func_sum_suppl f m (n - m).

Definition func_sum (f: nat -> C) (n: nat): C := func_sum2 f 0 n.

Lemma func_sum_suppl_scale: forall (n m: nat) (c: C) (f1 f2: nat -> C),
  (forall i, f1 i = c * f2 i) -> func_sum_suppl f1 n m = c * func_sum_suppl f2 n m.
Proof.
  intros.
  induction m as [|m'].
  - lca.
  - simpl.
    rewrite IHm'.
    rewrite H.
    lca.
Qed.

Lemma func_sum_suppl_add: forall (n m: nat) (f12 f1 f2: nat -> C),
  (forall i, f12 i = f1 i + f2 i) ->
  func_sum_suppl f12 n m = func_sum_suppl f1 n m + func_sum_suppl f2 n m.
Proof.
  intros.
  induction m as [|m'].
  - lca.
  - simpl.
    rewrite IHm'.
    rewrite H.
    lca.
Qed.

Lemma func_sum_suppl_sub: forall (n m: nat) (f12 f1 f2: nat -> C),
  (forall i, f12 i = f1 i - f2 i) ->
  func_sum_suppl f12 n m = func_sum_suppl f1 n m - func_sum_suppl f2 n m.
Proof.
  intros.
  induction m as [|m'].
  - lca.
  - simpl.
    rewrite IHm'.
    rewrite H.
    lca.
Qed.

Lemma func_sum_suppl_conj: forall (n m: nat) (f1 f2: nat -> C),
  (forall i, Cconj (f1 i) = f2 i) ->
  Cconj (func_sum_suppl f1 n m) = func_sum_suppl f2 n m.
Proof.
  intros.
  induction m as [|m'].
  - lca.
  - simpl.
    rewrite Cconj_plus.
    rewrite IHm'.
    rewrite H.
    lca.
Qed.

Lemma func_sum_f: forall (f1 f2: nat -> C) (n: nat),
  (forall i, (i < n)%nat -> f1 i = f2 i) -> func_sum f1 n = func_sum f2 n.
Proof.
  intros.
  unfold func_sum.
  unfold func_sum2.
  repeat rewrite Nat.sub_0_r.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite H.
    reflexivity.
    lia.
    intros.
    apply H.
    lia.
Qed.

Lemma func_sum2_split: forall (a b c: nat) (f: nat -> C),
  (a <= b <= c)%nat -> func_sum2 f a c = func_sum2 f a b + func_sum2 f b c.
Proof.
  intros a b c.
  revert a b.
  unfold func_sum2.
  induction c as [|c'].
  - intros.
    destruct H as [Hab Hbc].
    destruct b as [|b'].
    + destruct a as [|a'].
      * simpl.
        lca.
      * lia.
    + lia.
  - intros.
    destruct H as [Hab Hbc].
    destruct (Nat.eq_dec b (S c')).
    + subst b.
      simpl.
      replace (c' - c')%nat with O by lia.
      simpl.
      lca.
    + assert (b <= c')%nat as Hbc'.
      { apply le_lt_eq_dec in Hbc.
        destruct Hbc.
        all: lia. }
      replace (S c' - a)%nat with (S (c' - a)).
      replace (S c' - b)%nat with (S (c' - b)).
      simpl.
      rewrite IHc' with (b := b).
      replace (a + (c' - a))%nat with c'.
      replace (b + (c' - b))%nat with c'.
      ring_simplify.
      reflexivity.
      all: lia.
Qed.

Lemma func_sum2_split_mult: forall (n m: nat) (f: nat -> C),
  func_sum f (m + n * m) = func_sum2 f (n * m) (m + n * m) + func_sum f (n * m).
Proof.
  intros.
  unfold func_sum.
  ring_simplify.
  rewrite func_sum2_split with (b := (n * m)%nat).
  lca.
  lia.
Qed.

Lemma func_sum2_split3: forall (n m k: nat) (f: nat -> C),
  (n <= k < m)%nat ->
  func_sum2 f n m = func_sum2 f n k + func_sum2 f k (1 + k) + func_sum2 f (1 + k) m.
Proof.
  intros.
  rewrite func_sum2_split with (b := k).
  rewrite func_sum2_split with (a := k) (b := (1 + k)%nat).
  lca.
  all: lia.
Qed.

Lemma func_sum_suppl_zero: forall (n m: nat) (f: nat -> C),
  (forall k, (n <= k < n + m)%nat -> f k = 0) -> func_sum_suppl f n m = 0.
Proof.
  intros.
  induction m.
  - reflexivity.
  - simpl.
    rewrite IHm.
    rewrite H.
    lca.
    lia.
    intros.
    apply H.
    lia.
Qed.

Lemma func_sum2_zero: forall (n m: nat) (f: nat -> C),
  (forall k, (n <= k < m)%nat -> f k = 0) -> func_sum2 f n m = 0.
Proof.
  intros.
  unfold func_sum2.
  apply func_sum_suppl_zero.
  intros.
  apply H.
  lia.
Qed.

Lemma func_sum_suppl_pos: forall (n m: nat) (f: nat -> C),
  (forall k, (n <= k < n + m)%nat -> Cge_0 (f k)) -> Cge_0 (func_sum_suppl f n m).
Proof.
  intros.
  induction m.
  - split; [simpl; lra|simpl; lra].
  - simpl.
    apply Cge_0_plus.
    apply H.
    lia.
    apply IHm.
    intros.
    apply H.
    lia.
Qed.

Lemma func_sum_mod_suppl_l: forall (n m k i: nat) (f: nat -> C),
  (m > O)%nat -> (i <= k mod m)%nat ->
  func_sum_suppl (fun i : nat => if i mod m =? k mod m then f i else 0) (n * m) i = 0.
Proof.
  intros n m k i.
  revert n m k.
  induction i.
  - intros.
    reflexivity.
  - intros.
    simpl.
    rewrite IHi.
    replace ((n * m + i) mod m) with (i mod m).
    assert (i < m)%nat.
    { specialize (Nat.mod_bound_pos k m) as Hmod.
      lia. }
    assert (i mod m = i).
    { apply Nat.mod_small.
      apply H1. }
    rewrite H2.
    assert (i =? k mod m = false).
    { apply <- Nat.eqb_neq.
      lia. }
    rewrite H3.
    lca.
    rewrite Nat.Div0.add_mod.
    rewrite Nat.Div0.mul_mod.
    rewrite Nat.Div0.mod_same.
    rewrite Nat.mul_0_r.
    rewrite Nat.Div0.mod_0_l.
    simpl.
    rewrite Nat.mod_small.
    symmetry.
    apply Nat.mod_small.
    1-2: specialize (Nat.mod_bound_pos k m) as Hmod; lia.
    all: lia.
Qed.

Lemma func_sum_mod_suppl_m: forall (n m k: nat) (f: nat -> C),
  (m > O)%nat ->
  func_sum_suppl (fun i : nat => if i mod m =? k mod m then f i else 0) (n * m + (k mod m)) 1 = f (n * m + k mod m)%nat.
Proof.
  intros.
  simpl.
  assert (k mod m mod m = k mod m).
  { apply Nat.mod_small.
    specialize (Nat.mod_bound_pos k m) as Hmod. lia. }
  assert ((n * m + k mod m + 0) mod m =? k mod m = true).
  { apply <- Nat.eqb_eq.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.add_mod.
    rewrite Nat.Div0.mul_mod.
    rewrite Nat.Div0.mod_same.
    rewrite Nat.mul_0_r.
    rewrite Nat.Div0.mod_0_l.
    simpl.
    repeat rewrite H0.
    all: lia. }
  rewrite H1.
  rewrite Nat.add_0_r.
  lca.
Qed.

Lemma func_sum_mod_suppl_r: forall (n m k i: nat) (f: nat -> C),
  (m > O)%nat -> (i <= m - (k mod m) - 1)%nat ->
  func_sum_suppl (fun i : nat => if i mod m =? k mod m then f i else 0) (1 + (n * m + k mod m)) i = O.
Proof.
  intros n m k i.
  revert n m k.
  induction i.
  - intros.
    reflexivity.
  - intros.
    simpl.
    simpl in IHi.
    rewrite IHi.
    assert ((k mod m + 1 + i) < m)%nat by lia.
    assert ((n * m + k mod m + 1 + i) mod m =? k mod m = false).
    assert ((k mod m + 1 + i) mod m = (k mod m + 1 + i)%nat).
    { apply Nat.mod_small.
      apply H1. }
    { apply <- Nat.eqb_neq.
      replace (n * m + k mod m + 1 + i)%nat with (n * m + (k mod m + 1 + i))%nat by lia.
      rewrite Nat.Div0.add_mod.
      rewrite Nat.Div0.mul_mod.
      rewrite Nat.Div0.mod_same.
      rewrite Nat.mul_0_r.
      rewrite Nat.Div0.mod_0_l.
      simpl.
      repeat rewrite H2.
      all: lia. }
    replace (S (n * m + k mod m + i)) with (n * m + k mod m + 1 + i)%nat by lia.
    rewrite H2.
    lca.
    all: lia.
Qed.

Lemma func_sum_mod: forall (n m k: nat) (f: nat -> C),
  m <> O ->
  func_sum (fun i => if i mod m =? k mod m then f i else 0) (n * m) =
  func_sum (fun i => f (i * m + k mod m)%nat) n.
Proof.
  intros.
  unfold func_sum.
  unfold func_sum2.
  repeat rewrite Nat.sub_0_r.
  induction n.
  - intros.
    reflexivity.
  - intros.
    simpl.
    rewrite <- IHn.
    specialize (func_sum2_split_mult n m)as Hs.
    unfold func_sum in Hs.
    unfold func_sum2 in Hs.
    repeat rewrite Nat.sub_0_r in Hs.
    rewrite Hs.
    ring_simplify.
    replace (m + n * m - n * m)%nat with m by lia.
    replace (
      func_sum_suppl (fun i : nat => if i mod m =? k mod m then f i else 0) (n * m) m
    ) with (f (n * m + k mod m)%nat).
    lca.
    specialize (func_sum2_split3 (n * m) (n * m + m) (n * m + k mod m) (fun i : nat => if i mod m =? k mod m then f i else 0))as Hs3.
    unfold func_sum in Hs3.
    unfold func_sum2 in Hs3.
    replace (n * m + m - n * m)%nat with m in Hs3 by lia.
    rewrite Hs3.
    replace (n * m + k mod m - n * m)%nat with (k mod m) by lia.
    replace (1 + (n * m + k mod m) - (n * m + k mod m))%nat with 1%nat by lia.
    replace (n * m + m - (1 + (n * m + k mod m)))%nat with (m - (k mod m) - 1)%nat by lia.
    rewrite func_sum_mod_suppl_l.
    rewrite func_sum_mod_suppl_m.
    rewrite func_sum_mod_suppl_r.
    lca.
    1-5: lia.
    specialize (Nat.mod_bound_pos k m) as Hbound.
    lia.
Qed.

Lemma func_sum_div_suppl_l: forall (n m k i: nat) (f: nat -> C),
  m <> O ->
  (k < n * m)%nat ->
  (i <= k / m * m)%nat ->
  func_sum2 (fun i : nat => if i / m =? k / m then f i else 0) 0 i = 0.
Proof.
  intros.
  unfold func_sum2.
  rewrite Nat.sub_0_r.
  induction i.
  - simpl.
    lca.
  - simpl.
    rewrite IHi by lia.
    assert (i < m * (k / m))%nat as Hdiv by lia.
    apply Nat.Div0.div_lt_upper_bound in Hdiv.
    replace (i / m =? k / m) with false.
    lca.
    symmetry.
    apply Nat.eqb_neq.
    all: lia.
Qed.

Lemma func_sum_div_suppl_m: forall (n m k i: nat) (f: nat -> C),
  m <> O ->
  (k < n * m)%nat ->
  (i <= m)%nat ->
  func_sum2 (fun i : nat => if i / m =? k / m then f i else 0) (k / m * m) (i + k / m * m) =
  func_sum2 (fun i : nat => f (k / m * m + i)%nat) 0 i.
Proof.
  intros.
  unfold func_sum2.
  rewrite Nat.sub_0_r.
  replace (i + k / m * m - k / m * m)%nat with i by lia.
  induction i.
  - reflexivity.
  - simpl.
    rewrite IHi.
    replace ((k / m * m + i) / m =? k / m) with true.
    reflexivity.
    symmetry.
    apply Nat.eqb_eq.
    rewrite Nat.div_add_l.
    replace (i / m)%nat with O.
    lia.
    symmetry.
    apply Nat.div_small.
    all :lia.
Qed.

Lemma func_sum_div_suppl_r: forall (n m k i: nat) (f: nat -> C),
  m <> O ->
  (k < n * m)%nat ->
  (i <= (n * m - (m + k / m * m)))%nat ->
  func_sum_suppl (fun i : nat => if i / m =? k / m then f i else 0) (m + k / m * m) i = 0.
Proof.
  intros.
  induction i.
  - reflexivity.
  - simpl.
    rewrite IHi by lia.
    replace ((m + k / m * m + i) / m =? k / m) with false.
    lca.
    symmetry.
    apply Nat.eqb_neq.
    replace (m + k / m * m + i)%nat with (k / m * m + (1 * m + i))%nat by lia.
    repeat rewrite Nat.div_add_l.
    all: lia.
Qed.

Lemma func_sum_div: forall (n m k: nat) (f: nat -> C),
  m <> O ->
  (k < n * m)%nat ->
  func_sum (fun i => if i / m =? k / m then f i else 0) (n * m) =
  func_sum (fun i => f ((k / m) * m + i)%nat) m.
Proof.
  intros.
  unfold func_sum.
  repeat rewrite Nat.sub_0_r.
  rewrite func_sum2_split with (a := O) (b := (k / m * m)%nat) (c := (n * m)%nat).
  rewrite func_sum2_split with (a := (k / m * m)%nat) (b := (m + k / m * m)%nat).
  rewrite func_sum_div_suppl_l with (n := n).
  rewrite func_sum_div_suppl_m with (n := n).
  unfold func_sum2.
  rewrite func_sum_div_suppl_r with (n := n).
  lca.
  1-9: lia.
  split.
  lia.
  all: replace (n * m)%nat with (m * n)%nat in H0 by lia;
  apply Nat.Div0.div_lt_upper_bound in H0;
  nia.
Qed.

Lemma func_sum_dist_suppl: forall (n1 n2 i: nat) (f1 f2: nat -> C),
  n2 <> O ->
  (i <= n2)%nat ->
  func_sum_suppl (fun i : nat => f1 (i / n2)%nat * f2 (i mod n2)) (n1 * n2) i =
  func_sum_suppl f2 0 i * f1 n1.
Proof.
  intros.
  induction i as [|i].
  - lca.
  - simpl.
    rewrite IHi.
    rewrite Nat.div_add_l.
    rewrite Nat.Div0.add_mod.
    rewrite Nat.Div0.mul_mod.
    rewrite Nat.Div0.mod_same.
    rewrite Nat.div_small.
    rewrite Nat.mul_0_r.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_0_l.
    simpl.
    repeat rewrite Nat.mod_small.
    lca.
    all: lia.
Qed.

Lemma func_sum_dist: forall (n1 n2: nat) (f1 f2: nat -> C),
  n2 <> O ->
  func_sum (fun i => f1 (i / n2)%nat * f2 (i mod n2)) (n1 * n2) = func_sum f1 n1 * func_sum f2 n2.
Proof.
  intros.
  induction n1 as [|n1].
  - lca.
  - simpl.
    rewrite func_sum2_split_mult.
    rewrite IHn1.
    unfold func_sum, func_sum2.
    simpl.
    ring_simplify.
    replace (n2 + n1 * n2 - n1 * n2)%nat with n2 by lia.
    repeat rewrite Nat.sub_0_r.
    ring_simplify.
    rewrite func_sum_dist_suppl.
    lca.
    all: lia.
Qed.

Lemma func_sum_comm: forall (l: nat) (f: nat -> nat -> C),
  func_sum (fun i : nat => func_sum (fun j : nat => f i j) l) l =
  func_sum (fun i : nat => func_sum (fun j : nat => f j i) l) l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - unfold func_sum, func_sum2 in *.
    simpl in *.
    repeat rewrite Nat.sub_0_r in *.
    rewrite func_sum_suppl_add with
    (f12 := (fun i : nat => f i l + func_sum_suppl (fun j : nat => f i j) 0 l))
    (f1 := fun i => f i l)
    (f2 := (fun i : nat => func_sum_suppl (fun j : nat => f i j) 0 l)).
    rewrite func_sum_suppl_add with
    (f12 := (fun i : nat => f l i + func_sum_suppl (fun j : nat => f j i) 0 l))
    (f1 := fun i => f l i)
    (f2 := (fun i : nat => func_sum_suppl (fun j : nat => f j i) 0 l)).
    rewrite IHl.
    lca.
    intros. lca.
    intros. lca.
Qed.

Lemma func_sum_comm_mat: forall (l: nat) (f1 f2: nat -> nat -> C),
  func_sum (fun i : nat => func_sum (fun j : nat => f1 i j * f2 j i) l) l =
  func_sum (fun i : nat => func_sum (fun j : nat => f2 i j * f1 j i) l) l.
Proof.
  intros.
  specialize func_sum_comm with (f := fun i j => f1 i j * f2 j i) as Hcomm.
  replace (
    fun i : nat => func_sum (fun j : nat => f2 i j * f1 j i) l
  ) with (
    fun i : nat => func_sum (fun j : nat => f1 j i * f2 i j) l
  ).
  apply Hcomm.
  apply functional_extensionality.
  intros.
  replace (fun j : nat => f2 x j * f1 j x) with (fun j : nat => f1 j x * f2 x j).
  reflexivity.
  apply functional_extensionality.
  intros.
  lca.
Qed.

(* ============================================================================================== *)
