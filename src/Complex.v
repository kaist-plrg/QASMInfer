Require Export Util.
Require Export Reals.


Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Bind Scope R_scope with R.
Open Scope util_scope.
Declare Scope C_scope.
Bind Scope C_scope with C.

Definition C := (R * R)%type.

Definition RTC (x: R): C := (x, 0).
Definition NTC (n: nat): C := (INR n, 0).

Coercion RTC : R >-> C.
Coercion NTC : nat >-> C.

Definition Cplus (x y : C) : C := (fst x + fst y, snd x + snd y).
Definition Copp (x : C) : C := (-fst x, -snd x).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition Cinv (x : C) : C := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).

(* Added exponentiation *)
Fixpoint Cpow (c : C) (n : nat) : C :=
  match n with
  | 0%nat => 1
  | S n' => Cmult c (Cpow c n')
  end.


Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.
Infix "^" := Cpow : C_scope.

Definition Re (z : C) : R := fst z.

Definition Im (z : C) : R := snd z.

Definition Cmod (x : C) : R := sqrt (fst x ^ 2 + snd x ^ 2).

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).


Lemma RTC_inj: forall (x y: R),
  RTC x = RTC y -> x = y.
Proof.
  intros x y H.
  now apply (f_equal fst) in H.
Qed.


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
