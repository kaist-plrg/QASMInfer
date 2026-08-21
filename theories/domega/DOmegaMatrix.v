Require Import QASMInfer.domega.DOmega.
Require Import QASMInfer.matrix.All.

From Stdlib Require Import Bool.
From Stdlib Require Import Program.Equality.

Open Scope Complex_scope.
Open Scope Matrix_scope.

Section DOMEGA_MATRIX.

Inductive DOmegaMatrix : nat -> Type :=
| domega_bas_mat : DOmega -> DOmegaMatrix O
| domega_rec_mat :
    forall {n : nat},
      DOmegaMatrix n ->
      DOmegaMatrix n ->
      DOmegaMatrix n ->
      DOmegaMatrix n ->
      DOmegaMatrix (S n).

Arguments domega_rec_mat {n} _ _ _ _.

Definition domega_matrix_case0
    (P : DOmegaMatrix 0 -> Type)
    (H : forall a, P (domega_bas_mat a))
    (A : DOmegaMatrix 0) : P A :=
  match A with
  | domega_bas_mat a => H a
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Definition domega_matrix_caseS_ {n : nat} (A : DOmegaMatrix (S n))
    : forall
        (P : DOmegaMatrix (S n) -> Type)
        (H : forall A00 A01 A10 A11,
          P (domega_rec_mat A00 A01 A10 A11)),
        P A :=
  match A with
  | domega_rec_mat A00 A01 A10 A11 =>
      fun P H => H A00 A01 A10 A11
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Fixpoint complex_of_domega_matrix {n : nat} (x : DOmegaMatrix n)
    : Matrix n :=
  match x with
  | domega_bas_mat a => bas_mat (complex_of_domega a)
  | domega_rec_mat a b c d =>
      rec_mat
        (complex_of_domega_matrix a)
        (complex_of_domega_matrix b)
        (complex_of_domega_matrix c)
        (complex_of_domega_matrix d)
  end.

Fixpoint domega_matrix_zero {n : nat} : DOmegaMatrix n :=
  match n with
  | O => domega_bas_mat domega_zero
  | S n' =>
      domega_rec_mat
        (@domega_matrix_zero n')
        (@domega_matrix_zero n')
        (@domega_matrix_zero n')
        (@domega_matrix_zero n')
  end.

Fixpoint domega_matrix_eye {n : nat} : DOmegaMatrix n :=
  match n with
  | O => domega_bas_mat domega_one
  | S n' =>
      domega_rec_mat
        (@domega_matrix_eye n')
        (@domega_matrix_zero n')
        (@domega_matrix_zero n')
        (@domega_matrix_eye n')
  end.

Fixpoint domega_matrix_map {n : nat} (f : DOmega -> DOmega)
    (x : DOmegaMatrix n) : DOmegaMatrix n :=
  match x with
  | domega_bas_mat a => domega_bas_mat (f a)
  | domega_rec_mat a b c d =>
      domega_rec_mat
        (domega_matrix_map f a)
        (domega_matrix_map f b)
        (domega_matrix_map f c)
        (domega_matrix_map f d)
  end.

Fixpoint domega_matrix_map2 {n : nat} (f : DOmega -> DOmega -> DOmega)
    (x : DOmegaMatrix n) : DOmegaMatrix n -> DOmegaMatrix n :=
  match x with
  | domega_bas_mat a =>
      fun y =>
        domega_matrix_case0
          (fun _ => DOmegaMatrix 0)
          (fun b => domega_bas_mat (f a b))
          y
  | @domega_rec_mat n a b c d =>
      fun y =>
        domega_matrix_caseS_
          y
          (fun _ => DOmegaMatrix (S n))
          (fun e f' g h =>
            domega_rec_mat
              (domega_matrix_map2 f a e)
              (domega_matrix_map2 f b f')
              (domega_matrix_map2 f c g)
              (domega_matrix_map2 f d h))
  end.

Definition domega_matrix_add {n : nat}
    (x y : DOmegaMatrix n) : DOmegaMatrix n :=
  domega_matrix_map2 domega_add x y.

Definition domega_matrix_neg {n : nat}
    (x : DOmegaMatrix n) : DOmegaMatrix n :=
  domega_matrix_map domega_neg x.

Definition domega_matrix_sub {n : nat}
    (x y : DOmegaMatrix n) : DOmegaMatrix n :=
  domega_matrix_map2 domega_sub x y.

Definition domega_matrix_scale {n : nat}
    (scalar : DOmega) (x : DOmegaMatrix n) : DOmegaMatrix n :=
  domega_matrix_map (domega_mul scalar) x.

Fixpoint domega_matrix_mul {n : nat} (x : DOmegaMatrix n)
    : DOmegaMatrix n -> DOmegaMatrix n :=
  match x with
  | domega_bas_mat a =>
      fun y =>
        domega_matrix_case0
          (fun _ => DOmegaMatrix 0)
          (fun b => domega_bas_mat (domega_mul a b))
          y
  | @domega_rec_mat n a b c d =>
      fun y =>
        domega_matrix_caseS_
          y
          (fun _ => DOmegaMatrix (S n))
          (fun e f g h =>
            domega_rec_mat
              (domega_matrix_add
                 (domega_matrix_mul a e)
                 (domega_matrix_mul b g))
              (domega_matrix_add
                 (domega_matrix_mul a f)
                 (domega_matrix_mul b h))
              (domega_matrix_add
                 (domega_matrix_mul c e)
                 (domega_matrix_mul d g))
              (domega_matrix_add
                 (domega_matrix_mul c f)
                 (domega_matrix_mul d h)))
  end.

Fixpoint domega_matrix_eqb {n : nat} (x : DOmegaMatrix n)
    : DOmegaMatrix n -> bool :=
  match x with
  | domega_bas_mat a =>
      fun y =>
        domega_matrix_case0
          (fun _ => bool)
          (fun b => domega_eqb a b)
          y
  | @domega_rec_mat n a b c d =>
      fun y =>
        domega_matrix_caseS_
          y
          (fun _ => bool)
          (fun e f g h =>
            domega_matrix_eqb a e
            && domega_matrix_eqb b f
            && domega_matrix_eqb c g
            && domega_matrix_eqb d h)
  end.

Lemma domega_matrix_eqb_sound :
  forall {n : nat} (x y : DOmegaMatrix n),
    domega_matrix_eqb x y = true ->
    complex_of_domega_matrix x = complex_of_domega_matrix y.
Proof.
  induction x as [a | n a IHa b IHb c IHc d IHd]; intros y H.
  - dependent destruction y.
    simpl in *.
    f_equal.
    apply domega_eqb_sound in H.
    exact H.
  - dependent destruction y.
    cbn [domega_matrix_eqb domega_matrix_caseS_] in H.
    repeat rewrite Bool.andb_true_iff in H.
    destruct H as [[[Hae Hbf] Hcg] Hdh].
    simpl.
    f_equal.
    + apply IHa. exact Hae.
    + apply IHb. exact Hbf.
    + apply IHc. exact Hcg.
    + apply IHd. exact Hdh.
Qed.

Lemma complex_of_domega_matrix_zero :
  forall n,
    complex_of_domega_matrix (@domega_matrix_zero n) = @mat_0 n.
Proof.
  induction n as [| n IH].
  - simpl.
    rewrite complex_of_domega_zero.
    reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma complex_of_domega_matrix_eye :
  forall n,
    complex_of_domega_matrix (@domega_matrix_eye n) = @mat_eye n.
Proof.
  induction n as [| n IH].
  - simpl.
    rewrite complex_of_domega_one.
    reflexivity.
  - simpl.
    rewrite IH.
    rewrite complex_of_domega_matrix_zero.
    reflexivity.
Qed.

Lemma complex_of_domega_matrix_add :
  forall {n : nat} (x y : DOmegaMatrix n),
    complex_of_domega_matrix (domega_matrix_add x y) =
    mat_add (complex_of_domega_matrix x) (complex_of_domega_matrix y).
Proof.
  induction x as [a | n a IHa b IHb c IHc d IHd]; intros y.
  - dependent destruction y.
    cbn [domega_matrix_add domega_matrix_map2 domega_matrix_case0
      complex_of_domega_matrix mat_add mat_map2].
    rewrite complex_of_domega_add.
    reflexivity.
  - dependent destruction y.
    cbn [domega_matrix_add domega_matrix_map2 domega_matrix_caseS_
      complex_of_domega_matrix mat_add mat_map2].
    repeat match goal with
    | |- context[domega_matrix_map2 domega_add ?x ?y] =>
        change (domega_matrix_map2 domega_add x y) with (domega_matrix_add x y)
    end.
    rewrite IHa, IHb, IHc, IHd.
    reflexivity.
Qed.

Lemma complex_of_domega_matrix_neg :
  forall {n : nat} (x : DOmegaMatrix n),
    complex_of_domega_matrix (domega_matrix_neg x) =
    mat_neg (complex_of_domega_matrix x).
Proof.
  induction x as [a | n a IHa b IHb c IHc d IHd].
  - simpl.
    rewrite complex_of_domega_neg.
    reflexivity.
  - cbn [domega_matrix_neg domega_matrix_map complex_of_domega_matrix
      mat_neg mat_map].
    repeat match goal with
    | |- context[domega_matrix_map domega_neg ?x] =>
        change (domega_matrix_map domega_neg x) with (domega_matrix_neg x)
    end.
    rewrite IHa, IHb, IHc, IHd.
    reflexivity.
Qed.

Lemma complex_of_domega_matrix_sub :
  forall {n : nat} (x y : DOmegaMatrix n),
    complex_of_domega_matrix (domega_matrix_sub x y) =
    mat_sub (complex_of_domega_matrix x) (complex_of_domega_matrix y).
Proof.
  induction x as [a | n a IHa b IHb c IHc d IHd]; intros y.
  - dependent destruction y.
    cbn [domega_matrix_sub domega_matrix_map2 domega_matrix_case0
      complex_of_domega_matrix mat_sub mat_map2].
    rewrite complex_of_domega_sub.
    reflexivity.
  - dependent destruction y.
    cbn [domega_matrix_sub domega_matrix_map2 domega_matrix_caseS_
      complex_of_domega_matrix mat_sub mat_map2].
    repeat match goal with
    | |- context[domega_matrix_map2 domega_sub ?x ?y] =>
        change (domega_matrix_map2 domega_sub x y) with (domega_matrix_sub x y)
    end.
    rewrite IHa, IHb, IHc, IHd.
    reflexivity.
Qed.

Lemma complex_of_domega_matrix_scale :
  forall {n : nat} scalar (x : DOmegaMatrix n),
    complex_of_domega_matrix (domega_matrix_scale scalar x) =
    mat_scale (complex_of_domega scalar) (complex_of_domega_matrix x).
Proof.
  intros n scalar x.
  induction x as [a | n a IHa b IHb c IHc d IHd].
  - simpl.
    rewrite complex_of_domega_mul.
    reflexivity.
  - cbn [domega_matrix_scale domega_matrix_map complex_of_domega_matrix
      mat_scale mat_map].
    repeat match goal with
    | |- context[domega_matrix_map (domega_mul scalar) ?x] =>
        change (domega_matrix_map (domega_mul scalar) x)
          with (domega_matrix_scale scalar x)
    end.
    rewrite IHa, IHb, IHc, IHd.
    reflexivity.
Qed.

Lemma complex_of_domega_matrix_mul :
  forall {n : nat} (x y : DOmegaMatrix n),
    complex_of_domega_matrix (domega_matrix_mul x y) =
    mat_mul (complex_of_domega_matrix x) (complex_of_domega_matrix y).
Proof.
  induction x as [a | n a IHa b IHb c IHc d IHd]; intros y.
  - dependent destruction y.
    cbn [domega_matrix_mul domega_matrix_case0 complex_of_domega_matrix
      mat_mul mat_rect2_gen mat_case0].
    rewrite complex_of_domega_mul.
    reflexivity.
  - dependent destruction y.
    cbn [domega_matrix_mul domega_matrix_caseS_ complex_of_domega_matrix
      mat_mul mat_rect2_gen mat_caseS_ mat_add].
    repeat rewrite complex_of_domega_matrix_add.
    rewrite (IHa y1), (IHb y3), (IHa y2), (IHb y4).
    rewrite (IHc y1), (IHd y3), (IHc y2), (IHd y4).
    reflexivity.
Qed.

End DOMEGA_MATRIX.
