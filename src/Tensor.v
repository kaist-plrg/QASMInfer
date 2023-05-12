Require Export Matrix.
Import ListNotations.

Declare Scope T_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.


(* tensor product =============================================================================== *)

Definition Tproduct_inner (m1 m2: Matrix_inner):
  {m: Matrix_inner | rows m = (rows m1 * rows m2)%nat /\ cols m = (cols m1 * cols m2)%nat}.
Proof.
  refine ( exist _ {|
      rows := rows m1 * rows m2;
      cols := cols m1 * cols m2;
      inner := fun i j => Cmult (
        inner m1 (i / rows m2) (j / cols m2)
      ) (
        inner m2 (i mod rows m2) (j mod cols m2)
      )
    |} _ ).
  simpl. split. reflexivity. reflexivity.
Defined.

Definition Tproduct (m1 m2: Matrix):
  {m: Matrix | m.rows = (m1.rows * m2.rows)%nat /\ m.cols = (m1.cols * m2.cols)%nat}.
Proof.
  destruct (Tproduct_inner (inner_mat m1) (inner_mat m2)) as [m Hm].
  inversion Hm.
  refine( exist _ {|inner_mat := m|} _ ).
  Unshelve.
  - simpl. apply Hm.
  - assert (m1.rows > 0) by apply rows_pos.
    assert (m2.rows > 0) by apply rows_pos.
    lia.
  - assert (m1.cols > 0) by apply cols_pos.
    assert (m2.cols > 0) by apply cols_pos.
    lia.
Defined.

Property Tproduct_correct: forall
  (m1 m2 mt: Matrix) (i j: nat) (Ht: _) (Hi: _) (Hj: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ mt Ht = Tproduct m1 m2 ->
  mt[[i Hi|j Hj]] =
  m1[[(i / m2.rows) H1i|(j / m2.cols) H1j]] * m2[[(i mod m2.rows) H2i|(j mod m2.cols) H2j]].
Proof.
  unfold Mget. simpl.
  unfold Tproduct. simpl.
  unfold Tproduct_inner. simpl.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* distributive property of tensor product ====================================================== *)

(* Fact Tproduct_dist_suppl: forall (m1c m2r m3r m3c m4r m4c i j: nat) (f1 f2 f3 f4: nat -> nat -> C),
  m1c = m2r -> m3c = m4r ->
  dot_product_inner
    {| rows := 1; cols := m1c; inner := fun i' j' : nat => f1 (i / m3r + i')%nat j' |}
    {| rows := m2r; cols := 1; inner := fun i' j' : nat => f2 i' (j / m4c + j')%nat |} m1c *
  dot_product_inner
    {| rows := 1; cols := m3c; inner := fun i' j' : nat => f3 (i mod m3r + i')%nat j' |}
    {| rows := m4r; cols := 1; inner := fun i' j' : nat => f4 i' (j mod m4c + j')%nat |} m3c =
  dot_product_inner
    {| rows := 1; cols := m1c * m3c; inner := fun i' j' : nat =>
        f1 ((i + i') / m3r)%nat (j' / m3c)%nat *
        f3 ((i + i') mod m3r)%nat (j' mod m3c)%nat |}
    {| rows := m2r * m4r; cols := 1; inner := fun i' j' : nat =>
        f2 (i' / m4r)%nat ((j + j') / m4c)%nat *
        f4 (i' mod m4r)%nat ((j + j') mod m4c)%nat |} (m1c * m3c).
Proof.
  induction m1c as [|m1c'].
  - simpl.
    intros.
    lca.
  - simpl.
    induction m3c as [|m3c'].
    + simpl.
      intros.
      repeat rewrite Cmult_0_r.
      repeat rewrite Nat.mul_0_r.
      reflexivity.
    + intros.
      subst m2r m4r.
      simpl.
      specialize (IHm3c' m3c' m4c i j f1 f2 f3 f4).
      simpl in IHm3c'.
      repeat rewrite Nat.add_0_r.
      apply IHm3c'. *)

(* Fact Tproduct_dist_suppl: forall (m1c m3r m3c m4r m4c i j: nat) (f1 f2 f3 f4: nat -> nat -> C),
  m3c = m4r ->
  dot_product_inner (fun i' j' : nat => f1 (i / m3r + i')%nat j')
    (fun i' j' : nat => f2 i' (j / m4c + j')%nat) m1c *
  dot_product_inner (fun i' j' : nat => f3 (i mod m3r + i')%nat j')
    (fun i' j' : nat => f4 i' (j mod m4c + j')%nat) m3c =
  dot_product_inner
    (fun i' j' : nat =>
    f1 ((i + i') / m3r)%nat (j' / m3c)%nat *
    f3 ((i + i') mod m3r) (j' mod m3c))
    (fun i' j' : nat =>
    f2 (i' / m4r)%nat ((j + j') / m4c)%nat *
    f4 (i' mod m4r) ((j + j') mod m4c)) (m1c * m3c).
Proof.
  intros.
  subst m4r.
  revert m3c.
  induction m1c as [|m1c'].
  - simpl.
    intros.
    lca.
  - induction m3c as [|m3c'].
    + simpl.
      intros.
      repeat rewrite Cmult_0_r.
      repeat rewrite Nat.mul_0_r.
      reflexivity.
    + intros.
      simpl_left.
      rewrite Cmult_Cplus_dist.
      rewrite IHm1c'.
      simpl.
      repeat rewrite Nat.add_0_r.
      Nat.divmod


      hide_right.
      simpl.
      skubst m4r.

      specialize (IHm3c' m4r m4c i j f1 f2 f3 f4)
      subst m4r. *)

(* m1 ** m2 * I ** m3 = m1 ** (m2 * m3) 를 증명하자. *)

Lemma Tproduct_dist: forall
  (m1 m2 m3: Matrix) (i j: nat) (H12: _) (H34: _) (H1234: _) (Hi1: _) (Hj1: _) (Hi2: _) (Hj2: _),
  (Tproduct (Mmult m1 m2 H12).1 m3).1[[i Hi1|j Hj1]]
  = (Mmult (Tproduct m1 m3).1 (Tproduct m2 m4).1 H1234).1[[i Hi2|j Hj2]].
Proof.
  intros.
  unfold Mget. simpl.
  unfold Mmult_inner. simpl.
  induction (m1.cols) as [|m1cols'].
  unfold dot_product_inner. simpl.

(* ============================================================================================== *)

(* Definition trace, partial trace *)