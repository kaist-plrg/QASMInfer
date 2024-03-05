Require Export Matrix.

(* A 2^n vector is a tree of height n, where each leaf is a complex number. *)
Inductive Vector : nat -> Type :=
  | bas_vec : Complex -> Vector 0
  | rec_vec : forall {n}, Vector n  -> Vector n -> Vector (S n).

Section SCHEMES.

(* An induction scheme for (non-base) vectors. *)
Definition vec_rectS (P: forall {n}, Vector (S n) -> Type)
  (bas: forall (v w: Vector 0), P (rec_vec v w))
  (rect: forall {n} (v w: Vector(S n)), P v -> P w -> P (rec_vec v w)) :=
  fix vec_rectS_fix {n} (v: Vector (S n)) : P v :=
    match v with
    | @rec_vec O v1 v2 =>
      match v1, v2 with
      | @bas_vec c1, @bas_vec c2 => bas v1 v2
      | _, _ => fun devil => False_ind (@IDProp) devil
      end
    | @rec_vec (S nn') v1 v2 =>
      rect v1 v2 (vec_rectS_fix v1) (vec_rectS_fix v2)
    | _ => fun devil => False_ind (@IDProp) devil
    end.

(* A vector of size 0 is a base vector *)
Definition vec_case0 (P: Vector 0 -> Type) (H: forall c, P (bas_vec c)) (v: Vector 0) : P v :=
  match v with
  | @bas_vec c => H c
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Definition vec_0_inv : forall v: Vector 0, exists c, v = bas_vec c :=
  fun v => vec_case0 (fun v => exists c, v = bas_vec c) (fun c => ex_intro _ c eq_refl) v.

(* A vector of size 1 is a recursive vector with two base vectors *)
Definition vec_caseS (P: forall {n}, Vector (S n) -> Type)
  (H: forall {n} (v w: Vector n), @P n (rec_vec v w))
  {n} (v: Vector (S n)) : P v :=
  match v with
  | @rec_vec n v1 v2 => H v1 v2
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Definition vec_S_inv : forall {n} (v: Vector (S n)), exists v1 v2, v = rec_vec v1 v2 :=
  fun n v => vec_caseS (fun n v => exists v1 v2, v = rec_vec v1 v2)
    (fun n v1 v2 => ex_intro _ v1 (ex_intro _ v2 eq_refl)) v.

Definition vec_caseS_ {n: nat} (v: Vector (S n))
: forall (P: Vector (S n) -> Type) (H: forall v1 v2, P (rec_vec v1 v2)), P v :=
  match v with
  | @rec_vec n v1 v2 => fun P H => H v1 v2
  | _ => fun devil => False_ind (@IDProp) devil
  end.

(* An induction scheme for 2 vectors of same size *)
Definition vec_rect2 (P: forall {n}, Vector n -> Vector n -> Type)
  (bas: forall a b, P (bas_vec a) (bas_vec b))
  (rect: forall {n v1 v2 w1 w2}, P v1 w1 -> P v2 w2 -> P (rec_vec v1 v2) (rec_vec w1 w2)) :=
  fix vec_rect2_fix {n} (v: Vector n) : forall w: Vector n, P v w :=
    match v with
    | @bas_vec a => fun w => vec_case0 (fun w => P (bas_vec a) w) (bas a) w
    | @rec_vec _ v1 v2 => fun w =>
      vec_caseS_ w (fun w' => P (rec_vec v1 v2) w')
        (fun w1 w2 => rect (vec_rect2_fix v1 w1) (vec_rect2_fix v2 w2))
    end.

Definition vec_rect2_gen (P: forall {n}, Vector n -> Vector n -> Type)
  (bas: forall a b, P (bas_vec a) (bas_vec b))
  (rect: forall {n v1 v2 w1 w2}, P v1 w1 -> P v1 w2 -> P v2 w1 -> P v2 w2 -> P (rec_vec v1 v2) (rec_vec w1 w2)) :=
  fix vec_rect2_gen_fix {n} (v: Vector n) : forall w: Vector n, P v w :=
    match v with
    | @bas_vec a => fun w => vec_case0 (fun w => P (bas_vec a) w) (bas a) w
    | @rec_vec _ v1 v2 => fun w =>
      vec_caseS_ w (fun w' => P (rec_vec v1 v2) w')
        (fun w1 w2 => rect (vec_rect2_gen_fix v1 w1) (vec_rect2_gen_fix v1 w2) (vec_rect2_gen_fix v2 w1) (vec_rect2_gen_fix v2 w2))
    end.

Definition mat_vec_rect2 (P: forall {n}, Matrix n -> Vector n -> Type)
  (bas: forall a b, P (bas_mat a) (bas_vec b))
  (rect: forall {n A1 A2 A3 A4 v1 v2},
    P A1 v1 -> P A1 v2 ->
    P A2 v1 -> P A2 v2 ->
    P A3 v1 -> P A3 v2 ->
    P A4 v1 -> P A4 v2 ->
    P (rec_mat A1 A2 A3 A4) (rec_vec v1 v2)) :=
  fix mat_vec_rect2_fix {n} (A: Matrix n) : forall v: Vector n, P A v :=
    match A with
    | bas_mat a => fun v => vec_case0 (fun v => P (bas_mat a) v) (bas a) v
    | rec_mat A1 A2 A3 A4 => fun v =>
      vec_caseS_ v (fun v' => P (rec_mat A1 A2 A3 A4) v')
        (fun v1 v2 => rect
          (mat_vec_rect2_fix A1 v1) (mat_vec_rect2_fix A1 v2)
          (mat_vec_rect2_fix A2 v1) (mat_vec_rect2_fix A2 v2)
          (mat_vec_rect2_fix A3 v1) (mat_vec_rect2_fix A3 v2)
          (mat_vec_rect2_fix A4 v1) (mat_vec_rect2_fix A4 v2))
    end.

Definition vec_mat_rect2 (P: forall {n}, Vector n -> Matrix n -> Type)
  (bas: forall a b, P (bas_vec a) (bas_mat b))
  (rect: forall {n v1 v2 A1 A2 A3 A4},
    P v1 A1 -> P v1 A2 -> P v1 A3 -> P v1 A4 ->
    P v2 A1 -> P v2 A2 -> P v2 A3 -> P v2 A4 ->
    P (rec_vec v1 v2) (rec_mat A1 A2 A3 A4)) :=
  fix vec_mat_rect2_fix {n} (v: Vector n) : forall A: Matrix n, P v A :=
    match v with
    | bas_vec a => fun A => mat_case0 (fun A => P (bas_vec a) A) (bas a) A
    | rec_vec v1 v2 => fun A =>
      mat_caseS_ A (fun A' => P (rec_vec v1 v2) A')
        (fun A1 A2 A3 A4 => rect
          (vec_mat_rect2_fix v1 A1) (vec_mat_rect2_fix v1 A2)
          (vec_mat_rect2_fix v1 A3) (vec_mat_rect2_fix v1 A4)
          (vec_mat_rect2_fix v2 A1) (vec_mat_rect2_fix v2 A2)
          (vec_mat_rect2_fix v2 A3) (vec_mat_rect2_fix v2 A4))
    end.

End SCHEMES.

Section ITERATORS.

(* Uniform application on the elements of the vector *)
Definition vec_map (f: Complex -> Complex) : forall {n} (v: Vector n), Vector n :=
  fix vec_map_fix {n} (v: Vector n) : Vector n := match v with
    | bas_vec c => bas_vec (f c)
    | rec_vec v1 v2 => rec_vec (vec_map_fix v1) (vec_map_fix v2)
    end.

(* Element-wise application of a binary function on the elements of the vectors *)
Definition vec_map2 (g: Complex -> Complex -> Complex) : forall {n}, Vector n -> Vector n -> Vector n :=
  @vec_rect2 (fun n _ _ => Vector n) (fun a b => bas_vec (g a b))
    (fun n _ _ _ _ IH1 IH2 => rec_vec IH1 IH2).

End ITERATORS.


Section BASES.

(* Zero Vector *)
Fixpoint vec_zero {n} : Vector n.
Proof.
  destruct n.
  - exact (bas_vec 0).
  - exact (rec_vec (vec_zero n) (vec_zero n)).
Defined.

(* One Vector *)
Fixpoint vec_one {n} : Vector n.
Proof.
  destruct n.
  - exact (bas_vec 1).
  - exact (rec_vec (vec_one n) (vec_one n)).
Defined.

End BASES.


Section UOP.

(* Vector negation *)
Definition vec_neg {n} := @vec_map com_neg n.

(* Vector scalar multiplication *)
Definition vec_scale {n} (a: Complex) := @vec_map (fun b => a * b) n.

(* Vector conjugate transpose *)
Definition vec_conjtrans {n} (v: Vector n) : Vector n.
Proof.
  induction v.
  - exact (bas_vec (com_conj c)).
  - exact (rec_vec IHv1 IHv2).
Defined.

End UOP.


Section BOP.

(* Vector addition *)
Definition vec_add {n} := @vec_map2 com_add n.

(* Vector subtraction *)
Definition vec_sub {n} := @vec_map2 com_sub n.

(* Vector element-wise multiplication *)
Definition vec_mul_elem {n} := @vec_map2 com_mul n.

(* Vector dot product *)
Definition vec_dot: forall {n}, Vector n -> Vector n -> Complex :=
  @vec_rect2 (fun n _ _ => Complex) com_mul (fun n _ _ _ _ IH1 IH2 => IH1 + IH2).

Definition vec_outer: forall {n}, Vector n -> Vector n -> Matrix n :=
  @vec_rect2_gen (fun n _ _ => Matrix n) (fun a b => bas_mat (a * b))
    (fun n _ _ _ _ IH11 IH12 IH21 IH22 => rec_mat IH11 IH12 IH21 IH22).

(* Matrix vector multiplication: Treat V as column vector *)
Definition mat_vec_mul: forall {n}, Matrix n -> Vector n -> Vector n :=
  @mat_vec_rect2 (fun n _ _ => Vector n)
    (fun a b => bas_vec (a * b))
    (fun n A1 A2 A3 A4 v1 v2 IH11 _ _ IH22 IH31 _ _ IH42 =>
      rec_vec (vec_add IH11 IH22) (vec_add IH31 IH42)).

(* Vector matrix multiplication: Treat V as row vector *)
Definition vec_mat_mul: forall {n}, Vector n -> Matrix n -> Vector n :=
  @vec_mat_rect2 (fun n _ _ => Vector n)
    (fun a b => bas_vec (a * b))
    (fun n v1 v2 A1 A2 A3 A4 IH11 IH12 IH13 IH14 IH21 IH22 IH23 IH24 =>
      rec_vec (vec_add IH11 IH23) (vec_add IH12 IH24)).

End BOP.

(* | means vector *)
Notation "-| v" := (vec_neg v) (at level 40) : Matrix_scope.
Notation "v |†" := (vec_conjtrans v) (at level 30) : Matrix_scope.
Infix ".*|" := vec_scale (at level 35) : Matrix_scope.
Infix "*|" := mat_vec_mul (at level 40) : Matrix_scope.
Infix "|*" := vec_mat_mul (at level 40) : Matrix_scope.
Infix "|*|" := vec_dot (at level 40) : Matrix_scope.
Infix "|✕|" := vec_outer (at level 40) : Matrix_scope.
Infix "|+|" := vec_add (at level 50) : Matrix_scope.


Section PROPERTIES.

Open Scope Matrix_scope.
Delimit Scope Matrix_scope with mat.

(* Vector addition is commutative *)
Lemma vec_add_comm: forall {n} (v w: Vector n), v |+| w = w |+| v.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c1]; subst.
    specialize (vec_0_inv w) as [c2]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

Hint Extern 1 => (rewrite vec_add_comm) : comm_db.

(* Vector addition is associative *)
Lemma vec_add_assoc: forall {n} (v w u: Vector n), v |+| (w |+| u) = (v |+| w) |+| u.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c1]; subst.
    specialize (vec_0_inv w) as [c2]; subst.
    specialize (vec_0_inv u) as [c3]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    specialize (vec_S_inv u) as [u1 [u2 ?]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

Hint Extern 1 => (rewrite vec_add_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- vec_add_assoc) : assoc_db.

(* Vector addition has identity element *)

Lemma vec_add_0_l: forall {n} (v: Vector n), vec_zero |+| v = v.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

Lemma vec_add_0_r: forall {n} (v: Vector n), v |+| vec_zero = v.
Proof.
  intros.
  rewrite vec_add_comm.
  apply vec_add_0_l.
Qed.

(* Vector negation is the inverse of vector addition *)
Lemma vec_add_inv: forall {n} (v: Vector n), -| v |+| v = vec_zero.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

(* Vector scale over addition *)
Lemma vec_scale_dist_l: forall {n} (a: Complex) (v w: Vector n), a .*| (v |+| w) = (a .*| v) |+| (a .*| w).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c1]; subst.
    specialize (vec_0_inv w) as [c2]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    simpl; f_equal; auto.
Qed.

Lemma vec_scale_dist_r: forall {n} (a b: Complex) (v: Vector n), (a + b) .*| v = (a .*| v) |+| (b .*| v).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl; f_equal; auto.
Qed.

(* Inner product is commutative *)
Lemma vec_dot_comm: forall {n} (v w: Vector n), v |*| w = w |*| v.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c1]; subst.
    specialize (vec_0_inv w) as [c2]; subst.
    simpl.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    simpl.
    rewrite IHn.
    f_equal.
    apply IHn.
Qed.

Hint Extern 1 => (rewrite vec_dot_comm) : comm_db.

(* Inner product over addition *)
Lemma vec_dot_dist_l: forall {n} (v w u: Vector n), v |*| (w |+| u) = (v |*| w + v |*| u)%com.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c1]; subst.
    specialize (vec_0_inv w) as [c2]; subst.
    specialize (vec_0_inv u) as [c3]; subst.
    simpl.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    specialize (vec_S_inv u) as [u1 [u2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    lca.
Qed.

Lemma vec_dot_dist_r: forall {n} (v w u: Vector n), (v |+| w) |*| u = (v |*| u + w |*| u)%com.
Proof.
  intros.
  rewrite vec_dot_comm.
  rewrite (vec_dot_comm v u).
  rewrite (vec_dot_comm w u).
  apply vec_dot_dist_l.
Qed.

Lemma vec_dot_0_l: forall {n} (v: Vector n), vec_zero |*| v = 0.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    lca.
Qed.

Lemma vec_dot_0_r: forall {n} (v: Vector n), v |*| vec_zero = 0.
Proof.
  intros.
  rewrite vec_dot_comm.
  apply vec_dot_0_l.
Qed.

Lemma vec_vec_scale_dot_assoc: forall {n} (c: Complex) (v w: Vector n),
  c .*| v |*| w = (c * (v |*| w))%com.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c1]; subst.
    specialize (vec_0_inv w) as [c2]; subst.
    simpl; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    lca.
Qed.

Hint Extern 1 => (rewrite vec_vec_scale_dot_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- vec_vec_scale_dot_assoc) : assoc_db.

Lemma vec_dot_conj: forall {n} (v w: Vector n), com_conj (v |*| w) = (w|† |*| v|†).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (vec_0_inv w) as [d]; subst.
    simpl; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    simpl.
    rewrite com_conj_add.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma vec_dot_conjtrans_ge0 {n} (v: Vector n) : (v|† |*| v) >= 0.
Proof.
  intros.
  induction v.
  - simpl.
    apply com_conj_mul_ge0_l.
  - simpl.
    apply com_ge0_add; auto.
Qed.

Lemma vec_add_conjtrans: forall {n} (v w: Vector n), (v |+| w)|† = v|† |+| w|†.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (vec_0_inv w) as [d]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma vec_conjtrans_involutive: forall {n} (v: Vector n), v |† |† = v.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

Lemma vec_conjtrans_0: forall {n}, (@vec_zero n)|† = vec_zero.
Proof.
  intros.
  induction n.
  - simpl; f_equal; lca.
  - simpl; f_equal; auto.
Qed.

End PROPERTIES.


Section VECTORRING.

Open Scope Matrix_scope.

Definition vec_ring n: Ring_theory.ring_theory (@vec_zero n) vec_one vec_add vec_mul_elem vec_sub vec_neg eq.
Proof.
  constructor.
  - apply vec_add_0_l.
  - apply vec_add_comm.
  - apply vec_add_assoc.
  - intros.
    induction n.
    + specialize (vec_0_inv x) as [c]; subst.
      simpl; f_equal.
      lca.
    + specialize (vec_S_inv x) as [x1 [x2 ?]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - intros.
    induction n.
    + specialize (vec_0_inv x) as [c1]; subst.
      specialize (vec_0_inv y) as [c2]; subst.
      simpl; f_equal.
      lca.
    + specialize (vec_S_inv x) as [x1 [x2 ?]]; subst.
      specialize (vec_S_inv y) as [y1 [y2 ?]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - intros.
    induction n.
    + specialize (vec_0_inv x) as [c1]; subst.
      specialize (vec_0_inv y) as [c2]; subst.
      specialize (vec_0_inv z) as [c3]; subst.
      simpl; f_equal.
      lca.
    + specialize (vec_S_inv x) as [x1 [x2 ?]]; subst.
      specialize (vec_S_inv y) as [y1 [y2 ?]]; subst.
      specialize (vec_S_inv z) as [z1 [z2 ?]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - intros.
    induction n.
    + specialize (vec_0_inv x) as [c1]; subst.
      specialize (vec_0_inv y) as [c2]; subst.
      specialize (vec_0_inv z) as [c3]; subst.
      simpl; f_equal.
      lca.
    + specialize (vec_S_inv x) as [x1 [x2 ?]]; subst.
      specialize (vec_S_inv y) as [y1 [y2 ?]]; subst.
      specialize (vec_S_inv z) as [z1 [z2 ?]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - intros.
    induction n.
    + specialize (vec_0_inv x) as [c1]; subst.
      specialize (vec_0_inv y) as [c2]; subst.
      simpl; f_equal.
    + specialize (vec_S_inv x) as [x1 [x2 ?]]; subst.
      specialize (vec_S_inv y) as [y1 [y2 ?]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - intros.
    induction n.
    + specialize (vec_0_inv x) as [c1]; subst.
      simpl; f_equal.
      lca.
    + specialize (vec_S_inv x) as [x1 [x2 ?]]; subst.
      simpl; f_equal.
      all: apply IHn.
Qed.

End VECTORRING.
