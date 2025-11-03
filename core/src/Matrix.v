Require Export Complex.
Import ListNotations.

Declare Scope Matrix_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Complex_scope.
Bind Scope Complex_scope with Complex.
From Stdlib Require Import Program.Equality.

(* A 2^n * 2^n matrix is a tree of height n, where each leaf is a complex number. *)
Inductive Matrix : nat -> Type :=
  | bas_mat : Complex -> Matrix O
  | rec_mat : forall {n: nat}, Matrix n -> Matrix n -> Matrix n -> Matrix n -> Matrix (S n).
  (* rec_mat A B C D = [A | B \ C | D] *)

Section SCHEMES.

(* An induction scheme for (non-base) matrices. *)
Definition mat_rectS (P: forall {n}, Matrix (S n) -> Type)
  (bas: forall (A B C D: Matrix 0), P (rec_mat A B C D))
  (rect: forall {n} (A B C D: Matrix (S n)), P A -> P B -> P C -> P D -> P (rec_mat A B C D)) :=
  fix mat_rectS_fix {n} (A: Matrix (S n)) : P A :=
    match A with
    | @rec_mat O A1 A2 A3 A4 =>
      match A1, A2, A3, A4 with
      | @bas_mat a, @bas_mat b, @bas_mat c, @bas_mat d => bas A1 A2 A3 A4
      | _, _, _, _ => fun devil => False_ind (@IDProp) devil
      end
    | @rec_mat (S nn') A1 A2 A3 A4 =>
      rect A1 A2 A3 A4 (mat_rectS_fix A1) (mat_rectS_fix A2) (mat_rectS_fix A3) (mat_rectS_fix A4)
    | _ => fun devil => False_ind (@IDProp) devil
    end.

(* A matrix of size 0 is a base matrix. *)
Definition mat_case0 (P: Matrix 0 -> Type) (H: forall c, P (bas_mat c)) (A: Matrix 0) : P A :=
  match A with
  | @bas_mat a => H a
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Definition mat_0_inv : forall A: Matrix 0, exists a, A = bas_mat a :=
  fun A => mat_case0 (fun A => exists a, A = bas_mat a) (fun a => ex_intro _ a eq_refl) A.

(* A matrix of size 1 or more is a recursive matrix. *)
Definition mat_caseS (P: forall {n}, Matrix (S n) -> Type)
  (H: forall {n} (A1 A2 A3 A4: Matrix n), @P n (rec_mat A1 A2 A3 A4))
  {n} (A: Matrix (S n)) : P A :=
  match A with
  | @rec_mat n A1 A2 A3 A4 => H A1 A2 A3 A4
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Definition mat_S_inv : forall {n} (A: Matrix (S n)), exists A1 A2 A3 A4, A = rec_mat A1 A2 A3 A4 :=
  fun n A => mat_caseS (fun n A => exists A1 A2 A3 A4, A = rec_mat A1 A2 A3 A4)
  (fun n A1 A2 A3 A4 => ex_intro _ A1 (ex_intro _ A2 (ex_intro _ A3 (ex_intro _ A4 eq_refl)))) A.

Definition mat_caseS_ {n: nat} (A: Matrix (S n))
: forall (P: Matrix (S n) -> Type) (H: forall A1 A2 A3 A4, P (rec_mat A1 A2 A3 A4)), P A :=
  match A with
  | @rec_mat n A1 A2 A3 A4 => fun P H => H A1 A2 A3 A4
  | _ => fun devil => False_ind (@IDProp) devil
  end.

(* An induction scheme for 2 matrices of same size *)
Definition mat_rect2 (P: forall {n}, Matrix n -> Matrix n -> Type)
  (bas: forall a b, P (bas_mat a) (bas_mat b))
  (rect: forall {n A1 A2 A3 A4 B1 B2 B3 B4},
    P A1 B1 -> P A2 B2 -> P A3 B3 -> P A4 B4 -> P (rec_mat A1 A2 A3 A4) (rec_mat B1 B2 B3 B4)) :=
  fix mat_rect2_fix {n} (A: Matrix n) : forall B: Matrix n, P A B :=
    match A with
    | @bas_mat a => fun B => mat_case0 (fun B => P (bas_mat a) B) (bas a) B
    | @rec_mat _ A1 A2 A3 A4 => fun B =>
      mat_caseS_ B (fun B' => P (rec_mat A1 A2 A3 A4) B')
      (fun B1 B2 B3 B4 => rect (mat_rect2_fix A1 B1) (mat_rect2_fix A2 B2) (mat_rect2_fix A3 B3) (mat_rect2_fix A4 B4))
    end.

(* A generalized induction scheme for 2 matrices of same size *)
Definition mat_rect2_gen (P: forall {n}, Matrix n -> Matrix n -> Type)
  (bas: forall a b, P (bas_mat a) (bas_mat b))
  (rect: forall {n A1 A2 A3 A4 B1 B2 B3 B4},
    P A1 B1 -> P A1 B2 -> P A1 B3 -> P A1 B4 ->
    P A2 B1 -> P A2 B2 -> P A2 B3 -> P A2 B4 ->
    P A3 B1 -> P A3 B2 -> P A3 B3 -> P A3 B4 ->
    P A4 B1 -> P A4 B2 -> P A4 B3 -> P A4 B4 ->
    P (rec_mat A1 A2 A3 A4) (rec_mat B1 B2 B3 B4)) :=
  fix mat_rect2_gen_fix {n} (A: Matrix n) : forall B: Matrix n, P A B :=
    match A with
    | @bas_mat a => fun B => mat_case0 (fun B => P (bas_mat a) B) (bas a) B
    | @rec_mat _ A1 A2 A3 A4 => fun B =>
      mat_caseS_ B (fun B' => P (rec_mat A1 A2 A3 A4) B')
      (fun B1 B2 B3 B4 => rect
      (mat_rect2_gen_fix A1 B1) (mat_rect2_gen_fix A1 B2) (mat_rect2_gen_fix A1 B3) (mat_rect2_gen_fix A1 B4)
      (mat_rect2_gen_fix A2 B1) (mat_rect2_gen_fix A2 B2) (mat_rect2_gen_fix A2 B3) (mat_rect2_gen_fix A2 B4)
      (mat_rect2_gen_fix A3 B1) (mat_rect2_gen_fix A3 B2) (mat_rect2_gen_fix A3 B3) (mat_rect2_gen_fix A3 B4)
      (mat_rect2_gen_fix A4 B1) (mat_rect2_gen_fix A4 B2) (mat_rect2_gen_fix A4 B3) (mat_rect2_gen_fix A4 B4))
    end.

End SCHEMES.

Section BASES.

(* Zero Matrix *)
Fixpoint mat_0 {n} : Matrix n.
Proof.
  destruct n.
  - exact (bas_mat 0).
  - exact (rec_mat (mat_0 n) (mat_0 n) (mat_0 n) (mat_0 n)).
Defined.

(* One Matrix *)
Fixpoint mat_one {n} : Matrix n.
Proof.
  destruct n.
  - exact (bas_mat 1).
  - exact (rec_mat (mat_one n) (mat_one n) (mat_one n) (mat_one n)).
Defined.

(* Identity Matrix *)
Fixpoint mat_eye {n} : Matrix n.
Proof.
  destruct n.
  - exact (bas_mat 1).
  - exact (rec_mat (mat_eye n) mat_0 mat_0 (mat_eye n)).
Defined.

End BASES.

Section ITERATORS.

(* Uniform application on the elements of the matrix *)
Definition mat_map (f: Complex -> Complex) : forall {n} (A : Matrix n), Matrix n :=
  fix mat_map_fix {n} (A: Matrix n) : Matrix n := match A with
  | bas_mat a => bas_mat (f a)
  | rec_mat A1 A2 A3 A4 => rec_mat (mat_map_fix A1) (mat_map_fix A2) (mat_map_fix A3) (mat_map_fix A4)
  end.

(* Element-wise application of a binary function on the elements of the matrices *)
Definition mat_map2 (g: Complex -> Complex -> Complex) : forall {n}, Matrix n -> Matrix n -> Matrix n :=
  @mat_rect2 (fun n _ _ => Matrix n) (fun a b => bas_mat (g a b))
  (fun n _ _ _ _ _ _ _ _ IH1 IH2 IH3 IH4 => rec_mat IH1 IH2 IH3 IH4).

End ITERATORS.


Section UOP.

(* Matrix negation *)
Definition mat_neg {n} := @mat_map com_neg n.

(* Matrix scalar multiplication *)
Definition mat_scale {n} (a: Complex) := @mat_map (fun b => a * b) n.

(* Matrix conjugate transpose *)
Definition mat_conjtrans {n} (A : Matrix n) : Matrix n.
Proof.
  induction A.
  - exact (bas_mat (com_conj c)).
  - exact (rec_mat IHA1 IHA3 IHA2 IHA4).
Defined.

(* Matrix trace *)
Definition mat_trace {n} (A : Matrix n) : Complex.
Proof.
  induction A.
  - exact c.
  - exact (IHA1 + IHA4).
Defined.

End UOP.


Section BOP.

(* Matrix addition *)
Definition mat_add {n} := @mat_map2 com_add n.

(* Matrix subtraction *)
Definition mat_sub {n} := @mat_map2 com_sub n.

(* Element-wise matrix multiplication *)
Definition mat_mul_elem {n} := @mat_map2 com_mul n.

(* Matrix multiplication *)
Definition mat_mul: forall {n}, Matrix n -> Matrix n -> Matrix n :=
  @mat_rect2_gen (fun n _ _ => Matrix n) (fun a b => bas_mat (a * b))
  (fun n _ _ _ _ _ _ _ _ H11 H12 _ _ _ _ H23 H24 H31 H32 _ _ _ _ H43 H44 =>
    rec_mat (mat_add H11 H23) (mat_add H12 H24) (mat_add H31 H43) (mat_add H32 H44)).

End BOP.

Infix "+" := mat_add : Matrix_scope.
Notation "- A" := (mat_neg A) : Matrix_scope.
Infix "*" := mat_mul : Matrix_scope.
Infix ".*" := mat_scale (at level 35) : Matrix_scope.
Notation "A †" := (mat_conjtrans A) (at level 30) : Matrix_scope. (* opt + t *)
Notation "\tr A" := (mat_trace A) (at level 30) : Matrix_scope.

Section PROPERTIES.

Open Scope Matrix_scope.
Delimit Scope Matrix_scope with mat.

(* Matrix addition is commutative *)
Lemma mat_add_comm : forall {n} (A B : Matrix n), A + B = B + A.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    f_equal.
    all: auto.
Qed.

Hint Extern 1 => (rewrite mat_add_comm) : comm_db.

(* Matrix addition is associative *)
Lemma mat_add_assoc : forall {n} (A B C : Matrix n), A + (B + C) = (A + B) + C.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    specialize (mat_0_inv C) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    specialize (mat_S_inv C) as [C1 [C2 [C3 [C4 HC]]]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Hint Extern 1 => (rewrite mat_add_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- mat_add_assoc) : assoc_db.

(* Zero matrix is the left identity of matrix addition *)
Lemma mat_add_0_l : forall {n} (A : Matrix n), mat_0 + A = A.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: auto.
Qed.

(* Zero matrix is the right identity of matrix addition *)
Lemma mat_add_0_r : forall {n} (A : Matrix n), A + mat_0 = A.
Proof.
  intros.
  rewrite mat_add_comm.
  apply mat_add_0_l.
Qed.

(* Matrix negation is the inverse of matrix addition *)
Lemma mat_add_inv : forall {n} (A : Matrix n), A + (- A) = mat_0.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: auto.
Qed.

(* Matrix multiplication is distributive over matrix addition *)
Lemma mat_mul_dist_l : forall {n} (A B C : Matrix n), A * (B + C) = A * B + A * C.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    specialize (mat_0_inv C) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    specialize (mat_S_inv C) as [C1 [C2 [C3 [C4 HC]]]]; subst.
    simpl.
    repeat rewrite IHn.
    f_equal.
    all: repeat rewrite mat_add_assoc; f_equal.
    all: repeat rewrite <- mat_add_assoc; f_equal.
    all: apply mat_add_comm.
Qed.

Lemma mat_mul_dist_r : forall {n} (A B C : Matrix n), (A + B) * C = A * C + B * C.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    specialize (mat_0_inv C) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    specialize (mat_S_inv C) as [C1 [C2 [C3 [C4 HC]]]]; subst.
    simpl.
    repeat rewrite IHn.
    f_equal.
    all: repeat rewrite mat_add_assoc; f_equal.
    all: repeat rewrite <- mat_add_assoc; f_equal.
    all: apply mat_add_comm.
Qed.

(* Matrix multiplication is associative *)
Lemma mat_mul_assoc : forall {n} (A B C : Matrix n), A * (B * C) = (A * B) * C.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    specialize (mat_0_inv C) as [c]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    specialize (mat_S_inv C) as [C1 [C2 [C3 [C4 HC]]]]; subst.
    simpl.
    repeat rewrite mat_mul_dist_l.
    repeat rewrite IHn.
    repeat rewrite mat_mul_dist_r.
    f_equal.
    all: repeat rewrite mat_add_assoc; f_equal.
    all: repeat rewrite <- mat_add_assoc; f_equal.
    all: apply mat_add_comm.
Qed.

Hint Extern 1 => (rewrite mat_mul_assoc) : dist_db.
Hint Extern 1 => (rewrite <- mat_mul_assoc) : dist_db.

Lemma mat_mul_0_l : forall {n} (A : Matrix n), mat_0 * A = mat_0.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: repeat rewrite IHn.
    all: apply mat_add_0_l.
Qed.

Lemma mat_mul_0_r : forall {n} (A : Matrix n), A * mat_0 = mat_0.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: repeat rewrite IHn.
    all: apply mat_add_0_l.
Qed.

Lemma mat_mul_eye_l : forall {n} (A : Matrix n), mat_eye * A = A.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: rewrite IHn.
    all: rewrite mat_mul_0_l.
    all: try rewrite mat_add_0_l; try rewrite mat_add_0_r.
    all: reflexivity.
Qed.

Lemma mat_mul_eye_r : forall {n} (A : Matrix n), A * mat_eye = A.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: rewrite IHn.
    all: rewrite mat_mul_0_r.
    all: try rewrite mat_add_0_l; try rewrite mat_add_0_r.
    all: reflexivity.
Qed.

Lemma mat_scale_1 : forall {n} (A : Matrix n), 1 .* A = A.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma mat_scale_0 : forall {n} (A : Matrix n), 0 .* A = mat_0.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma mat_0_scale : forall {n} (a : Complex), a .* (@mat_0 n) = mat_0.
Proof.
  intros.
  induction n.
  - simpl.
    f_equal.
    lca.
  - simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma mat_scale_cmul_assoc : forall {n} (a b : Complex) (A : Matrix n), (a * b) .* A = a .* (b .* A).
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a']; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Hint Extern 1 => (rewrite mat_scale_cmul_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- mat_scale_cmul_assoc) : assoc_db.

Lemma mat_scale_dist_l : forall {n} (a : Complex) (A B : Matrix n), a .* (A + B) = a .* A + a .* B.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a']; subst.
    specialize (mat_0_inv B) as [b']; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma mat_scale_dist_r : forall {n} (a b : Complex) (A : Matrix n), (a + b) .* A = a .* A + b .* A.
Proof.
  intros.
  induction A.
  - simpl.
    f_equal.
    lca.
  - simpl.
    f_equal; assumption.
Qed.

Lemma mat_scale_mul_assoc : forall {n} (a : Complex) (A B : Matrix n), (a .* A) * B = a .* (A * B).
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a']; subst.
    specialize (mat_0_inv B) as [b']; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite mat_scale_dist_l.
    reflexivity.
Qed.

Hint Extern 1 => (rewrite mat_scale_mul_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- mat_scale_mul_assoc) : assoc_db.

Lemma mat_scale_mul_comm: forall {n} (a : Complex) (A B : Matrix n), (a .* A) * B = A * (a .* B).
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a']; subst.
    specialize (mat_0_inv B) as [b']; subst.
    simpl.
    f_equal.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    repeat rewrite IHn.
    reflexivity.
Qed.

Hint Extern 1 => (rewrite mat_scale_mul_comm) : comm_db.

Lemma mat_scale_scale_comm: forall {n} (a b: Complex) (A: Matrix n), (a * b) .* A = a .* (b .* A).
Proof.
  intros.
  induction A.
  - com_simpl.
    rewrite com_mul_assoc.
    reflexivity.
  - simpl. f_equal; assumption.
Qed.

Lemma mat_conjtrans_involutive : forall {n} (A : Matrix n), A†† = A.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    apply com_conj_involutive.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

Lemma mat_add_conjtrans : forall {n} (A B : Matrix n), (A + B)† = A† + B†.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    apply com_conj_add.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    f_equal.
    all: apply IHn.
Qed.

Lemma mat_mul_conjtrans : forall {n} (A B : Matrix n), (A * B)† = B† * A†.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    rewrite com_conj_mul.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    repeat rewrite mat_add_conjtrans.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma mat_scale_conjtrans : forall {n} (a : Complex) (A : Matrix n), (a .* A)† = com_conj a .* A†.
Proof.
  intros.
  induction A.
  - simpl.
    f_equal.
    apply com_conj_mul.
  - simpl.
    rewrite IHA1; rewrite IHA2; rewrite IHA3; rewrite IHA4.
    reflexivity.
Qed.

Lemma mat_scale_trace : forall {n} (a : Complex) (A : Matrix n), \tr (a .* A) = (a * \tr A)%com.
Proof.
  intros.
  induction A.
  - simpl.
    lca.
  - simpl.
    rewrite IHA1, IHA4.
    lca.
Qed.

Lemma mat_add_trace : forall {n} (A B : Matrix n), \tr (A + B) = (\tr A + \tr B)%com.
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    repeat rewrite IHn.
    lca.
Qed.

Lemma mat_mul_trace_comm : forall {n} (A B : Matrix n), \tr (A * B) = \tr (B * A).
Proof.
  intros.
  induction n.
  - specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    lca.
  - specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 HA]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 HB]]]]; subst.
    simpl.
    repeat rewrite mat_add_trace.
    replace (\tr (B1 * A1)) with (\tr (A1 * B1)) by apply IHn.
    replace (\tr (B2 * A3)) with (\tr (A3 * B2)) by apply IHn.
    replace (\tr (B3 * A2)) with (\tr (A2 * B3)) by apply IHn.
    replace (\tr (B4 * A4)) with (\tr (A4 * B4)) by apply IHn.
    lca.
Qed.

Lemma mat_trace_conjtrans : forall {n} (A : Matrix n), \tr (A†) = (\tr A) ^*.
Proof.
  intros.
  induction A.
  - reflexivity.
  - simpl.
    rewrite com_conj_add.
    rewrite IHA1, IHA4.
    reflexivity.
Qed.

Lemma mat_trace_0 : forall {n}, \tr (@mat_0 n) = 0.
Proof.
  intros.
  induction n.
  - simpl; lca.
  - simpl.
    rewrite IHn.
    lca.
Qed.

Hint Extern 1 => (rewrite mat_mul_trace_comm) : comm_db.

Lemma mat_eq_imp_mul_l : forall {n: nat} {A B: Matrix n} (C: Matrix n),
  A = B -> C * A = C * B.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma mat_eq_imp_mul_r : forall {n: nat} {A B: Matrix n} (C: Matrix n),
  A = B -> A * C = B * C.
Proof.
  intros. rewrite H. reflexivity.
Qed.

End PROPERTIES.

Section MatrixRing.

Definition mat_ring n: Ring_theory.ring_theory (@mat_0 n) mat_one mat_add mat_mul_elem mat_sub mat_neg eq.
Proof.
  constructor.
  - apply mat_add_0_l.
  - apply mat_add_comm.
  - apply mat_add_assoc.
  - induction n.
    + intros.
      specialize (mat_0_inv x) as [a]; subst.
      simpl; f_equal.
      lca.
    + intros.
      specialize (mat_S_inv x) as [A1 [A2 [A3 [A4 HA]]]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - induction n.
    + intros.
      specialize (mat_0_inv x) as [a]; subst.
      specialize (mat_0_inv y) as [b]; subst.
      simpl; f_equal.
      lca.
    + intros.
      specialize (mat_S_inv x) as [A1 [A2 [A3 [A4 HA]]]]; subst.
      specialize (mat_S_inv y) as [B1 [B2 [B3 [B4 HB]]]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - induction n.
    + intros.
      specialize (mat_0_inv x) as [a]; subst.
      specialize (mat_0_inv y) as [b]; subst.
      specialize (mat_0_inv z) as [c]; subst.
      simpl; f_equal.
      lca.
    + intros.
      specialize (mat_S_inv x) as [A1 [A2 [A3 [A4 HA]]]]; subst.
      specialize (mat_S_inv y) as [B1 [B2 [B3 [B4 HB]]]]; subst.
      specialize (mat_S_inv z) as [C1 [C2 [C3 [C4 HC]]]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - induction n.
    + intros.
      specialize (mat_0_inv x) as [a]; subst.
      specialize (mat_0_inv y) as [b]; subst.
      specialize (mat_0_inv z) as [c]; subst.
      simpl; f_equal.
      lca.
    + intros.
      specialize (mat_S_inv x) as [A1 [A2 [A3 [A4 HA]]]]; subst.
      specialize (mat_S_inv y) as [B1 [B2 [B3 [B4 HB]]]]; subst.
      specialize (mat_S_inv z) as [C1 [C2 [C3 [C4 HC]]]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - induction n.
    + intros.
      specialize (mat_0_inv x) as [a]; subst.
      specialize (mat_0_inv y) as [b]; subst.
      reflexivity.
    + intros.
      specialize (mat_S_inv x) as [A1 [A2 [A3 [A4 HA]]]]; subst.
      specialize (mat_S_inv y) as [B1 [B2 [B3 [B4 HB]]]]; subst.
      simpl; f_equal.
      all: apply IHn.
  - apply mat_add_inv.
Qed.

End MatrixRing.

Section MatrixCast.

Lemma add_comm: forall {m n}, (m + n)%nat = (n + m)%nat.
Proof. lia. Qed.

Lemma add_assoc: forall {m n k: nat}, (m + (n + k))%nat = (m + n + k)%nat.
Proof. lia. Qed.

(* Convertible Typecasting of matrix *)
Definition mat_ccast {n m} (A: Matrix n): n = m -> Matrix m.
Proof.
  intros.
  generalize H. clear H.
  generalize m. clear m.
  induction A as [a|]; intros; destruct m.
  - constructor. exact a.
  - exfalso. apply (O_S _ H).
  - exfalso. apply (O_S _ (eq_sym H)).
  - constructor; apply eq_add_S in H.
    apply (IHA1 _ H).
    apply (IHA2 _ H).
    apply (IHA3 _ H).
    apply (IHA4 _ H).
Defined.

(* Eq_rect based Typecasting of matrix *)
Definition mat_cast {n m} (A: Matrix n) (H: n = m): Matrix m.
Proof.
  rewrite <- H.
  exact A.
Defined.

Lemma mat_ccast_refl: forall {n} (A: Matrix n) (H: n = n),
  mat_ccast A H = A.
Proof.
  intros.
  induction A.
  - reflexivity.
  - simpl.
    rewrite IHA1. rewrite IHA2. rewrite IHA3. rewrite IHA4.
    reflexivity.
Qed.

Lemma mat_cast_ccast: forall {m n} (A: Matrix n) (H: n = m),
  mat_cast A H = mat_ccast A H.
Proof.
  intros.
  induction A.
  - destruct H. reflexivity.
  - destruct H.
    simpl.
    f_equal; rewrite mat_ccast_refl; reflexivity.
Qed.

Lemma mat_ccast_refl': forall {n m} (A: Matrix n) (H1 H2: n = m),
  mat_ccast A H1 = mat_ccast A H2.
Proof.
  intros.
  generalize H2. clear H2.
  generalize H1. clear H1.
  generalize m. clear m.
  induction A; intros; destruct m.
  - reflexivity.
  - inversion H1.
  - inversion H1.
  - simpl.
    erewrite IHA1. erewrite IHA2. erewrite IHA3. erewrite IHA4.
    reflexivity.
Qed.

Lemma mat_cast_refl: forall {n} (A: Matrix n) (H: n = n),
  mat_cast A H = A.
Proof.
  intros. simpl_eq. reflexivity.
Qed.

Lemma mat_cast_refl': forall {n m} (A: Matrix n) (H1 H2: n = m),
  mat_cast A H1 = mat_cast A H2.
Proof.
  intros.
  repeat rewrite mat_cast_ccast.
  apply mat_ccast_refl'.
Qed.

Lemma mat_JMeq_refl: forall n m (A: Matrix n) (H : n = m),
  JMeq (mat_cast A H) A.
Proof.
  intros.
  unfold mat_cast, eq_rect.
  destruct H.
  apply JMeq_refl.
Qed.

Lemma mat_cast_trans: forall n m k (A: Matrix n) (H1: n = m) (H2: m = k),
  mat_cast A (eq_trans H1 H2) = mat_cast (mat_cast A H1) H2.
Proof.
  intros.
  apply JMeq_eq.
  eapply JMeq_trans.
  - apply mat_JMeq_refl.
  - destruct H2. destruct H1. apply JMeq_refl.
Qed.

Lemma mat_ccast_trans: forall n m k (A: Matrix n) (H1: n = m) (H2: m = k),
  mat_ccast A (eq_trans H1 H2) = mat_ccast (mat_ccast A H1) H2.
Proof.
  intros.
  repeat rewrite <- mat_cast_ccast.
  apply mat_cast_trans.
Qed.

Lemma mat_JMeq_refl': forall {n m k} (A: Matrix n) (H1 : n = m) (H2: n = k),
  JMeq (mat_cast A H1) (mat_cast A H2).
Proof.
  intros.
  unfold mat_cast, eq_rect.
  destruct H1.
  destruct H2.
  apply JMeq_refl.
Qed.

Lemma JMeq_comm: forall {m n} (A: Matrix (m + n)),
  JMeq A (mat_cast A add_comm).
Proof.
  intros.
  rewrite mat_JMeq_refl.
  reflexivity.
Qed.

Lemma JMeq_assoc: forall {m n k} (A: Matrix (m + (n + k))),
  JMeq A (mat_cast A (add_assoc)).
Proof.
  intros.
  rewrite mat_JMeq_refl.
  reflexivity.
Qed.

Lemma mat_0_ccast: forall {n m} (H: m = n),
  @mat_0 n = mat_ccast (@mat_0 m) H.
Proof.
  induction n; intros; destruct m.
  - reflexivity.
  - inversion H.
  - inversion H.
  - simpl. f_equal; apply IHn.
Qed.

Lemma mat_0_cast: forall {n m} (H: m = n),
  @mat_0 n = mat_cast (@mat_0 m) H.
Proof. intros. rewrite mat_cast_ccast. apply mat_0_ccast. Qed.

Lemma mat_0_JMeq: forall {n m},
  n = m -> JMeq (@mat_0 n) (@mat_0 m).
Proof. intros; rewrite H; reflexivity. Qed.

Lemma mat_eye_ccast: forall {n m} (H: m = n),
  @mat_eye n = mat_ccast (@mat_eye m) H.
Proof.
  induction n; intros; destruct m.
  - reflexivity.
  - inversion H.
  - inversion H.
  - simpl. f_equal; try apply IHn.
    all: apply mat_0_ccast.
Qed.

Lemma mat_eye_cast: forall {n m} (H: m = n),
  @mat_eye n = mat_cast (@mat_eye m) H.
Proof. intros. rewrite mat_cast_ccast. apply mat_eye_ccast. Qed.

Lemma mat_eye_JMeq: forall {n m},
  n = m -> JMeq (@mat_eye n) (@mat_eye m).
Proof. intros; rewrite H; reflexivity. Qed.

End MatrixCast.

Ltac mat_cast :=
  repeat (
    rewrite <- mat_cast_ccast ||
    rewrite mat_eye_cast ||
    rewrite mat_0_cast ||
    rewrite mat_cast_trans ||
    apply mat_cast_refl ||
    apply mat_cast_refl' ||
    rewrite mat_cast_refl ||
    rewrite mat_cast_refl' ||
    reflexivity
  ).

Ltac do_JMeq :=
  repeat (
    rewrite JMeq_eq ||
    rewrite mat_JMeq_refl ||
    rewrite <- JMeq_comm ||
    rewrite <- JMeq_assoc ||
    apply mat_eye_JMeq; try lia ||
    apply mat_0_JMeq; try lia ||
    reflexivity
  ).
















Section EXAMPLE.

Variable n: nat.

Add Ring MRing : (mat_ring n).

Open Scope Matrix_scope.

Theorem temp: forall (A B C D: Matrix n), A + B + C + D = A + (B + C) + D.
Proof.
  intros.
  ring.
Qed.

End EXAMPLE.

Arguments temp {_}.

(* Ltac mat_simplify :=
  repeat (
    simpl ||
    rewrite mat_add_assoc ||
    rewrite mat_add_0_l ||
    rewrite mat_add_0_r ||
    rewrite mat_mul_dist_l ||
    rewrite mat_mul_dist_r ||
    rewrite mat_mul_0_l ||
    rewrite mat_mul_0_r ||
    rewrite mat_mul_eye_l ||
    rewrite mat_mul_eye_r
  ). *)
