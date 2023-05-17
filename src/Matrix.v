Require Export Complex.
Require Import FunctionalExtensionality.
Import ListNotations.

Declare Scope M_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Delimit Scope C_scope with C.

(* Matrix record ================================================================================ *)

Record Matrix: Type := {
  Mbits: nat;
  Minner: nat -> nat -> C;
}.

Definition Msize (m: Matrix): nat := Nat.pow 2 (Mbits m).

Definition MMeqbits (m1 m2: Matrix): Prop := Mbits m1 = Mbits m2.

(* ============================================================================================== *)
(* Vector record ================================================================================ *)

Record RowVec: Type := {
  RVbits: nat;
  RVinner: nat -> C;
}.

Record ColVec: Type := {
  CVbits: nat;
  CVinner: nat -> C;
}.

Definition RVsize (r: RowVec): nat := Nat.pow 2 (RVbits r).
Definition CVsize (c: ColVec): nat := Nat.pow 2 (CVbits c).

Definition MReqbits (m: Matrix) (r: RowVec): Prop := Mbits m = RVbits r.
Definition RMeqbits (r: RowVec) (m: Matrix) : Prop := RVbits r = Mbits m.
Definition MCeqbits (m: Matrix) (c: ColVec): Prop := Mbits m = CVbits c.
Definition CMeqbits (c: ColVec) (m: Matrix): Prop := CVbits c = Mbits m.
Definition RReqbits (r1 r2: RowVec): Prop := RVbits r1 = RVbits r2.
Definition RCeqbits (r: RowVec) (c: ColVec): Prop := RVbits r = CVbits c.
Definition CReqbits (c: ColVec) (r: RowVec): Prop := CVbits c = RVbits r.
Definition CCeqbits (c1 c2: ColVec): Prop := CVbits c1 = CVbits c2.

(* ============================================================================================== *)
(* get an element from a matrix ================================================================= *)

Definition Mget (m : Matrix) (i j: nat) (Hi: i < Msize m) (Hj: j < Msize m): C := Minner m i j.

Notation "m '[[' i Hi '|' j Hj ']]'" :=
  (Mget m i j Hi Hj) (at level 10, i at level 9, Hi at level 9, j at level 9, Hj at level 9, no associativity).

(* ============================================================================================== *)
(* get an element from a vector ================================================================= *)

Definition RVget (r : RowVec) (j: nat) (Hj: j < RVsize r): C := RVinner r j.
Definition CVget (c : ColVec) (i: nat) (Hi: i < CVsize c): C := CVinner c i.

(* ============================================================================================== *)
(* equality of two matrices ===================================================================== *)

Axiom Mequal: forall (m1 m2: Matrix),
  Mbits m1 = Mbits m2 -> (forall i j, i < Msize m1 -> j < Msize m2 -> Minner m1 i j = Minner m2 i j) -> m1 = m2.

(* ============================================================================================== *)
(* equality of two vectors ====================================================================== *)

Definition RVequal (r1 r2: RowVec): Prop := forall (j: nat) (Hj1: _) (Hj2: _),
  (RReqbits r1 r2) /\ (RVget r1 j Hj1 = RVget r2 j Hj2).

Definition CVequal (c1 c2: ColVec): Prop := forall (i: nat) (Hi1: _) (Hi2: _),
  (CCeqbits c1 c2) /\ (CVget c1 i Hi1 = CVget c2 i Hi2).

(* ============================================================================================== *)
(* extract row and column vectors from a matrix ================================================= *)

Definition extract_row (m: Matrix) (i: nat) (Hi: i < Msize m): RowVec :=
  {|
    RVbits := Mbits m;
    RVinner := fun j => Minner m i j;
  |}.

Lemma extract_row_bits: forall (m: Matrix) (i: nat) (Hi: _), RMeqbits (extract_row m i Hi) m.
Proof. reflexivity. Qed.

Definition extract_col (m: Matrix) (j: nat) (Hj: j < Msize m): ColVec :=
  {|
    CVbits := Mbits m;
    CVinner := fun i => Minner m i j;
  |}.

Lemma extract_col_bits: forall (m: Matrix) (j: nat) (Hj: _), CMeqbits (extract_col m j Hj) m.
Proof. reflexivity. Qed.

Definition extract_row_unsafe (m: Matrix) (i: nat): RowVec :=
  {|
    RVbits := Mbits m;
    RVinner := fun j => Minner m i j;
  |}.

Lemma extract_row_unsafe_bits: forall (m: Matrix) (i: nat), RMeqbits (extract_row_unsafe m i) m.
Proof. reflexivity. Qed.

Definition extract_col_unsafe (m: Matrix) (j: nat): ColVec :=
  {|
    CVbits := Mbits m;
    CVinner := fun i => Minner m i j;
  |}.

Lemma extract_col_unsafe_bits: forall (m: Matrix) (j: nat), CMeqbits (extract_col_unsafe m j) m.
Proof. reflexivity. Qed.

Lemma extract_row_correct: forall
  (m: Matrix) (r: RowVec) (i j: nat) (Hi Hi': _) (Hj: _) (Hjr: _),
  RVget (extract_row m i Hi) j Hjr = m[[i Hi'|j Hj]].
Proof.
  unfold extract_row.
  intros.
  unfold RVget.
  unfold Mget.
  simpl.
  reflexivity.
Qed.

Lemma extract_col_correct: forall
  (m: Matrix) (c: ColVec) (i j: nat) (Hi: _) (Hj Hj': _) (Hic: _),
  CVget (extract_col m j Hj) i Hic = m[[i Hi|j Hj']].
Proof.
  unfold extract_col.
  intros.
  unfold CVget.
  unfold Mget.
  simpl.
  reflexivity.
Qed.

Fixpoint dot_product_suppl (r c: nat -> C) (idx: nat): C.
Proof.
  destruct idx as [|idx'].
  - exact O.
  - apply (r idx' * c idx' + dot_product_suppl r c idx').
Defined.

Definition dot_product (r: RowVec) (c: ColVec) (Hrc: RCeqbits r c): C :=
  dot_product_suppl (RVinner r) (CVinner c) (RVsize r).

Lemma dot_product_suppl_scale_l: forall (l: nat) (c: C) (f1 f2 f: nat -> C),
  (forall n, f1 n = c * f2 n) -> dot_product_suppl f1 f l = c * dot_product_suppl f2 f l.
Proof.
  intros.
  induction l as [|l'].
  - lca.
  - simpl.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_scale_r: forall (l: nat) (c: C) (f1 f2 f: nat -> C),
  (forall n, f1 n = c * f2 n) -> dot_product_suppl f f1 l = c * dot_product_suppl f f2 l.
Proof.
  intros.
  induction l as [|l'].
  - lca.
  - simpl.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_comm: forall (l: nat) (f1 f2: nat -> C),
  dot_product_suppl f1 f2 l = dot_product_suppl f2 f1 l.
Proof.
  intros.
  induction l as [|l'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    lca.
Qed.

Lemma dot_product_suppl_dist_l: forall (l: nat) (f f1 f2 f12: nat -> C),
  (forall n, f12 n = f1 n + f2 n) -> dot_product_suppl f12 f l = dot_product_suppl f1 f l + dot_product_suppl f2 f l.
Proof.
  intros.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    ring_simplify.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_dist_r: forall (l: nat) (f f1 f2 f12: nat -> C),
  (forall n, f12 n = f1 n + f2 n) -> dot_product_suppl f f12 l = dot_product_suppl f f1 l + dot_product_suppl f f2 l.
Proof.
  intros.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    ring_simplify.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_assoc: forall (l: nat) (f1 f3: nat -> C) (f2: nat -> nat -> C),
  dot_product_suppl (fun j0 => dot_product_suppl f1 (fun i0 => f2 i0 j0) l) f3 l =
  dot_product_suppl f1 (fun i0 => dot_product_suppl (fun j0 => f2 i0 j0) f3 l) l.
Proof.
  intros.
  induction l as [|l'].
  - reflexivity.
  - simpl.
    specialize dot_product_suppl_dist_l with
      (f := f3)
      (f1 := fun j0 => f1 l' * f2 l' j0)
      (f2 := fun j0 => dot_product_suppl f1 (fun i0 : nat => f2 i0 j0) l')
      (f12 := fun j0 : nat => f1 l' * f2 l' j0 + dot_product_suppl f1 (fun i0 : nat => f2 i0 j0) l') as Hdist1.
    specialize dot_product_suppl_dist_r with
      (f := f1)
      (f1 := fun i0 => f2 i0 l' * f3 l')
      (f2 := fun i0 => dot_product_suppl (fun j0 : nat => f2 i0 j0) f3 l')
      (f12 := fun i0 : nat => f2 i0 l' * f3 l' + dot_product_suppl (fun j0 : nat => f2 i0 j0) f3 l') as Hdist2.
    rewrite Hdist1.
    rewrite Hdist2.
    rewrite IHl'.
    specialize dot_product_suppl_scale_l with
    (f1 := fun j0 : nat => f1 l' * f2 l' j0)
    (f2 := fun j0 : nat => f2 l' j0)
    (c := f1 l') as Hscale1.
    specialize dot_product_suppl_scale_r with
    (f1 := fun i0 : nat => f2 i0 l' * f3 l')
    (f2 := fun i0 : nat => f2 i0 l')
    (c := f3 l') as Hscale2.
    rewrite Hscale1.
    rewrite Hscale2.
    ring_simplify.
    lca.
    intros. lca.
    intros. lca.
    intros. lca.
    intros. lca.
Qed.

Lemma dot_product_suppl_conj1: forall (l: nat) (f1 f2: nat -> C),
  Cconj (dot_product_suppl f1 f2 l) =
  dot_product_suppl (fun n => Cconj (f1 n)) (fun n => Cconj (f2 n)) l.
Proof.
  intros.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    rewrite Cconj_plus.
    rewrite Cconj_mult.
    rewrite IHl'.
    reflexivity.
Qed.

Lemma dot_product_suppl_conj2: forall (l: nat) (f1 f2: nat -> C),
  Cconj (dot_product_suppl f1 f2 l) =
  dot_product_suppl (fun n => Cconj (f2 n)) (fun n => Cconj (f1 n)) l.
Proof.
  intros.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    rewrite Cconj_plus.
    rewrite Cconj_mult.
    rewrite IHl'.
    lca.
Qed.

Lemma dot_product_suppl_f_r: forall (l: nat) (f1 f2 f3: nat -> C),
  (forall n, n < l -> f2 n = f3 n) -> dot_product_suppl f1 f2 l = dot_product_suppl f1 f3 l.
Proof.
  intros.
  induction l as [|l'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    rewrite H.
    reflexivity.
    lia.
    intros.
    apply H.
    lia.
Qed.

(* ============================================================================================== *)
(* element-wise unary operation ================================================================= *)

Definition Muop (uop: C -> C) (m: Matrix): Matrix :=
  {|
    Mbits := Mbits m;
    Minner := fun i j => uop (Minner m i j);
  |}.

Lemma Muop_bits: forall (uop: C -> C) (m: Matrix), MMeqbits (Muop uop m) m.
Proof. reflexivity. Qed.

Lemma Muop_correct: forall
  (uop: C -> C) (m: Matrix) (i j: nat)
  (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  (Muop uop m)[[i H2i|j H2j]] = uop (m[[i H1i|j H1j]]).
Proof.
  intros.
  unfold Mget.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* opposite of a matrix ========================================================================= *)

Definition Mopp (m: Matrix): Matrix := Muop Copp m.

Lemma Mopp_bits: forall (m: Matrix), MMeqbits (Mopp m) m.
Proof. apply Muop_bits. Qed.

Lemma Mopp_correct: forall
  (m: Matrix) (i j: nat)
  (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  (Mopp m)[[i H2i|j H2j]] = Copp (m[[i H1i|j H1j]]).
Proof. apply Muop_correct. Qed.

(* ============================================================================================== *)
(* scalar multiplication ======================================================================== *)

Definition Msmul (s: C) (m: Matrix): Matrix := Muop (Cmult s) m.

Lemma Msuml_correct: forall
  (s: C) (m: Matrix) (i j: nat)
  (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  (Msmul s m)[[i H2i|j H2j]] = (Cmult s) (m[[i H1i|j H1j]]).
Proof. intro s. apply Muop_correct. Qed.

(* ============================================================================================== *)
(* element-wise binary operation ================================================================ *)

Definition Mbop_unsafe (bop: C -> C -> C) (m1 m2: Matrix): Matrix :=
  {|
    Mbits := Mbits m1;
    Minner := fun i j => bop (Minner m1 i j) (Minner m2 i j)
  |}.

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: MMeqbits m1 m2): Matrix :=
  Mbop_unsafe bop m1 m2.

Lemma Mbop_bits_l: forall (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: _),
  MMeqbits m1 (Mbop bop m1 m2 Hbits).
Proof. reflexivity. Qed.

Lemma Mbop_bits_r: forall (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: _),
  MMeqbits m2 (Mbop bop m1 m2 Hbits).
Proof.
  intros.
  unfold Mbop.
  unfold MMeqbits in *.
  simpl.
  rewrite <- Hbits.
  reflexivity.
Qed.

Lemma Mbop_correct: forall
  (bop: C -> C -> C) (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  (Mbop bop m1 m2 Hbits)[[i H3i|j H3j]] = bop (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  unfold Mbop, Mget.
  intros.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* matrix addition ============================================================================== *)

Definition Mplus (m1 m2: Matrix) (Hbits: MMeqbits m1 m2) := Mbop_unsafe Cplus m1 m2.

Lemma Mplus_bits_l: forall (m1 m2: Matrix) (Hbits: _), MMeqbits m1 (Mplus m1 m2 Hbits).
Proof. apply Mbop_bits_l. Qed.

Lemma Mplus_bits_r: forall (m1 m2: Matrix) (Hbits: _), MMeqbits m2 (Mplus m1 m2 Hbits).
Proof. apply Mbop_bits_r. Qed.

Lemma Mplus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  (Mplus m1 m2 Hbits)[[i H3i|j H3j]] = Cplus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof. apply Mbop_correct. Qed.

(* ============================================================================================== *)
(* matrix subtraction =========================================================================== *)

Definition Mminus (m1 m2: Matrix) (Hbits: MMeqbits m1 m2) := Mbop_unsafe Cminus m1 m2.

Lemma Mminus_bits_l: forall (m1 m2: Matrix) (Hbits: _), MMeqbits m1 (Mminus m1 m2 Hbits).
Proof. apply Mbop_bits_l. Qed.

Lemma Mminus_bits_r: forall (m1 m2: Matrix) (Hbits: _), MMeqbits m2 (Mminus m1 m2 Hbits).
Proof. apply Mbop_bits_r. Qed.

Lemma Mminus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  (Mminus m1 m2 Hbits)[[i H3i|j H3j]] = Cminus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof. apply Mbop_correct. Qed.

(* ============================================================================================== *)
(* matrix multiplication ======================================================================== *)

Definition Mmult_inner (m1 m2: Matrix) (i j: nat): C :=
  dot_product_suppl
    (RVinner (extract_row_unsafe m1 i))
    (CVinner (extract_col_unsafe m2 j))
    (Msize m1).

Definition Mmult_unsafe (m1 m2: Matrix) : Matrix :=
  {|
    Mbits := Mbits m1;
    Minner := fun i j => Mmult_inner m1 m2 i j;
  |}.

Definition Mmult (m1 m2: Matrix) (H: MMeqbits m1 m2): Matrix := Mmult_unsafe m1 m2.

Lemma Mmult_bits_l: forall (m1 m2: Matrix) (H: _), MMeqbits (Mmult m1 m2 H) m1.
Proof. reflexivity. Qed.

Lemma Mmult_bits_r: forall (m1 m2: Matrix) (H: _), MMeqbits (Mmult m1 m2 H) m2.
Proof.
  intros.
  unfold Mmult.
  unfold MMeqbits in *.
  simpl.
  apply H.
Qed.

Lemma Mmult_correct: forall (m1 m2 m: Matrix) (r: RowVec) (c: ColVec) (i j: nat)
  (Hi: _) (Hj: _) (H: _) (Hmi: _) (Hmj: _) (Hrc: _),
  (Mmult m1 m2 H)[[i Hmi|j Hmj]] = dot_product (extract_row m1 i Hi) (extract_col m2 j Hj) Hrc.
Proof.
  intros.
  unfold Mget.
  unfold Mmult_inner.
  unfold dot_product.
  simpl.
  reflexivity.
Qed.

Lemma Mmult_assoc: forall (m1 m2 m3: Matrix)
  (H12: _) (H12_3: _) (H23: _) (H1_23: _),
  (Mmult (Mmult m1 m2 H12) m3 H12_3) = (Mmult m1 (Mmult m2 m3 H23) H1_23).
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    reflexivity.
  - intros.
    unfold Mget.
    simpl.
    unfold Mmult.
    unfold Mmult_unsafe.
    unfold Mmult_inner.
    unfold extract_row_unsafe.
    unfold extract_col_unsafe.
    unfold RVsize.
    unfold Msize in *.
    simpl in *.
    rewrite H12.
    apply dot_product_suppl_assoc.
Qed.

(* Lemma Mmult_eq: forall (m1 m2 m3: Matrix) (H12: _) (H13: _),
Mequal m2 m3 -> Mequal (Mmult m1 m2 H12) (Mmult m1 m3 H13).
Proof.
  intros.
  split.
  - unfold MMeqbits.
    repeat rewrite Mmult_bits_l.
    reflexivity.
  - intros.
    destruct H.
    unfold Mget in *.
    unfold Mmult.
    unfold Mmult_inner.
    simpl.
    apply dot_product_suppl_f_r.
    intros.
    unfold MMeqbits in *.
    unfold Msize in *.
    rewrite Mmult_bits_r in *.
    apply H0.
    rewrite <- H12.
    apply H1.
    rewrite <- H13.
    apply H1.
    lia.
    lia.
Qed. *)


(* ============================================================================================== *)
(* matrix-vector multiplication ================================================================= *)

Definition MVmult_inner (m: Matrix) (c: ColVec) (i: nat): C :=
  dot_product_suppl (RVinner (extract_row_unsafe m i)) (CVinner c) (CVsize c).

Definition MVmult (m: Matrix) (c: ColVec) (H: MCeqbits m c): ColVec :=
  {|
    CVbits := CVbits c;
    CVinner := fun i => MVmult_inner m c i;
  |}.

Lemma MVmult_bits_l: forall (m: Matrix) (c: ColVec) (H: _), CMeqbits (MVmult m c H) m.
Proof.
  intros.
  unfold CMeqbits.
  unfold MVmult.
  simpl.
  symmetry.
  apply H.
Qed.

Lemma MVmult_bits_r (m: Matrix) (c: ColVec) (H: _): CCeqbits (MVmult m c H) c.
Proof. reflexivity. Qed.

Lemma MVmult_correct: forall (m: Matrix) (r: RowVec) (c c': ColVec) (i: nat)
  (Hi: _) (H: _) (Hci: _) (Hrc: _),
  CVget (MVmult m c H) i Hci = dot_product (extract_row m i Hi) c Hrc.
Proof.
  intros.
  unfold CVget, dot_product.
  unfold MVmult_inner.
  unfold RVsize.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma MMVmult_assoc: forall (m1 m2 m12: Matrix) (c3 c23 c12_3 c1_23: ColVec)
  (H12: _) (H12_3: _) (H23: _) (H1_23: _),
  CVequal (MVmult (Mmult m1 m2 H12) c3 H12_3) (MVmult m1 (MVmult m2 c3 H23) H1_23).
Proof.
  intros.
  unfold CVequal.
  split.
  - unfold CCeqbits.
    simpl.
    rewrite <- H12_3.
    reflexivity.
  - unfold CVget.
    simpl.
    unfold Mmult.
    unfold MVmult.
    unfold Mmult_inner.
    unfold MVmult_inner.
    unfold extract_row_unsafe.
    unfold CVsize.
    unfold RVsize.
    unfold Msize.
    simpl in *.
    replace (CVbits c3) with (Mbits m1).
    apply dot_product_suppl_assoc.
Qed.

(* ============================================================================================== *)
(* vector-matrix multiplication ================================================================= *)


Definition VMmult_inner (r: RowVec) (m: Matrix) (j: nat): C :=
  dot_product_suppl (RVinner r) (CVinner (extract_col_unsafe m j)) (RVsize r).

Definition VMmult (r: RowVec) (m: Matrix) (H: RMeqbits r m): RowVec :=
  {|
    RVbits := RVbits r;
    RVinner := fun j => VMmult_inner r m j;
  |}.

Lemma VMmult_bits_l: forall (r: RowVec) (m: Matrix) (H: RMeqbits r m), RReqbits (VMmult r m H) r.
Proof. reflexivity. Qed.

Lemma VMmult_bits_r: forall (r: RowVec) (m: Matrix) (H: RMeqbits r m), RMeqbits (VMmult r m H) m.
Proof.
  intros.
  unfold RMeqbits.
  unfold VMmult.
  simpl.
  apply H.
Qed.

Lemma VMmult_correct: forall (m: Matrix) (r r': RowVec) (c: ColVec) (j: nat)
  (Hj: _) (H: _) (Hri: _) (Hrc: _),
  RVget (VMmult r m H) j Hri = dot_product r (extract_col m j Hj) Hrc.
Proof.
  intros.
  unfold RVget, dot_product.
  unfold MVmult_inner.
  unfold RVsize.
  simpl.
  reflexivity.
Qed.

Lemma VMMmult_assoc: forall (r1 r12 r12_3 r1_23: RowVec) (m3 m2 m23: Matrix)
  (H12: _) (H12_3: _) (H23: _) (H1_23: _),
  RVequal (VMmult (VMmult r1 m2 H12) m3 H12_3) (VMmult r1 (Mmult m2 m3 H23) H1_23).
Proof.
  intros.
  unfold RVequal.
  split.
  - unfold RReqbits.
    simpl.
    rewrite H12_3.
    reflexivity.
  - unfold RVget. simpl.
    unfold Mmult.
    unfold Mmult_inner.
    unfold VMmult.
    unfold VMmult_inner.
    unfold extract_col_unsafe.
    unfold CVsize.
    unfold RVsize.
    simpl in *.
    replace (RVbits r1) with (Mbits m2).
    apply dot_product_suppl_assoc.
Qed.

(* ============================================================================================== *)
(* vector-vector multiplication (outer product) ================================================= *)

Definition VVmult (c: ColVec) (r: RowVec) (H: CReqbits c r): Matrix :=
  {|
    Mbits := CVbits c;
    Minner := fun i j => CVinner c i * RVinner r j;
  |}.

(* ============================================================================================== *)
(* transpose of a matrix ======================================================================== *)

Definition Mtranspose (m: Matrix): Matrix :=
  {|
    Mbits := Mbits m;
    Minner := fun i j => Minner m j i;
  |}.

Lemma Mtranspose_bits: forall (m: Matrix), MMeqbits (Mtranspose m) m.
Proof. reflexivity. Qed.

Lemma Mtranspose_correct: forall (m mt: Matrix) (i j: nat) (Hi: _) (Hi': _) (Hj: _) (Hj': _),
  m[[i Hi|j Hj]] = (Mtranspose m)[[j Hj'|i Hi']].
Proof.
  unfold Mtranspose.
  unfold Mget.
  intros.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* transpose of a vector ======================================================================== *)

Definition RVtranspose (r: RowVec): ColVec :=
  {|
    CVbits := RVbits r;
    CVinner :=  RVinner r;
  |}.

Lemma RVtranspose_size: forall (r: RowVec), CReqbits (RVtranspose r) r.
Proof. reflexivity. Qed.

Definition CVtranspose (c: ColVec): RowVec :=
  {|
    RVbits := CVbits c;
    RVinner :=  CVinner c;
  |}.

Lemma CVtranspose_size: forall (c: ColVec), RCeqbits (CVtranspose c) c.
Proof. reflexivity. Qed.

(* ============================================================================================== *)
(* conjugate tranpose of a matrix =============================================================== *)

Definition Mconjtrans (m: Matrix): Matrix :=
  {|
    Mbits := Mbits m;
    Minner := fun i j => Cconj (Minner m j i);
  |}.

Lemma Mconjtrans_bits: forall (m: Matrix), MMeqbits (Mconjtrans m) m.
Proof. reflexivity. Qed.

Lemma Mconjtrans_correct: forall (m: Matrix) (i j: nat) (Hi: _) (Hi': _) (Hj: _) (Hj': _),
  (Mconjtrans m)[[i Hi|j Hj]] = Cconj(m[[j Hj'|i Hi']]).
Proof.
  unfold Mtranspose.
  unfold Mget.
  intros.
  reflexivity.
Qed.

Lemma Mconjtrans_mult: forall (m1 m2: Matrix) (H12: _) (H21: _),
  Mconjtrans (Mmult m1 m2 H12) = Mmult (Mconjtrans m2) (Mconjtrans m1) H21.
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    repeat rewrite Mmult_bits_l.
    repeat rewrite Mconjtrans_bits.
    repeat rewrite Mmult_bits_l.
    apply H12.
  - intros.
    unfold Mget.
    simpl.
    unfold Mmult_inner.
    unfold extract_row_unsafe.
    unfold extract_col_unsafe.
    unfold RVsize.
    unfold Msize.
    simpl.
    rewrite H12.
    apply dot_product_suppl_conj2.
Qed.

(* ============================================================================================== *)
(* conjugate transpose of a vector ============================================================== *)

Definition RVconjtrans (r: RowVec): ColVec :=
  {|
    CVbits := RVbits r;
    CVinner :=  fun i => Cconj (RVinner r i);
  |}.

Lemma RVconjtrans_bits: forall (r: RowVec), CReqbits (RVconjtrans r) r.
Proof. reflexivity. Qed.

Definition CVconjtrans (c: ColVec): RowVec :=
  {|
    RVbits := CVbits c;
    RVinner :=  fun i => Cconj (CVinner c i);
  |}.

Lemma CVconjtrans_bits: forall (c: ColVec), RCeqbits (CVconjtrans c) c.
Proof. reflexivity. Qed.

(* ============================================================================================== *)
(* trace ======================================================================================== *)

Fixpoint Mtrace_suppl (m: nat -> nat -> C) (idx: nat): C.
Proof.
  destruct idx as [|idx'].
  - exact O.
  - apply (m idx' idx' + Mtrace_suppl m idx').
Defined.

Definition Mtrace (m: Matrix): C := Mtrace_suppl (Minner m) (Msize m).

(* ============================================================================================== *)
(* identity matrix ============================================================================== *)

Definition eye (bits: nat): Matrix :=
  {|
    Mbits := bits;
    Minner := fun i j => if i =? j then 1 else 0;
  |}.

Lemma eye_bits: forall (bits: nat), Mbits (eye bits) = bits.
Proof. reflexivity. Qed.

Fact Mmult_eye_r_suppl: forall (j l: nat) (f: nat -> C),
  j < l -> dot_product_suppl f (fun i0 => if i0 =? j then 1 else 0) l = f j.
Proof.
  intros.
  induction l as [|l'].
  - intros.
    lia.
  - intros.
    destruct (lt_dec j l') as [Hl|Hl].
    + simpl.
      assert (l' =? j = false).
      { apply Nat.eqb_neq. lia. }
      rewrite H0.
      rewrite Cmult_0_r.
      rewrite Cplus_0_l.
      apply IHl'.
      apply Hl.
    + simpl.
      assert (l' = j) as Hj.
      { destruct (lt_eq_lt_dec j l') as [ [Hj|Hj]|Hj]. lia. lia. lia. }
      replace (l' =? j) with true.
      subst l'.
      assert (forall n, n >= j -> dot_product_suppl f (fun i0 : nat => if i0 =? n then 1 else 0) j = 0).
      { clear.
        induction j as [|j'].
        - reflexivity.
        - intros.
          simpl.
          replace (j' =? n) with false.
          rewrite Cmult_0_r.
          rewrite Cplus_0_l.
          apply IHj'.
          lia.
          symmetry.
          apply <- Nat.eqb_neq.
          lia. }
      specialize H0 with j.
      assert (dot_product_suppl f (fun i0 : nat => if i0 =? j then 1 else 0) j = 0).
      { apply H0. lia. }
      rewrite H1.
      lca.
      symmetry.
      apply <- Nat.eqb_eq.
      apply Hj.
Qed.

Fact Mmult_eye_l_suppl: forall (i l: nat) (f: nat -> C),
  i < l -> dot_product_suppl (fun j0 => if i =? j0 then 1 else 0) f l = f i.
Proof.
  intros.
  induction l as [|l'].
  - intros.
    lia.
  - intros.
    destruct (lt_dec i l') as [Hl|Hl].
    + simpl.
      assert (i =? l' = false).
      { apply Nat.eqb_neq. lia. }
      rewrite H0.
      rewrite Cmult_0_l.
      rewrite Cplus_0_l.
      apply IHl'.
      apply Hl.
    + simpl.
      assert (l' = i) as Hj.
      { destruct (lt_eq_lt_dec i l') as [ [Hj|Hj]|Hj]. lia. lia. lia. }
      replace (l' =? i) with true.
      subst l'.
      assert (forall n, n >= i -> dot_product_suppl (fun i0 : nat => if n =? i0 then 1 else 0) f i = 0).
      { clear.
        induction i as [|i'].
        - reflexivity.
        - intros.
          simpl.
          replace (n =? i') with false.
          rewrite Cmult_0_l.
          rewrite Cplus_0_l.
          apply IHi'.
          lia.
          symmetry.
          apply <- Nat.eqb_neq.
          lia. }
      specialize H0 with i.
      assert (dot_product_suppl (fun j0 : nat => if i =? j0 then 1 else 0) f i = 0).
      { apply H0. lia. }
      rewrite H1.
      rewrite Nat.eqb_refl.
      lca.
      symmetry.
      apply <- Nat.eqb_eq.
      apply Hj.
Qed.

Lemma Mmult_eye_r: forall (m: Matrix) (Hme: _),Mmult m (eye (Mbits m)) Hme = m.
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    rewrite Mmult_bits_r.
    apply eye_bits.
  - intros.
    unfold Mget.
    unfold Mmult.
    unfold Mmult_inner.
    simpl.
    apply Mmult_eye_r_suppl.
    apply H0.
Qed.

Lemma Mmult_eye_l: forall (m: Matrix) (Hem: _), Mmult (eye (Mbits m)) m Hem = m.
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    rewrite Mmult_bits_r.
    apply eye_bits.
  - intros.
    unfold Mget.
    unfold Mmult.
    unfold Mmult_unsafe.
    unfold Mmult_inner.
    simpl.
    rewrite Mmult_eye_l_suppl.
    reflexivity.
    replace (Msize (eye (Mbits m))) with (Msize m).
    + unfold Msize in *;
      repeat rewrite Mmult_bits_l in *;
      repeat rewrite Mconjtrans_bits in *;
      repeat rewrite eye_bits in *.
      apply H.
    + unfold Msize in *;
      repeat rewrite Mmult_bits_l in *;
      repeat rewrite Mconjtrans_bits in *;
      repeat rewrite eye_bits in *.
      reflexivity.
Qed.

(* ============================================================================================== *)
(* tactic of simplifying bits =================================================================== *)

Ltac simpl_bits :=
  unfold MMeqbits in *;
  unfold Msize in *;
  repeat rewrite Mmult_bits_l in *;
  repeat rewrite Mconjtrans_bits in *;
  repeat rewrite eye_bits in *.

(* ============================================================================================== *)
(* ring ========================================================================================= *)

(* Definition M_inner_Ring (bits: nat): Ring_theory.ring_theory (Mzero bits) (eye bits) (Mplus




Czero Cone Cplus Cmult Cminus Copp eq. *)

(* ============================================================================================== *)
