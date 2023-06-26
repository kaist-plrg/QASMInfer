Require Export Complex.
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

Definition pow_2 n := Nat.pow 2 n.

Definition Msize (m: Matrix): nat := pow_2 (Mbits m).

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

Definition RVsize (r: RowVec): nat := pow_2 (RVbits r).
Definition CVsize (c: ColVec): nat := pow_2 (CVbits c).

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

Axiom RVequal: forall (r1 r2: RowVec),
  RVbits r1 = RVbits r2 -> (forall i, i < RVsize r1 -> i < RVsize r2 -> RVinner r1 i = RVinner r2 i) -> r1 = r2.

Axiom CVequal: forall (c1 c2: ColVec),
  CVbits c1 = CVbits c2 -> (forall i, i < CVsize c1 -> i < CVsize c2 -> CVinner c1 i = CVinner c2 i) -> c1 = c2.

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

Definition dot_product_suppl (r c: nat -> C) (idx: nat): C :=
  func_sum (fun i => r i * c i) idx.

Ltac dps_unfold :=
  unfold dot_product_suppl;
  unfold func_sum;
  unfold func_sum2;
  repeat rewrite Nat.sub_0_r.

Lemma dot_product_suppl_scale_l: forall (l: nat) (c: C) (f1 f2 f: nat -> C),
  (forall n, f1 n = c * f2 n) -> dot_product_suppl f1 f l = c * dot_product_suppl f2 f l.
Proof.
  intros.
  dps_unfold.
  induction l as [|l'].
  - lca.
  - unfold dot_product_suppl.
    simpl.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_scale_r: forall (l: nat) (c: C) (f1 f2 f: nat -> C),
  (forall n, f1 n = c * f2 n) -> dot_product_suppl f f1 l = c * dot_product_suppl f f2 l.
Proof.
  intros.
  dps_unfold.
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
  dps_unfold.
  induction l as [|l'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    lca.
Qed.

Lemma func_sum_suppl_dist: forall (n m: nat) (f1 f2 f12: nat -> C),
  (forall i, f12 i = f1 i + f2 i) -> func_sum_suppl f12 n m = func_sum_suppl f1 n m + func_sum_suppl f2 n m.
Proof.
  intros.
  induction m as [|m'].
  - lca.
  - simpl.
    rewrite IHm'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_plus_l: forall (l: nat) (f f1 f2 f12: nat -> C),
  (forall n, f12 n = f1 n + f2 n) -> dot_product_suppl f12 f l = dot_product_suppl f1 f l + dot_product_suppl f2 f l.
Proof.
  intros.
  dps_unfold.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    ring_simplify.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_plus_r: forall (l: nat) (f f1 f2 f12: nat -> C),
  (forall n, f12 n = f1 n + f2 n) -> dot_product_suppl f f12 l = dot_product_suppl f f1 l + dot_product_suppl f f2 l.
Proof.
  intros.
  dps_unfold.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    ring_simplify.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_minus_l: forall (l: nat) (f f1 f2 f12: nat -> C),
  (forall n, f12 n = f1 n - f2 n) -> dot_product_suppl f12 f l = dot_product_suppl f1 f l - dot_product_suppl f2 f l.
Proof.
  intros.
  dps_unfold.
  induction l as [|l'].
  - simpl. lca.
  - simpl.
    ring_simplify.
    rewrite IHl'.
    rewrite H.
    lca.
Qed.

Lemma dot_product_suppl_minus_r: forall (l: nat) (f f1 f2 f12: nat -> C),
  (forall n, f12 n = f1 n - f2 n) -> dot_product_suppl f f12 l = dot_product_suppl f f1 l - dot_product_suppl f f2 l.
Proof.
  intros.
  dps_unfold.
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
  dps_unfold.
  induction l as [|l'].
  - reflexivity.
  - simpl.
    specialize func_sum_suppl_dist with
      (f1 := fun i => (f1 l' * f2 l' i) * f3 i)
      (f2 := fun i => (func_sum_suppl (fun i0 : nat => f1 i0 * f2 i0 i) 0 l') * f3 i)
      (f12 := fun i => (f1 l' * f2 l' i + func_sum_suppl (fun i0 : nat => f1 i0 * f2 i0 i) 0 l') * f3 i)
      as Hdist1.
    specialize func_sum_suppl_dist with
      (f1 := fun i => f1 i * (f2 i l' * f3 l'))
      (f2 := fun i => f1 i * func_sum_suppl (fun i0 : nat => f2 i i0 * f3 i0) 0 l')
      (f12 := fun i => f1 i * (f2 i l' * f3 l' + func_sum_suppl (fun i0 : nat => f2 i i0 * f3 i0) 0 l'))
      as Hdist2.
    rewrite Hdist1.
    rewrite Hdist2.
    rewrite IHl'.
    specialize func_sum_suppl_scale with
    (f1 := fun i : nat => f1 l' * f2 l' i * f3 i)
    (f2 := fun i : nat => f2 l' i * f3 i)
    (c := f1 l') as Hscale1.
    specialize func_sum_suppl_scale with
    (f1 := fun i => f1 i * (f2 i l' * f3 l'))
    (f2 := fun i => f1 i * f2 i l')
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
  dps_unfold.
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
  dps_unfold.
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
  dps_unfold.
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

Lemma dot_product_suppl_ge0: forall (l: nat) (f: nat -> C),
  Cge_0 (dot_product_suppl (fun i => Cconj (f i)) f l).
Proof.
  intros.
  dps_unfold.
  split.
  - induction l.
    + simpl.
      lra.
    + simpl in *.
      apply Rle_ge.
      apply Rplus_le_le_0_compat.
      * nra.
      * apply Rge_le.
        apply IHl.
  - induction l.
    + simpl.
      lra.
    + simpl in *.
      unfold Cimag in IHl.
      lra.
Qed.

Definition dot_product_unsafe (r: RowVec) (c: ColVec): C :=
  dot_product_suppl (RVinner r) (CVinner c) (RVsize r).

Definition dot_product (r: RowVec) (c: ColVec) (Hrc: RCeqbits r c): C := dot_product_unsafe r c.

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

Lemma Msmul_correct: forall
  (s: C) (m: Matrix) (i j: nat)
  (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  (Msmul s m)[[i H2i|j H2j]] = (Cmult s) (m[[i H1i|j H1j]]).
Proof. intro s. apply Muop_correct. Qed.

Lemma Msmul_bits: forall (s: C) (m: Matrix), MMeqbits (Msmul s m) m.
Proof.
  unfold Msmul.
  intros.
  apply Muop_bits.
Qed.

(* ============================================================================================== *)
(* element-wise binary operation ================================================================ *)

Definition Mbop_unsafe (bop: C -> C -> C) (m1 m2: Matrix): Matrix :=
  {|
    Mbits := Mbits m1;
    Minner := fun i j => bop (Minner m1 i j) (Minner m2 i j)
  |}.

Lemma Mbop_unsafe_bits_l: forall (bop: C -> C -> C) (m1 m2: Matrix),
  MMeqbits (Mbop_unsafe bop m1 m2) m1.
Proof. reflexivity. Qed.

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: MMeqbits m1 m2): Matrix :=
  Mbop_unsafe bop m1 m2.

Lemma Mbop_bits_l: forall (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: _),
  MMeqbits (Mbop bop m1 m2 Hbits) m1.
Proof. reflexivity. Qed.

Lemma Mbop_bits_r: forall (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: _),
  MMeqbits (Mbop bop m1 m2 Hbits) m2.
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

Lemma Mplus_bits_l: forall (m1 m2: Matrix) (Hbits: _), MMeqbits (Mplus m1 m2 Hbits) m1.
Proof. apply Mbop_bits_l. Qed.

Lemma Mplus_bits_r: forall (m1 m2: Matrix) (Hbits: _), MMeqbits (Mplus m1 m2 Hbits) m2.
Proof. apply Mbop_bits_r. Qed.

Lemma Mplus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  (Mplus m1 m2 Hbits)[[i H3i|j H3j]] = Cplus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof. apply Mbop_correct. Qed.

Lemma Mplus_comm: forall (m1 m2: Matrix) (H1: _) (H2: _), Mplus m1 m2 H1 = Mplus m2 m1 H2.
Proof.
  intros.
  apply Mequal.
  - repeat rewrite Mplus_bits_l.
    apply H1.
  - unfold Mplus, Mbop_unsafe.
    intros.
    lca.
Qed.

(* ============================================================================================== *)
(* matrix subtraction =========================================================================== *)

Definition Mminus (m1 m2: Matrix) (Hbits: MMeqbits m1 m2) := Mbop_unsafe Cminus m1 m2.

Lemma Mminus_bits_l: forall (m1 m2: Matrix) (Hbits: _), MMeqbits (Mminus m1 m2 Hbits) m1.
Proof. apply Mbop_bits_l. Qed.

Lemma Mminus_bits_r: forall (m1 m2: Matrix) (Hbits: _), MMeqbits (Mminus m1 m2 Hbits) m2.
Proof. apply Mbop_bits_r. Qed.

Lemma Mminus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  (Mminus m1 m2 Hbits)[[i H3i|j H3j]] = Cminus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof. apply Mbop_correct. Qed.

Lemma Mplus_Mminus_eq_l: forall (m1 m2 m3: Matrix) (H12: _) (H32: _),
  Mplus m1 m2 H12 = m3 <-> m1 = Mminus m3 m2 H32.
Proof.
  split.
  - intros.
    apply Mequal.
    + rewrite Mminus_bits_r.
      apply H12.
    + intros.
      unfold Mplus, Mminus, Mbop_unsafe in *.
      subst m3.
      simpl in *.
      lca.
  - intros.
    apply Mequal.
    + rewrite Mplus_bits_r.
      symmetry.
      apply H32.
    + intros.
      unfold Mplus, Mminus, Mbop_unsafe in *.
      subst m1.
      simpl in *.
      lca.
Qed.

Lemma Mplus_Mminus_eq_r: forall (m1 m2 m3: Matrix) (H12: _) (H31: _),
  Mplus m1 m2 H12 = m3 <-> m2 = Mminus m3 m1 H31.
Proof.
  split.
  - intros.
    apply Mequal.
    + rewrite Mminus_bits_r.
      symmetry.
      apply H12.
    + intros.
      unfold Mplus, Mminus, Mbop_unsafe in *.
      subst m3.
      simpl in *.
      lca.
  - intros.
    apply Mequal.
    + rewrite Mplus_bits_l.
      symmetry.
      apply H31.
    + intros.
      unfold Mplus, Mminus, Mbop_unsafe in *.
      subst m2.
      simpl in *.
      lca.
Qed.

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

Lemma Mmult_unsafe_bits_l: forall (m1 m2: Matrix), MMeqbits (Mmult_unsafe m1 m2) m1.
Proof. reflexivity. Qed.

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

Lemma Mmult_dist_plus_l: forall (m1 m2 m3: Matrix) (H12: _) (H12_3: _) (H13: _) (H23: _) (H1323: _),
  (Mmult (Mplus m1 m2 H12) m3 H12_3) = Mplus (Mmult m1 m3 H13) (Mmult m2 m3 H23) H1323.
Proof.
  intros.
  apply Mequal.
  - repeat (repeat rewrite Mmult_bits_l; repeat rewrite Mplus_bits_l).
    reflexivity.
  - intros.
    unfold Mmult, Mmult_unsafe, Mmult_inner, Mplus, Mbop_unsafe, Msize.
    simpl.
    repeat rewrite H12.
    apply dot_product_suppl_plus_l.
    intros.
    lca.
Qed.

Lemma Mmult_dist_plus_r: forall (m1 m2 m3: Matrix) (H23: _) (H1_23: _) (H12: _) (H13: _) (H1213: _),
  (Mmult m1 (Mplus m2 m3 H23) H1_23) = Mplus (Mmult m1 m2 H12) (Mmult m1 m3 H13) H1213.
Proof.
  intros.
  apply Mequal.
  - repeat (repeat rewrite Mmult_bits_l; repeat rewrite Mplus_bits_l).
    reflexivity.
  - intros.
    unfold Mmult, Mmult_unsafe, Mmult_inner, Mplus, Mbop_unsafe, Msize.
    simpl.
    repeat rewrite H12.
    apply dot_product_suppl_plus_r.
    intros.
    lca.
Qed.

Lemma Mmult_dist_minus_l: forall (m1 m2 m3: Matrix) (H12: _) (H12_3: _) (H13: _) (H23: _) (H1323: _),
  (Mmult (Mminus m1 m2 H12) m3 H12_3) = Mminus (Mmult m1 m3 H13) (Mmult m2 m3 H23) H1323.
Proof.
  intros.
  apply Mequal.
  - repeat (repeat rewrite Mmult_bits_l; repeat rewrite Mplus_bits_l).
    reflexivity.
  - intros.
    unfold Mmult, Mmult_unsafe, Mmult_inner, Mminus, Mbop_unsafe, Msize.
    simpl.
    repeat rewrite H12.
    apply dot_product_suppl_minus_l.
    intros.
    lca.
Qed.

Lemma Mmult_dist_minus_r: forall (m1 m2 m3: Matrix) (H23: _) (H1_23: _) (H12: _) (H13: _) (H1213: _),
  (Mmult m1 (Mminus m2 m3 H23) H1_23) = Mminus (Mmult m1 m2 H12) (Mmult m1 m3 H13) H1213.
Proof.
  intros.
  apply Mequal.
  - repeat (repeat rewrite Mmult_bits_l; repeat rewrite Mplus_bits_l).
    reflexivity.
  - intros.
    unfold Mmult, Mmult_unsafe, Mmult_inner, Mminus, Mbop_unsafe, Msize.
    simpl.
    repeat rewrite H12.
    apply dot_product_suppl_minus_r.
    intros.
    lca.
Qed.

Lemma Mmult_smul_comm_l: forall (m1 m2: Matrix) (c: C) H1 H2,
  Mmult (Msmul c m1) m2 H1 =  Msmul c (Mmult m1 m2 H2).
Proof.
  intros.
  unfold Mmult, Msmul, Mmult_unsafe, Muop, Msize.
  simpl.
  apply Mequal.
  - reflexivity.
  - unfold Msize.
    simpl.
    intros.
    unfold Mmult_inner, extract_row_unsafe, extract_col_unsafe, Msize.
    simpl.
    apply dot_product_suppl_scale_l.
    intros.
    reflexivity.
Qed.

(* ============================================================================================== *)
(* matrix-vector multiplication ================================================================= *)

Definition MVmult_inner (m: Matrix) (c: ColVec) (i: nat): C :=
  dot_product_suppl (RVinner (extract_row_unsafe m i)) (CVinner c) (CVsize c).

Definition MVmult_unsafe (m: Matrix) (c: ColVec): ColVec :=
  {|
    CVbits := CVbits c;
    CVinner := fun i => MVmult_inner m c i;
  |}.

Lemma MVmult_unsafe_bits_l: forall (m: Matrix) (c: ColVec), CCeqbits (MVmult_unsafe m c) c.
Proof.
  intros.
  unfold CCeqbits.
  simpl.
  reflexivity.
Qed.

Definition MVmult (m: Matrix) (c: ColVec) (H: MCeqbits m c): ColVec := MVmult_unsafe m c.

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
  unfold MVmult_inner, dot_product_unsafe.
  unfold RVsize.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma MMVmult_assoc: forall (m1 m2: Matrix) (c3: ColVec)
  (H12: _) (H12_3: _) (H23: _) (H1_23: _),
  MVmult (Mmult m1 m2 H12) c3 H12_3 = MVmult m1 (MVmult m2 c3 H23) H1_23.
Proof.
  intros.
  apply CVequal.
  - unfold CCeqbits.
    simpl.
    rewrite <- H12_3.
    reflexivity.
  - intros.
    unfold CVget.
    simpl.
    unfold Mmult, MVmult, MVmult_unsafe, Mmult_inner, MVmult_inner, extract_row_unsafe,
      CVsize, RVsize, Msize.
    simpl in *.
    replace (CVbits c3) with (Mbits m1).
    apply dot_product_suppl_assoc.
Qed.

(* Lemma MVmult_dist: forall (m1 m2: Matrix) (c: ColVec) H Hm12c Hm1c Hm2c,
  MVmult (Mplus m1 m2 H) c Hm12c = Mplus (MVmult m1 c Hm1c) (MVmult m2 c Hm2c). *)

(* ============================================================================================== *)
(* vector-matrix multiplication ================================================================= *)


Definition VMmult_inner (r: RowVec) (m: Matrix) (j: nat): C :=
  dot_product_suppl (RVinner r) (CVinner (extract_col_unsafe m j)) (RVsize r).

Definition VMmult_unsafe (r: RowVec) (m: Matrix): RowVec :=
  {|
    RVbits := RVbits r;
    RVinner := fun j => VMmult_inner r m j;
  |}.

Definition VMmult (r: RowVec) (m: Matrix) (H: RMeqbits r m): RowVec := VMmult_unsafe r m.

Lemma VMmult_bits_l: forall (r: RowVec) (m: Matrix) (H: RMeqbits r m), RReqbits (VMmult r m H) r.
Proof. reflexivity. Qed.

Lemma VMmult_bits_r: forall (r: RowVec) (m: Matrix) (H: RMeqbits r m), RMeqbits (VMmult r m H) m.
Proof.
  intros.
  unfold RMeqbits, VMmult.
  simpl.
  apply H.
Qed.

Lemma VMmult_correct: forall (m: Matrix) (r r': RowVec) (c: ColVec) (j: nat)
  (Hj: _) (H: _) (Hri: _) (Hrc: _),
  RVget (VMmult r m H) j Hri = dot_product r (extract_col m j Hj) Hrc.
Proof.
  intros.
  unfold RVget, dot_product, MVmult_inner, RVsize.
  simpl.
  reflexivity.
Qed.

Lemma VMMmult_assoc: forall (r1: RowVec) (m3 m2: Matrix)
  (H12: _) (H12_3: _) (H23: _) (H1_23: _),
  VMmult (VMmult r1 m2 H12) m3 H12_3 = VMmult r1 (Mmult m2 m3 H23) H1_23.
Proof.
  intros.
  apply RVequal.
  - unfold RReqbits.
    simpl.
    rewrite H12_3.
    reflexivity.
  - intros.
    unfold RVget. simpl.
    repeat unfold Mmult, Mmult_inner, VMmult, VMmult_inner, VMmult_unsafe, extract_col_unsafe, CVsize, RVsize.
    simpl in *.
    replace (RVbits r1) with (Mbits m2).
    apply dot_product_suppl_assoc.
Qed.

Lemma dot_product_Mmult_assoc: forall (r: RowVec) (m: Matrix) (c: ColVec) (Hrm: _) (H1: _) (Hmc: _) (H2: _),
  dot_product (VMmult r m Hrm) c H1 = dot_product r (MVmult m c Hmc) H2.
Proof.
  intros.
  unfold VMmult, MVmult, dot_product.
  unfold dot_product_unsafe, RVsize; simpl.
  unfold VMmult_inner, MVmult_inner; simpl.
  unfold RVsize, CVsize.
  repeat rewrite Hrm.
  repeat rewrite <- Hmc.
  apply dot_product_suppl_assoc.
Qed.

Lemma VMVmult_assoc: forall
  (m: Matrix) (r: RowVec) (c: ColVec) (Hmc: _) (Hr_mc: _) (Hrm: _) (Hrm_c: _),
  dot_product r (MVmult m c Hmc) Hr_mc = dot_product (VMmult r m Hrm) c Hrm_c.
Proof.
  intros.
  unfold MVmult, VMmult, dot_product, dot_product_unsafe, MVmult_unsafe, VMmult_unsafe,
    VMmult_inner, MVmult_inner, RVsize, CVsize, pow_2.
  simpl.
  unfold dot_product_suppl.
  repeat rewrite <- Hmc.
  repeat rewrite Hrm.
  replace (
    (fun i => RVinner r i * func_sum (fun i0 => Minner m i i0 * CVinner c i0) (2 ^ Mbits m))
  ) with (
    (fun i => func_sum (fun i0 => RVinner r i * Minner m i i0 * CVinner c i0) (2 ^ Mbits m))
  ).
  replace (
    (fun i => func_sum (fun i0 => RVinner r i0 * Minner m i0 i) (2 ^ Mbits m) * CVinner c i)
  ) with (
    (fun i => func_sum (fun i0 => RVinner r i0 * Minner m i0 i * CVinner c i) (2 ^ Mbits m))
  ).
  rewrite func_sum_comm.
  replace (
    (fun i => func_sum (fun j => CVinner c i * (RVinner r j * Minner m j i)) (2 ^ Mbits m))
  ) with (
    (fun i => func_sum (fun i0 => RVinner r i0 * Minner m i0 i * CVinner c i) (2 ^ Mbits m))
  ).
  reflexivity.
  apply functional_extensionality.
  intros i.
  replace (
    fun i0 : nat => RVinner r i0 * Minner m i0 i * CVinner c i
  ) with (
    fun j : nat => CVinner c i * (RVinner r j * Minner m j i)
  ).
  reflexivity.
  apply functional_extensionality.
  intros.
  lca.
  apply functional_extensionality.
  intros.
  rewrite Cmult_comm.
  unfold func_sum, func_sum2.
  apply func_sum_suppl_scale.
  intros.
  lca.
  apply functional_extensionality.
  intros.
  unfold func_sum, func_sum2.
  apply func_sum_suppl_scale.
  intros.
  lca.
Qed.

(* ============================================================================================== *)
(* vector-vector multiplication (outer product) ================================================= *)

Definition VVmult_unsafe (c: ColVec) (r: RowVec): Matrix :=
  {|
    Mbits := CVbits c;
    Minner := fun i j => CVinner c i * RVinner r j;
  |}.

Definition VVmult (c: ColVec) (r: RowVec) (H: CReqbits c r): Matrix := VVmult_unsafe c r.

Lemma VVmult_bits_l: forall (c: ColVec) (r: RowVec) (H: _), MCeqbits (VVmult c r H) c.
Proof. reflexivity. Qed.

Lemma VVmult_bits_r: forall (c: ColVec) (r: RowVec) (H: _), MReqbits (VVmult c r H) r.
Proof.
  intros.
  simpl.
  apply H.
Qed.

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

Lemma Mconjtrans_plus: forall (m1 m2: Matrix) (H12: _) (H21: _),
  Mconjtrans (Mplus m1 m2 H12) = Mplus (Mconjtrans m1) (Mconjtrans m2) H21.
Proof.
  intros.
  apply Mequal.
  - repeat rewrite Mconjtrans_bits.
    repeat rewrite Mplus_bits_l.
    symmetry.
    apply Mconjtrans_bits.
  - simpl.
    intros.
    apply Cconj_plus.
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

Lemma Mconjtrans_twice: forall (m: Matrix),
  Mconjtrans (Mconjtrans m) = m.
Proof.
  intros.
  apply Mequal.
  - reflexivity.
  - intros.
    unfold Mconjtrans, Minner.
    apply Cconj_twice.
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

Lemma RVconjtrans_mult: forall (r: RowVec) (m: Matrix) (H1: _) (H2: _),
  RVconjtrans (VMmult r m H1) = MVmult (Mconjtrans m) (RVconjtrans r) H2.
Proof.
  intros.
  apply CVequal.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    unfold MVmult_inner, VMmult_inner, RVconjtrans, Mconjtrans.
    simpl.
    unfold CVsize, RVsize.
    simpl.
    rewrite dot_product_suppl_comm.
    apply dot_product_suppl_conj1.
Qed.

Definition CVconjtrans (c: ColVec): RowVec :=
  {|
    RVbits := CVbits c;
    RVinner :=  fun i => Cconj (CVinner c i);
  |}.

Lemma CVconjtrans_bits: forall (c: ColVec), RCeqbits (CVconjtrans c) c.
Proof. reflexivity. Qed.

Lemma CVconjtrans_mult: forall (m: Matrix) (c: ColVec) (H1: _) (H2: _),
  CVconjtrans (MVmult m c H1) = VMmult (CVconjtrans c) (Mconjtrans m) H2.
Proof.
  intros.
  apply RVequal.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    unfold MVmult_inner, VMmult_inner, CVconjtrans, Mconjtrans.
    simpl.
    unfold CVsize, RVsize.
    simpl.
    rewrite dot_product_suppl_comm.
    apply dot_product_suppl_conj1.
Qed.

Lemma CRVconjtrans_twice: forall (c: ColVec), RVconjtrans (CVconjtrans c) = c.
Proof.
  intros.
  apply CVequal.
  - rewrite RVconjtrans_bits.
    apply CVconjtrans_bits.
  - intros.
    unfold RVconjtrans, CVconjtrans.
    simpl.
    apply Cconj_twice.
Qed.

Lemma RCVconjtrans_twice: forall (r: RowVec), CVconjtrans (RVconjtrans r) = r.
Proof.
  intros.
  apply RVequal.
  - rewrite CVconjtrans_bits.
    apply RVconjtrans_bits.
  - intros.
    unfold RVconjtrans, CVconjtrans.
    simpl.
    apply Cconj_twice.
Qed.

Lemma CVconjtrans_ge0: forall (c: ColVec) (H: _), Cge_0 (dot_product (CVconjtrans c) c H).
Proof.
  intros.
  unfold dot_product, dot_product_unsafe, CVconjtrans, RVsize.
  simpl.
  apply dot_product_suppl_ge0.
Qed.

Lemma dot_product_conjtrans: forall (r: RowVec) (c: ColVec) (H1: _) (H2: _),
  Cconj (dot_product r c H1) = dot_product (CVconjtrans c) (RVconjtrans r) H2.
Proof.
  intros.
  unfold dot_product, dot_product_unsafe, RVsize, RVconjtrans, CVconjtrans.
  repeat rewrite CVconjtrans_bits.
  simpl.
  repeat rewrite H1.
  rewrite dot_product_suppl_conj2.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* trace ======================================================================================== *)

Definition Mtrace (m: Matrix): C := func_sum (fun i => Minner m i i) (Msize m).

Lemma Mtrace_Mmult_comm: forall (m1 m2: Matrix) (H1: _) (H2: _),
  Mtrace (Mmult m1 m2 H1) = Mtrace (Mmult m2 m1 H2).
Proof.
  intros.
  unfold Mmult, Mmult_unsafe, Mmult_inner, dot_product_suppl, Mtrace, Msize in *.
  repeat rewrite H1.
  simpl.
  apply func_sum_comm_mat.
Qed.


Lemma Mtrace_Mplus_dist: forall (m1 m2: Matrix) (H: _),
  Mtrace (Mplus m1 m2 H) = Mtrace m1 + Mtrace m2.
Proof.
  intros.
  unfold Mplus, Mbop_unsafe, Mtrace, Msize, func_sum, func_sum2 in *.
  repeat rewrite Nat.sub_0_r.
  repeat rewrite H.
  simpl.
  apply func_sum_suppl_add.
  reflexivity.
Qed.

Lemma Mtrace_Mminus_dist: forall (m1 m2: Matrix) (H: _),
  Mtrace (Mminus m1 m2 H) = Mtrace m1 - Mtrace m2.
Proof.
  intros.
  unfold Mminus, Mbop_unsafe, Mtrace, Msize, func_sum, func_sum2 in *.
  repeat rewrite Nat.sub_0_r.
  repeat rewrite H.
  simpl.
  apply func_sum_suppl_sub.
  reflexivity.
Qed.

Lemma Mtrace_Msmul: forall (m: Matrix) (c: C),
  Mtrace (Msmul c m) = c * Mtrace m.
Proof.
  intros.
  unfold Msmul, Muop, Mtrace, Msize, func_sum, func_sum2.
  simpl.
  apply func_sum_suppl_scale.
  intros.
  reflexivity.
Qed.

Lemma Mtrace_Cconj: forall (m: Matrix), Cconj (Mtrace m) = Mtrace (Mconjtrans m).
Proof.
  intros.
  unfold Mtrace, Msize, func_sum, func_sum2, Mconjtrans in *.
  simpl.
  rewrite Nat.sub_0_r.
  apply func_sum_suppl_conj with (f2 := (fun i : nat => Cconj (Minner m i i))).
  intros.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* identity matrix ============================================================================== *)

Definition eye (bits: nat): Matrix :=
  {|
    Mbits := bits;
    Minner := fun i j => if i =? j then 1 else 0;
  |}.

Lemma eye_bits: forall (bits: nat), Mbits (eye bits) = bits.
Proof. reflexivity. Qed.

Lemma eye_conjtrans: forall (bits: nat), Mconjtrans (eye bits) = eye bits.
Proof.
  intros.
  unfold eye, Mconjtrans.
  simpl.
  apply Mequal.
  - reflexivity.
  - unfold Msize, Cconj.
    simpl.
    intros.
    apply c_proj_eq.
    + simpl.
      rewrite Nat.eqb_sym.
      reflexivity.
    + rewrite Nat.eqb_sym.
      unfold NTC.
      simpl.
      destruct (i =? j).
      * simpl. lra.
      * simpl. lra.
Qed.

Fact Mmult_eye_r_suppl: forall (j l: nat) (f: nat -> C),
  j < l -> dot_product_suppl f (fun i0 => if i0 =? j then 1 else 0) l = f j.
Proof.
  intros.
  dps_unfold.
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
      assert (forall n, n >= j -> func_sum_suppl (fun i : nat => f i * (if i =? n then 1 else 0)) 0 j = 0).
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
      assert (func_sum_suppl (fun i : nat => f i * (if i =? j then 1 else 0)) 0 j = 0).
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
  dps_unfold.
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
      assert (forall n, n >= i -> func_sum_suppl (fun i0 : nat => (if n =? i0 then 1 else 0) * f i0) 0 i = 0).
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
      assert (func_sum_suppl (fun i0 : nat => (if i =? i0 then 1 else 0) * f i0) 0 i = 0).
      { apply H0. lia. }
      rewrite H1.
      rewrite Nat.eqb_refl.
      lca.
      symmetry.
      apply <- Nat.eqb_eq.
      apply Hj.
Qed.

Lemma Mmult_eye_r: forall (m: Matrix) (n: nat) (Hme: _),
  n = Mbits m -> Mmult m (eye n) Hme = m.
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    rewrite Mmult_bits_r.
    rewrite eye_bits.
    lia.
  - intros.
    unfold Mget, Mmult, Mmult_inner.
    simpl.
    apply Mmult_eye_r_suppl.
    apply H1.
Qed.

Lemma Mmult_eye_l: forall (m: Matrix) (n: nat) (Hem: _),
  n = Mbits m -> Mmult (eye n) m Hem = m.
Proof.
  intros.
  apply Mequal.
  - unfold MMeqbits.
    rewrite Mmult_bits_r.
    apply eye_bits.
  - intros.
    unfold Mget, Mmult, Mmult_unsafe, Mmult_inner.
    simpl.
    rewrite Mmult_eye_l_suppl.
    reflexivity.
    replace (Msize (eye (Mbits m))) with (Msize m).
    + unfold Msize in *;
      repeat rewrite Mmult_bits_l in *;
      repeat rewrite Mconjtrans_bits in *;
      repeat rewrite eye_bits in *.
      apply H0.
    + unfold Msize in *;
      repeat rewrite Mmult_bits_l in *;
      repeat rewrite Mconjtrans_bits in *;
      repeat rewrite eye_bits in *.
      reflexivity.
Qed.

Lemma MVmult_eye: forall (c: ColVec) (Hec: _), MVmult (eye (CVbits c)) c Hec = c.
Proof.
  intros.
  apply CVequal.
  - apply MVmult_bits_r.
  - intros.
    unfold MVmult, MVmult_unsafe, MVmult_inner.
    simpl.
    apply Mmult_eye_l_suppl.
    lia.
Qed.

Lemma VMmult_eye: forall (r: RowVec) (Hre: _), VMmult r (eye (RVbits r)) Hre = r.
Proof.
  intros.
  apply RVequal.
  - apply VMmult_bits_l.
  - intros.
    unfold VMmult, VMmult_unsafe, VMmult_inner.
    simpl.
    apply Mmult_eye_r_suppl.
    lia.
Qed.

Lemma eye_trace_pos: forall n, Cge_0 (Mtrace (eye n)).
Proof.
  assert (forall i, Cge_0 (func_sum (fun i : nat => if i =? i then 1%nat else 0%nat) i)).
  { induction i.
    - split.
      + simpl. lra.
      + simpl. lra.
    - destruct IHi as [Hp Hr].
      split.
      + unfold Creal, func_sum, func_sum2 in *.
        rewrite Nat.sub_0_r in *.
        simpl in *.
        replace (i =? i) with true.
        simpl.
        lra.
        symmetry.
        apply Nat.eqb_eq.
        reflexivity.
      + unfold Cimag, func_sum, func_sum2 in *.
        rewrite Nat.sub_0_r in *.
        simpl in *.
        replace (i =? i) with true.
        simpl.
        lra.
        symmetry.
        apply Nat.eqb_eq.
        reflexivity. }
  intros.
  unfold Mtrace, eye, Msize.
  simpl.
  apply H.
Qed.

(* ============================================================================================== *)
