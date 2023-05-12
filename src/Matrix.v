Require Export Complex.
Import ListNotations.

Declare Scope M_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.

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
(* equality of two matrices ===================================================================== *)

Definition Mequal (m1 m2: Matrix): Prop := forall (i j: nat) (Hi1: _) (Hi2: _) (Hj1: _) (Hj2: _),
(MMeqbits m1 m2) /\ (m1[[i Hi1|j Hj1]] = m2[[i Hi2|j Hj2]]).

(* ============================================================================================== *)
(* get an element from a vector ================================================================= *)

Definition RVget (r : RowVec) (j: nat) (Hj: j < RVsize r): C := RVinner r j.
Definition CVget (c : ColVec) (i: nat) (Hi: i < CVsize c): C := CVinner c i.

(* ============================================================================================== *)
(* extract row and column vectors from a matrix ================================================= *)

Definition extract_row (m: Matrix) (i: nat) (Hi: i < Msize m): {r: RowVec | RMeqbits r m}.
Proof.
  refine (exist _ {|
    RVbits := Mbits m;
    RVinner := fun j => Minner m i j;
    |} _ ).
  reflexivity.
Defined.

Definition extract_col (m: Matrix) (j: nat) (Hj: j < Msize m): {c: ColVec | CMeqbits c m}.
Proof.
  refine (exist _ {|
    CVbits := Mbits m;
    CVinner := fun i => Minner m i j;
    |} _ ).
  reflexivity.
Defined.

Definition extract_row_unsafe (m: Matrix) (i: nat): {r: RowVec | RMeqbits r m}.
Proof.
  refine (exist _ {|
    RVbits := Mbits m;
    RVinner := fun j => Minner m i j;
    |} _ ).
  reflexivity.
Defined.

Definition extract_col_unsafe (m: Matrix) (j: nat): {c: ColVec | CMeqbits c m}.
Proof.
  refine (exist _ {|
    CVbits := Mbits m;
    CVinner := fun i => Minner m i j;
    |} _ ).
  reflexivity.
Defined.

Lemma extract_row_correct: forall
  (m: Matrix) (r: RowVec) (i j: nat) (Hi Hi': _) (Hj: _) (Hr: _) (Hjr: _),
  exist _ r Hr = extract_row m i Hi ->
  RVget r j Hjr = m[[i Hi'|j Hj]].
Proof.
  unfold extract_row.
  intros.
  inversion H.
  unfold RVget.
  unfold Mget.
  rewrite H1.
  simpl.
  reflexivity.
Qed.

Lemma extract_col_correct: forall
  (m: Matrix) (c: ColVec) (i j: nat) (Hi: _) (Hj Hj': _) (Hc: _) (Hic: _),
  exist _ c Hc = extract_col m j Hj ->
  CVget c i Hic = m[[i Hi|j Hj']].
Proof.
  unfold extract_col.
  intros.
  inversion H.
  unfold CVget.
  unfold Mget.
  rewrite H1.
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

(* ============================================================================================== *)
(* element-wise unary operation ================================================================= *)

Definition Muop (uop: C -> C) (m: Matrix): {m': Matrix | MMeqbits m' m}.
Proof.
  refine ( exist _ {|
    Mbits := Mbits m;
    Minner := fun i j => uop (Minner m i j);
    |} _ ).
  reflexivity.
Defined.

Lemma Muop_correct: forall
  (uop: C -> C) (m1 m2: Matrix) (i j: nat)
  (Huop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ m2 Huop = Muop uop m1 ->
  m2[[i H2i|j H2j]] = uop (m1[[i H1i|j H1j]]).
Proof.
  intros.
  inversion H.
  subst m2.
  unfold Mget.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* opposite of a matrix ========================================================================= *)

Definition Mopp (m: Matrix): {m': Matrix | MMeqbits m' m} := Muop Copp m.

Notation "- x" := (Mopp x) : M_scope.

Lemma Mopp_correct: forall
  (m1 m2: Matrix) (i j: nat)
  (Huop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ m2 Huop = Mopp m1 ->
  m2[[i H2i|j H2j]] = Copp (m1[[i H1i|j H1j]]).
Proof.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* scalar multiplication ======================================================================== *)

Definition Msmul (s: C) (m: Matrix): {m': Matrix | MMeqbits m' m} := Muop (Cmult s) m.

Lemma Msuml_correct: forall
  (s: C) (m1 m2: Matrix) (i j: nat)
  (Huop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ m2 Huop = Msmul s m1 -> m2[[i H2i|j H2j]] = (Cmult s) (m1[[i H1i|j H1j]]).
Proof.
  intro s.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* element-wise binary operation ================================================================ *)

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hbits: MMeqbits m1 m2):
  {m: Matrix| MMeqbits m m1}.
Proof.
  refine (exist _ {|
    Mbits := Mbits m1;
    Minner := fun i j => bop (Minner m1 i j) (Minner m2 i j) |} _ ).
  simpl. reflexivity.
Defined.

Lemma Mbop_correct: forall
  (bop: C -> C -> C) (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Mbop bop m1 m2 Hbits ->
  m3[[i H3i|j H3j]] = bop (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  unfold Mbop, Mget.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* matrix addition ============================================================================== *)

Definition Mplus (m1 m2: Matrix) (Hbits: MMeqbits m1 m2) := Mbop Cplus m1 m2 Hbits.

Lemma Mplus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Mplus m1 m2 Hbits ->
  m3[[i H3i|j H3j]] = Cplus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix subtraction =========================================================================== *)

Definition Mminus (m1 m2: Matrix) (Hbits: MMeqbits m1 m2) := Mbop Cminus m1 m2 Hbits.

Lemma Mminus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Mminus m1 m2 Hbits ->
  m3[[i H3i|j H3j]] = Cminus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix element-wise multiplication =========================================================== *)

Definition Meltmul (m1 m2: Matrix) (Hbits: MMeqbits m1 m2) := Mbop Cmult m1 m2 Hbits.

Lemma Meltmul_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hbits: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Meltmul m1 m2 Hbits ->
  m3[[i H3i|j H3j]] = Cmult (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix multiplication ======================================================================== *)

Definition Mmult_inner (m1 m2: Matrix) (i j: nat): C.
Proof.
  destruct (extract_row_unsafe m1 i) as [r _].
  destruct (extract_col_unsafe m2 j) as [c _].
  refine (dot_product_suppl (RVinner r) (CVinner c) (RVsize r)).
Defined.

Definition Mmult (m1 m2: Matrix) (H: MMeqbits m1 m2): {m: Matrix | MMeqbits m m1}.
Proof.
  refine(exist _ {|
    Mbits := Mbits m1;
    Minner := fun i j => Mmult_inner m1 m2 i j;
    |} _).
  reflexivity.
Defined.

Lemma Mmult_correct: forall (m1 m2 m: Matrix) (r: RowVec) (c: ColVec) (i j: nat)
  (Hi: _) (Hj: _) (H: _) (Hm: _) (Hmi: _) (Hmj: _) (Hr1: _) (Hc1: _) (Hrc: _),
  exist _ m Hm = Mmult m1 m2 H ->
  exist _ r Hr1 = extract_row m1 i Hi ->
  exist _ c Hc1 = extract_col m2 j Hj ->
  m[[i Hmi|j Hmj]] = dot_product r c Hrc.
Proof.
  intros.
  inversion H0.
  inversion H1.
  inversion H2.
  unfold Mget.
  rewrite H4.
  unfold Mmult_inner.
  unfold dot_product.
  rewrite H5.
  rewrite H6.
  simpl.
  reflexivity.
Qed.

Lemma Mmult_assoc: forall (m1 m2 m3 m12 m12_3 m23 m1_23: Matrix)
  (H12: _) (H12_3: _) (H23: _) (H1_23: _) (E12: _) (E12_3: _) (E23: _) (E1_23: _),
  exist _ m12 E12 = Mmult m1 m2 H12 ->
  exist _ m12_3 E12_3 = Mmult m12 m3 H12_3 ->
  exist _ m23 E23 = Mmult m2 m3 H23 ->
  exist _ m1_23 E1_23 = Mmult m1 m23 H1_23 ->
  Mequal m12_3 m1_23.
Proof.
  intros.
  unfold Mequal.
  inversion H.
  inversion H0.
  inversion H1.
  inversion H2.
  split.
  - unfold MMeqbits.
    simpl.
    rewrite H12_3.
    symmetry.
    apply (eq_trans H12 H23).
  - unfold Mget.
    simpl.
    rewrite H4.
    rewrite H6.
    unfold Mmult_inner.
    unfold extract_row_unsafe.
    unfold extract_col_unsafe.
    unfold RVsize.
    unfold Msize in *.
    simpl in *.


(* ============================================================================================== *)
(* transpose of a matrix ======================================================================== *)

Definition Mtranspose (m: Matrix): {m': Matrix| MMeqbits m m'}.
Proof.
  refine ( exist _ {|
    Mbits := Mbits m;
    Minner := fun i j => Minner m j i;
    |} _ ).
  reflexivity.
Defined.

Lemma Mtranspose_correct: forall (m mt: Matrix) (i j: nat) (Hi: _) (Hi': _) (Hj: _) (Hj': _) (Hmt: _),
  exist _ mt Hmt = Mtranspose m -> m[[i Hi|j Hj]] = mt[[j Hj'|i Hi']].
Proof.
  unfold Mtranspose.
  unfold Mget.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* conjucate tranpose of a matrix =============================================================== *)

Definition Mconjtrans (m: Matrix): {m': Matrix| MMeqbits m m'}.
Proof.
  refine ( exist _ {|
    Mbits := Mbits m;
    Minner := fun i j => Cconj (Minner m j i);
    |} _ ).
  reflexivity.
Defined.

Lemma Mconjtrans_correct: forall (m mct: Matrix) (i j: nat) (Hi: _) (Hi': _) (Hj: _) (Hj': _) (Hmt: _),
  exist _ mct Hmt = Mconjtrans m -> mct[[i Hi|j Hj]] = Cconj(m[[j Hj'|i Hi']]).
Proof.
  unfold Mtranspose.
  unfold Mget.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* identity matrix ============================================================================== *)

(* Definition eye_inner (n: nat): {m: Matrix_inner | rows m = n /\ cols m = n}.
Proof.
  refine ( exist _ {|
    rows := n;
    cols := n;
    inner := fun i j => if i =? j then 1 else 0;
    |} _).
  simpl. split. reflexivity. reflexivity.
Defined. *)

Definition eye (bits: nat): {m: Matrix | Mbits m = bits}.
Proof.
  refine (exist _ {|
    Mbits := bits;
    Minner := fun i j => if i =? j then 1 else 0;
    |} _).
  reflexivity.
Defined.

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
      {
        (* destruct (lt_eq_lt_dec j l') as [[H1|H2]|H3]. *)
        destruct (lt_eq_lt_dec j l') as [Hj|Hj].
        - destruct Hj as [Hj|Hj]. lia. lia.
        - lia. }
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

Fact Mmult_eye_l_suppl: forall (j l: nat) (f: nat -> C),
  j < l -> dot_product_suppl (fun j0 => if j =? j0 then 1 else 0) f l = f j.
Proof.
  intros.
  induction l as [|l'].
  - intros.
    lia.
  - intros.
    destruct (lt_dec j l') as [Hl|Hl].
    + simpl.
      assert (j =? l' = false).
      { apply Nat.eqb_neq. lia. }
      rewrite H0.
      rewrite Cmult_0_l.
      rewrite Cplus_0_l.
      apply IHl'.
      apply Hl.
    + simpl.
      assert (l' = j) as Hj.
      {
        (* destruct (lt_eq_lt_dec j l') as [[H1|H2]|H3]. *)
        destruct (lt_eq_lt_dec j l') as [Hj|Hj].
        - destruct Hj as [Hj|Hj]. lia. lia.
        - lia. }
      replace (l' =? j) with true.
      subst l'.
      assert (forall n, n >= j -> dot_product_suppl (fun i0 : nat => if n =? i0 then 1 else 0) f j = 0).
      { clear.
        induction j as [|j'].
        - reflexivity.
        - intros.
          simpl.
          replace (n =? j') with false.
          rewrite Cmult_0_l.
          rewrite Cplus_0_l.
          apply IHj'.
          lia.
          symmetry.
          apply <- Nat.eqb_neq.
          lia. }
      specialize H0 with j.
      assert (dot_product_suppl (fun j0 : nat => if j =? j0 then 1 else 0) f j = 0).
      { apply H0. lia. }
      rewrite H1.
      rewrite Nat.eqb_refl.
      lca.
      symmetry.
      apply <- Nat.eqb_eq.
      apply Hj.
Qed.

Lemma Mmult_eye_r: forall (m m' e: Matrix) (Hm': _) (He: _) (Hme: _),
  exist _ e He = (eye (Mbits m)) ->
  exist _ m' Hm' = Mmult m e Hme -> Mequal m' m.
Proof.
  unfold Mequal.
  intros.
  inversion H.
  inversion H0.
  split.
  - apply Hm'.
  - unfold Mget.
    rewrite H3.
    unfold Mmult_inner.
    rewrite H2.
    unfold RVsize.
    simpl.
    apply Mmult_eye_r_suppl.
    apply Hj2.
Qed.

Lemma Mmult_eye_l: forall (m m' e: Matrix) (Hm': _) (He: _) (Hem: _),
  exist _ e He = (eye (Mbits m)) ->
  exist _ m' Hm' = Mmult e m Hem -> Mequal m' m.
Proof.
  unfold Mequal.
  intros.
  inversion H.
  inversion H0.
  split.
  - apply eq_trans with (y := Mbits e).
    apply Hm'.
    apply Hem.
  - unfold Mget.
    rewrite H3.
    unfold Mmult_inner.
    rewrite H2.
    unfold RVsize.
    simpl.
    specialize (Mmult_eye_l_suppl i (2 ^ Mbits m) (fun i0 => Minner m i0 j)).
    intros.
    apply H1 in Hi2.
    rewrite Hi2.
    reflexivity.
Qed.

(* ============================================================================================== *)
