Require Export Complex.
Import ListNotations.

Declare Scope M_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.

(* Matrix record ================================================================================ *)

Record Matrix_inner: Type := {
  rows: nat;
  cols: nat;
  inner: nat -> nat -> C;
}.

Record Matrix: Type := {
  inner_mat: Matrix_inner;
  rows_pos: rows inner_mat > 0;
  cols_pos: cols inner_mat > 0;
}.

Notation "m .rows" := (rows (inner_mat m)) (at level 9, format "m '.rows'").
Notation "m .cols" := (cols (inner_mat m)) (at level 9, format "m '.cols'").
Notation "m .inner" := (inner (inner_mat m)) (at level 9, format "m '.inner'").

(* ============================================================================================== *)
(* get an element from a matrix ================================================================= *)

Definition Mget (m : Matrix) (i j: nat) (Hi: i < m.rows) (Hj: j < m.cols): C := m.inner i j.

Notation "m '[[' i Hi '|' j Hj ']]'" :=
  (Mget m i j Hi Hj) (at level 10, i at level 9, Hi at level 9, j at level 9, Hj at level 9, no associativity).

(* ============================================================================================== *)
(* row and column vectors ======================================================================= *)

Definition extract_row_inner (m: Matrix_inner) (i: nat): {m': Matrix_inner | rows m' = 1 /\ cols m' = cols m}.
Proof.
  refine ( exist _ {|
    rows := 1;
    cols := cols m;
    inner := fun i' j' => inner m (i + i')%nat (j');
    |} _ ).
  split. reflexivity. reflexivity.
Defined.

Definition extract_row (m: Matrix) (i: nat) (H: i < m.rows): {m': Matrix | m'.rows = 1 /\ m'.cols = m.cols}.
Proof.
  destruct (extract_row_inner (inner_mat m) i) as [m' Hm'].
  refine ( exist _
    {|inner_mat := m' |} _).
  Unshelve.
  - simpl. apply Hm'.
  - simpl. lia.
  - destruct Hm' as [_ Hm].
    rewrite Hm.
    apply cols_pos.
Defined.

Property extract_row_correct: forall
  (m r: Matrix) (i j: nat) (Hi Hi': _) (Hj: _) (Hr: _) (Hir: _) (Hjr: _),
  exist _ r Hr = extract_row m i Hi ->
  r[[0 Hir|j Hjr]] = m[[i Hi'|j Hj]].
Proof.
  unfold extract_row.
  intros.
  inversion H.
  unfold Mget.
  rewrite H1.
  intros.
  simpl.
  replace (i + 0)%nat with i by lia.
  reflexivity.
Qed.

Definition extract_col_inner (m: Matrix_inner) (j: nat): {m': Matrix_inner | rows m' = rows m /\ cols m' = 1}.
Proof.
  refine ( exist _ {|
    rows := rows m;
    cols := 1;
    inner := fun i' j' => inner m (i')%nat (j + j');
    |} _ ).
  split. reflexivity. reflexivity.
Defined.

Definition extract_col (m: Matrix) (j: nat) (H: j < m.cols): {m': Matrix | m'.rows = m.rows /\ m'.cols = 1}.
Proof.
  destruct (extract_col_inner (inner_mat m) j) as [m' Hm'].
  refine ( exist _ {|inner_mat := m'|} _).
  Unshelve.
  - simpl. apply Hm'.
  - destruct Hm' as [Hm _].
    rewrite Hm.
    apply rows_pos.
  - simpl. lia.
Defined.

Property extract_col_correct: forall
  (m c: Matrix) (i j: nat)
  (Hi: _) (Hj Hj': _) (Hc: _) (Hic: _) (Hjc: _),
  exist _ c Hc = extract_col m j Hj ->
  c[[i Hic|0 Hjc]] = m[[i Hi|j Hj']].
Proof.
  unfold extract_col.
  intros.
  inversion H.
  unfold Mget.
  rewrite H1.
  intros.
  simpl.
  replace (j + 0)%nat with j by lia.
  reflexivity.
Qed.

Fixpoint dot_product_inner (r c: Matrix_inner) (idx: nat): C.
Proof.
  destruct idx as [|idx'].
  - exact O.
  - apply (inner r O idx' * inner c idx' O + dot_product_inner r c idx').
Defined.

Definition dot_product (r c: Matrix) (Hr: r.rows = 1) (Hc: c.cols = 1) (Hrc: r.cols = c.rows): C.
Proof.
  refine (dot_product_inner (inner_mat r) (inner_mat c) (r.cols)).
Defined.

Fact eq_dot_product: forall (m1 m2 m3 m4: Matrix) (H1: _) (H2: _) (H3: _) (H4: _) (H5: _) (H6: _),
  m1 = m3 -> m2 = m4 -> dot_product m1 m2 H1 H2 H3 = dot_product m3 m4 H4 H5 H6.
Proof.
  intros.
  subst m1 m2.
  assert (H1 = H4) as HP1 by apply proof_irrelevance.
  assert (H2 = H5) as HP2 by apply proof_irrelevance.
  assert (H3 = H6) as HP3 by apply proof_irrelevance.
  rewrite HP1.
  rewrite HP2.
  rewrite HP3.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* element-wise unary operation ================================================================= *)

Definition Muop_inner (uop: C -> C) (m: Matrix_inner): {m': Matrix_inner | rows m' = rows m /\ cols m' = cols m}.
Proof.
  refine ( exist _ {|
    rows := rows m;
    cols := cols m;
    inner := fun i j => uop (inner m i j);
    |} _ ).
  simpl. split. reflexivity. reflexivity.
Defined.

Definition Muop (uop: C -> C) (m: Matrix): {m': Matrix | m'.rows = m.rows /\ m'.cols = m.cols}.
Proof.
  destruct (Muop_inner uop (inner_mat m)) as [m' Hm'].
  refine (exist _ {|inner_mat := m'|} _).
  simpl. apply Hm'.
  Unshelve.
  - destruct Hm' as [H1 H2].
    rewrite H1. apply rows_pos.
  - destruct Hm' as [H1 H2].
    rewrite H2. apply cols_pos.
Defined.

Property Muop_correct: forall
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

Definition Mopp (m: Matrix): {m': Matrix | m'.rows = m.rows  /\ m'.cols = m.cols} :=
  Muop Copp m.

Notation "- x" := (Mopp x) : M_scope.

Property Mopp_correct: forall
  (m1 m2: Matrix) (i j: nat)
  (Huop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ m2 Huop = Mopp m1 ->
  m2[[i H2i|j H2j]] = Copp (m1[[i H1i|j H1j]]).
Proof.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* scalar multiplication ======================================================================== *)

Definition Msmul (s: C) (m: Matrix): {m': Matrix | m'.rows = m.rows  /\ m'.cols = m.cols} :=
  Muop (Cmult s) m.

Property Msuml_correct: forall
  (s: C) (m1 m2: Matrix) (i j: nat)
  (Huop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _),
  exist _ m2 Huop = Msmul s m1 -> m2[[i H2i|j H2j]] = (Cmult s) (m1[[i H1i|j H1j]]).
Proof.
  intro s.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* element-wise binary operation ================================================================ *)

Definition Mbop_inner (bop: C -> C -> C) (m1 m2: Matrix_inner):
  {m: Matrix_inner | rows m = rows m1 /\ cols m = cols m1}.
Proof.
  refine (exist _ {|
    rows := rows m1;
    cols := cols m1;
    inner := fun i j => bop (inner m1 i j) (inner m2 i j) |} _ ).
  simpl. split. reflexivity. reflexivity.
Defined.

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hrows: m1.rows = m2.rows) (Hcols: m1.cols = m2.cols):
  {m: Matrix | m.rows = m1.rows /\ m.cols = m1.cols}.
Proof.
  destruct (Mbop_inner bop (inner_mat m1) (inner_mat m2)) as [m Hm].
  destruct Hm as [H1 H2].
  refine (exist _ {|inner_mat:= m|} _).
  Unshelve.
  - simpl. split. lia. lia.
  - rewrite H1. apply rows_pos.
  - rewrite H2. apply cols_pos.
Defined.

Property Mbop_correct: forall
  (bop: C -> C -> C) (m1 m2 m3: Matrix) (i j: nat)
  (Hrows: _) (Hcols: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Mbop bop m1 m2 Hrows Hcols ->
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

Definition Mplus
  (m1 m2: Matrix) (Hrows: m1.rows = m2.rows) (Hcols: m1.cols = m2.cols):
  {m: Matrix | m.rows = m1.rows /\ m.cols = m1.cols} :=
  Mbop Cplus m1 m2 Hrows Hcols.

Property Mplus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hrows: _) (Hcols: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Mplus m1 m2 Hrows Hcols ->
  m3[[i H3i|j H3j]] = Cplus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix subtraction =========================================================================== *)

Definition Mminus
  (m1 m2: Matrix) (Hrows: m1.rows = m2.rows) (Hcols: m1.cols = m2.cols):
  {m: Matrix | m.rows = m1.rows /\ m.cols = m1.cols} :=
  Mbop Cminus m1 m2 Hrows Hcols.

Property Mminus_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hrows: _) (Hcols: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Mminus m1 m2 Hrows Hcols ->
  m3[[i H3i|j H3j]] = Cminus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix element-wise multiplication =========================================================== *)

Definition Meltmul
  (m1 m2: Matrix) (Hrows: m1.rows = m2.rows) (Hcols: m1.cols = m2.cols):
  {m: Matrix | m.rows = m1.rows /\ m.cols = m1.cols} :=
  Mbop Cmult m1 m2 Hrows Hcols.

Property Meltmul_correct: forall
  (m1 m2 m3: Matrix) (i j: nat)
  (Hrows: _) (Hcols: _) (Hbop: _) (H1i: _) (H1j: _) (H2i: _) (H2j: _) (H3i: _) (H3j: _),
  exist _ m3 Hbop = Meltmul m1 m2 Hrows Hcols ->
  m3[[i H3i|j H3j]] = Cmult (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix multiplication ======================================================================== *)

Definition Mmult_inner (m1 m2: Matrix_inner) (i j: nat): C.
Proof.
  destruct (extract_row_inner m1 i) as [r _].
  destruct (extract_col_inner m2 j) as [c _].
  refine (dot_product_inner r c (cols r)).
Defined.

Definition Mmult (m1 m2: Matrix) (H: m1.cols = m2.rows):
  {m: Matrix | m.rows = m1.rows /\ m.cols = m2.cols}.
Proof.
  refine( exist _
    {|inner_mat := {|
        rows:= m1.rows;
        cols:= m2.cols;
        inner:= fun i j => Mmult_inner (inner_mat m1) (inner_mat m2) i j; |} |} _).
  Unshelve.
  split. reflexivity. reflexivity.
  apply rows_pos. apply cols_pos.
Defined.

Property Mmult_correct: forall (m1 m2 m r c: Matrix) (i j: nat)
  (Hi: _) (Hj: _) (H: _) (Hm: _) (Hmi: _) (Hmj: _) (Hr1: _) (Hr2: _) (Hc1: _) (Hc2: _) (Hrc: _),
  exist _ m Hm = Mmult m1 m2 H ->
  exist _ r Hr1 = extract_row m1 i Hi ->
  exist _ c Hc1 = extract_col m2 j Hj ->
  m[[i Hmi|j Hmj]] = dot_product r c Hr2 Hc2 Hrc.
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

(* ============================================================================================== *)
(* transpose of a matrix ======================================================================== *)

Definition Mtranspose (m: Matrix): {mt: Matrix | mt.rows = m.cols /\ mt.cols = m.rows}.
Proof.
  refine( exist _ {|inner_mat := {|
      rows := m.cols;
      cols := m.rows;
      inner := fun i j => inner (inner_mat m) j i;
    |} |} _ ).
    Unshelve.
    split. reflexivity. reflexivity.
    apply cols_pos. apply rows_pos.
Defined.

Property Mtranspose_correct: forall (m mt: Matrix) (i j: nat) (Hi: _) (Hi': _) (Hj: _) (Hj': _) (Hmt: _),
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

Definition Mconjtrans (m: Matrix): {mt: Matrix | mt.rows = m.cols /\ mt.cols = m.rows}.
Proof.
  refine( exist _ {|inner_mat := {|
      rows := m.cols;
      cols := m.rows;
      inner := fun i j => Cconj (inner (inner_mat m) j i);
    |} |} _ ).
    Unshelve.
    split. reflexivity. reflexivity.
    apply cols_pos. apply rows_pos.
Defined.

Property Mconjtrans_correct: forall (m mct: Matrix) (i j: nat) (Hi: _) (Hi': _) (Hj: _) (Hj': _) (Hmct: _),
  exist _ mct Hmct = Mconjtrans m -> mct[[j Hj'|i Hi']] = Cconj(m[[i Hi|j Hj]]) .
Proof.
  unfold Mconjtrans.
  unfold Mget.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* fundamental matrices ========================================================================= *)

Definition eye (n: nat) (H: n > 0): {m: Matrix | m.rows = n /\ m.cols = n}.
Proof.
  refine ( exist _ {|inner_mat := {|
    rows := n;
    cols := n;
    inner := fun i j => if i =? j then 1 else 0;
    |}|} _ ).
  Unshelve.
  split.
  reflexivity. reflexivity. apply H. apply H.
Defined.

(* ============================================================================================== *)
