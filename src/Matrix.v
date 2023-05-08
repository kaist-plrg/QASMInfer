Require Export Complex.
Import ListNotations.

Declare Scope M_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.

(* Matrix record ================================================================================ *)

Record Matrix := {
  rows: nat;
  cols: nat;
  inner: nat -> nat -> C;
  rows_pos: rows > 0;
  cols_pos: cols > 0;
}.

(* ============================================================================================== *)
(* get an element from a matrix ================================================================= *)

Definition Mget (m : Matrix) (i j: nat) (Hi: i < rows m) (Hj: j < cols m): C := inner m i j.

Notation "m '[[' i Hi '|' j Hj ']]'" :=
  (Mget m i j Hi Hj) (at level 10, i at level 9, Hi at level 9, j at level 9, Hj at level 9, no associativity).

(* ============================================================================================== *)
(* row and column vectors ======================================================================= *)

Definition extract_row (m: Matrix) (i: nat) (H: i < rows m): {m': Matrix | rows m' = 1 /\ cols m' = cols m}.
Proof.
  refine ( exist _
    {|rows := 1;
      cols := cols m;
      inner := fun i' j' => inner m (i + i')%nat (j');
      rows_pos := _;
      cols_pos := _;
    |} _).
  Unshelve.
  - split. reflexivity. reflexivity.
  - lia.
  - apply cols_pos.
Defined.

Property extract_row_correct: forall
  (m r: Matrix) (i j: nat)
  (Hi Hi': i < rows m) (Hj: j < cols m) (Hr: rows r = 1 /\ cols r = cols m) (Hir: 0 < rows r) (Hjr: j < cols r),
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

Definition extract_col (m: Matrix) (j: nat) (H: j < cols m): {m': Matrix | rows m' = rows m /\ cols m' = 1}.
Proof.
  refine ( exist _
    {|rows := rows m;
      cols := 1;
      inner := fun i' j' => inner m (i')%nat (j + j');
    |} _).
  Unshelve.
  - split. reflexivity. reflexivity.
  - apply rows_pos.
  - lia.
Defined.

Property extract_col_correct: forall
  (m c: Matrix) (i j: nat)
  (Hi: i < rows m) (Hj Hj': j < cols m) (Hc: rows c = rows m /\ cols c = 1) (Hic: i < rows c) (Hjc: 0 < cols c),
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

Fixpoint dot_product_suppl (r c: Matrix) (idx: nat)
  (Hi: idx <= cols r) (Hr: rows r = 1) (Hc: cols c = 1) (Hrc: cols r = rows c): C.
Proof.
  destruct idx as [|idx'].
  - exact O.
  - refine (r[[O _|idx' _]] * c[[idx' _|O _]] + dot_product_suppl r c idx' _ Hr Hc Hrc).
    lia. lia. lia. lia. lia.
Defined.

Definition dot_product (r c: Matrix) (Hr: rows r = 1) (Hc: cols c = 1) (Hrc: cols r = rows c): C.
Proof.
  refine (dot_product_suppl r c (cols r) _ Hr Hc Hrc).
  lia.
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

Definition Muop (uop: C -> C) (m: Matrix): {m': Matrix | rows m' = rows m /\ cols m' = cols m}.
Proof.
  refine (
    exist _ {| rows := rows m;
              cols := cols m;
              inner := fun i j => uop (inner m i j)
            |}
            _
  ).
  simpl.
  Unshelve.
  - split. reflexivity. reflexivity.
  - apply rows_pos.
  - apply cols_pos.
Defined.

Property Muop_correct: forall
  (uop: C -> C)
  (m1 m2: Matrix)
  (i j: nat)
  (Huop: rows m2 = rows m1 /\ cols m2 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2),
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

Definition Mopp (m: Matrix): {m': Matrix | rows m' = rows m /\ cols m' = cols m} :=
  Muop Copp m.

Notation "- x" := (Mopp x) : M_scope.

Property Mopp_correct: forall
  (m1 m2: Matrix)
  (i j: nat)
  (Huop: rows m2 = rows m1 /\ cols m2 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2),
  exist _ m2 Huop = Mopp m1 ->
  m2[[i H2i|j H2j]] = Copp (m1[[i H1i|j H1j]]).
Proof.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* scalar multiplication ======================================================================== *)

Definition Msmul (s: C) (m: Matrix): {m': Matrix | rows m' = rows m /\ cols m' = cols m} :=
  Muop (Cmult s) m.

Property Msuml_correct: forall
  (s: C)
  (m1 m2: Matrix)
  (i j: nat)
  (Huop: rows m2 = rows m1 /\ cols m2 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2),
  exist _ m2 Huop = Msmul s m1 ->
  m2[[i H2i|j H2j]] = (Cmult s) (m1[[i H1i|j H1j]]).
Proof.
  intro s.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* element-wise binary operation ================================================================ *)

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2):
  {m: Matrix | rows m = rows m1 /\ cols m = cols m1}.
Proof.
  (* destruct (bop_lists bop (data m1) (data m2) (matrix_shape_size m1 m2 Hrows Hcols)) as [newData newH]. *)
  refine (
    exist _ {|rows := rows m1;
              cols := cols m1;
              inner := fun i j => bop (inner m1 i j) (inner m2 i j);
              |}
             _
  ).
  Unshelve.
  - split. reflexivity. reflexivity.
  - apply rows_pos.
  - apply cols_pos.
Defined.

Property Mbop_correct: forall
  (bop: C -> C -> C)
  (m1 m2 m3: Matrix)
  (i j: nat)
  (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2)
  (Hbop: rows m3 = rows m1 /\ cols m3 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2)
  (H3i: i < rows m3) (H3j: j < cols m3),
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
  (m1 m2: Matrix) (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2):
  {m: Matrix | rows m = rows m1 /\ cols m = cols m1} :=
  Mbop Cplus m1 m2 Hrows Hcols.

Infix "+" := Mplus : M_scope.

Property Mplus_correct: forall
  (m1 m2 m3: Matrix)
  (i j: nat)
  (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2)
  (Hbop: rows m3 = rows m1 /\ cols m3 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2)
  (H3i: i < rows m3) (H3j: j < cols m3),
  exist _ m3 Hbop = Mplus m1 m2 Hrows Hcols ->
  m3[[i H3i|j H3j]] = Cplus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix subtraction =========================================================================== *)

Definition Mminus
  (m1 m2: Matrix) (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2):
  {m: Matrix | rows m = rows m1 /\ cols m = cols m1} :=
  Mbop Cminus m1 m2 Hrows Hcols.

Infix "-" := Mminus : M_scope.

Property Mminus_correct: forall
  (m1 m2 m3: Matrix)
  (i j: nat)
  (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2)
  (Hbop: rows m3 = rows m1 /\ cols m3 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2)
  (H3i: i < rows m3) (H3j: j < cols m3),
  exist _ m3 Hbop = Mminus m1 m2 Hrows Hcols ->
  m3[[i H3i|j H3j]] = Cminus (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix element-wise multiplication =========================================================== *)

Definition Meltmul
  (m1 m2: Matrix) (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2):
  {m: Matrix | rows m = rows m1 /\ cols m = cols m1} :=
  Mbop Cmult m1 m2 Hrows Hcols.

Property Meltmul_correct: forall
  (m1 m2 m3: Matrix)
  (i j: nat)
  (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2)
  (Hbop: rows m3 = rows m1 /\ cols m3 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2)
  (H3i: i < rows m3) (H3j: j < cols m3),
  exist _ m3 Hbop = Meltmul m1 m2 Hrows Hcols ->
  m3[[i H3i|j H3j]] = Cmult (m1[[i H1i|j H1j]]) (m2[[i H2i|j H2j]]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix multiplication ======================================================================== *)

Definition Mmult_inner (m1 m2: Matrix) (i j: nat) (H: cols m1 = rows m2): C.
Proof.
  destruct (lt_dec i (rows m1)) as [Hi | Hi'].
  - destruct (lt_dec j (cols m2)) as [Hj | Hj'].
    + destruct (extract_row m1 i Hi) as [r Hr].
      destruct Hr as [Hr1 Hr2].
      destruct (extract_col m2 j Hj) as [c Hc].
      destruct Hc as [Hc1 Hc2].
      refine (dot_product r c Hr1 Hc2 _). lia.
    + exact O.
  - exact O.
Defined.

Definition Mmult (m1 m2: Matrix) (H: cols m1 = rows m2): {m: Matrix | rows m = rows m1 /\ cols m = cols m2}.
Proof.
  refine( exist _
    {|rows:= rows m1;
      cols:= cols m2;
      inner:= fun i j => Mmult_inner m1 m2 i j H;
    |} _).
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
  unfold Mget.
  rewrite H4.
  simpl.
  unfold Mmult_inner.
  destruct (lt_dec i (rows m1)).
  - destruct (lt_dec j (cols m2)).
    + simpl.
      inversion H1.
      inversion H2.
      simpl.
      apply eq_dot_product.
      * rewrite H5.
        reflexivity.
      * rewrite H6.
        reflexivity.
    + contradiction.
  - contradiction.
Qed.

(* ============================================================================================== *)

(* Definition Mmult (m1 m2: Matrix): option Matrix. *)
(* Definition transpose, dagger *)
(* Definition trace, partial trace *)
(* Definition tensor_product *)
