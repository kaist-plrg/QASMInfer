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
  data: list C;
  rows_pos: rows > 0;
  cols_pos: cols > 0;
  data_length: length data = (rows * cols)%nat
}.

Lemma matrix_shape_size: forall m1 m2: Matrix,
  rows m1 = rows m2 -> cols m1 = cols m2 -> length (data m1) = length (data m2).
Proof.
  intros m1 m2 Hrows Hcols.
  repeat rewrite data_length.
  rewrite Hrows.
  rewrite Hcols.
  reflexivity.
Qed.

(* ============================================================================================== *)
(* get an element from a matrix ================================================================= *)

Definition Mget (m : Matrix) (i j: nat) (Hi: i < rows m) (Hj: j < cols m): C.
Proof.
  refine (nth_safe (data m) (i * cols m + j) _).
  rewrite data_length.
  nia.
Defined.

Notation "m '[[' i Hi '|' j Hj ']]'" :=
  (Mget m i j Hi Hj) (at level 10, i at level 9, Hi at level 9, j at level 9, Hj at level 9, no associativity).

(* ============================================================================================== *)
(* extract i-th row or j-th column ============================================================== *)

Definition extract_row (m: Matrix) (i: nat) (H: i < rows m): {l: list C | length l = cols m}.
Proof.
  refine( exist _ (firstn (cols m) (skipn (i * cols m) (data m))) _).
  apply firstn_length_le.
  rewrite skipn_length.
  rewrite data_length.
  nia.
Defined.

Property extract_row_correct: forall
  (m: Matrix) (i j: nat) (row: list C)
  (Hi: i < rows m) (Hj: j < cols m) (Hr: length row = cols m) (Hjr: j < length row),
  exist _ row Hr = extract_row m i Hi ->
  nth_safe row j Hjr = m[[i Hi|j Hj]].
Proof.
  unfold extract_row.
  unfold Mget.
  intros.
  revert Hj Hjr.
  inversion H.
  intros.
  assert (j < length (skipn (i * cols m) (data m))) as H2.
  { rewrite skipn_length.
    rewrite data_length.
    clear H.
    nia. }
  rewrite firstn_nth_safe with (H2 := H2).
  assert (i * cols m + j < length (data m)) as H3.
  { rewrite data_length.
    clear H.
    nia. }
  rewrite skipn_nth_safe with (H2 := H3).
  apply eq_nth_safe.
  clear H.
  lia.
Qed.


Definition jth_of_ith_row
(m: Matrix) (i: nat) (Hi: i < rows m)
(j: nat) (Hin: In j (range (cols m))): C.
Proof.
  refine (m[[i Hi|j _]]).
  apply in_range_lt.
  apply Hin.
Defined.

Definition extract_row (m: Matrix) (i: nat) (H: i < rows m): {l: list C | length l = cols m}.
Proof.
  refine (
    exist _
    (map_with_proof (range(cols m)) (jth_of_ith_row m i H))
    _
  ).
  rewrite length_map_with_proof.
  rewrite length_range.
  reflexivity.
Defined.

(* Definition extract_row (m: Matrix) (i: nat) (H: i < rows m): {l: list C | length l = cols m}.

Fixpoint extract_row_suppl (m: Matrix) (i len: nat) (Hi: i < rows m) (Hlen: len <= cols m): {l: list C | length l = len}.
Proof.
  destruct len as [|j].
  - exists []. reflexivity.
  - remember [(Mget m i j Hi Hlen)] as t.
    assert (j <= cols m) as Hj by lia.
    destruct (extract_row_suppl m i j Hi Hj) as [l' H'].
    refine (exist _ (l' ++ t) _).
    rewrite app_length.
    rewrite H'.
    subst t.
    simpl.
    lia.
Defined.

Definition extract_row (m: Matrix) (i: nat) (H: i < rows m): {l: list C | length l = cols m}.
Proof.
  refine (extract_row_suppl m i (cols m) H _). lia.
Defined. *)

Property extract_row_correct: forall
  (m1 m2: Matrix) (i1 i2 j1 j2 r1 r2 c1 c2: nat) (row: list C)
  (Hi1: i1 < rows m1) (Hj1: j1 < length row) (Hl: length row = cols m1)
  (Hi2: i2 < rows m2) (Hj2: j2 < cols m2),
  m1 = m2 -> i1 = i2 -> j1 = j2 ->
  row = proj1_sig (extract_row m1 i1 Hi1) ->
  nth_safe row j1 Hj1 = Mget m2 i2 j2 Hi2 Hj2.
Proof.
  unfold extract_row.
  (* unfold map_with_proof. *)
  simpl.
  intros.
  revert Hl Hj2 Hi2 Hj1.
  induction j1 as [|j1'].
  - subst m2 i2 j2.
    destruct row as [|h t] eqn: E.
    + assert (@length nat [] = length( map_with_proof (range (cols m1)) (jth_of_ith_row m1 i1 Hi1))) as H.
      { rewrite <- H2.
        reflexivity.
      }
      simpl in H.
      rewrite length_map_with_proof in H.
      rewrite length_range in H.
      lia.
    + simpl.
      destruct (cols m1).
      unfold range in H2.
  -






  - intros.
    simpl in Hl.
    lia.
  - intros.
    subst i2 j2.
    destruct j1 as [|j1'].
    + simpl in *.
      destruct (cols m).



(* ============================================================================================== *)
(* element-wise unary operation ================================================================= *)

Definition Muop (uop: C -> C) (m: Matrix): {m': Matrix | rows m' = rows m /\ cols m' = cols m}.
Proof.
  refine (
    exist _ {| rows := rows m;
              cols := cols m;
              data := map uop (data m)
            |}
            _
  ).
  simpl.
  Unshelve.
  - split. reflexivity. reflexivity.
  - apply rows_pos.
  - apply cols_pos.
  - rewrite map_length.
    apply data_length.
Defined.

Property Muop_correct: forall
  (uop: C -> C)
  (m1 m2: Matrix)
  (i j: nat)
  (Huop: rows m2 = rows m1 /\ cols m2 = cols m1)
  (H1i: i < rows m1) (H1j: j < cols m1)
  (H2i: i < rows m2) (H2j: j < cols m2),
  exist _ m2 Huop = Muop uop m1 ->
  m2[i H2i][j H2j] = uop m1[i H1i][j H1j].
Proof.
  intros.
  inversion H.
  subst m2.
  unfold Mget.
  simpl.
  eapply map_nth_safe.
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
  m2[i H2i][j H2j] = Copp m1[i H1i][j H1j].
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
  m2[i H2i][j H2j] = (Cmult s) m1[i H1i][j H1j].
Proof.
  intro s.
  apply Muop_correct.
Qed.

(* ============================================================================================== *)
(* element-wise binary operation ================================================================ *)

Definition Mbop (bop: C -> C -> C) (m1 m2: Matrix) (Hrows: rows m1 = rows m2) (Hcols: cols m1 = cols m2):
  {m: Matrix | rows m = rows m1 /\ cols m = cols m1}.
Proof.
  destruct (bop_lists bop (data m1) (data m2) (matrix_shape_size m1 m2 Hrows Hcols)) as [newData newH].
  refine (
    exist _ {| rows := rows m1;
             cols := cols m1;
             data := newData;
             data_length := _  |}
             _
  ).
  Unshelve.
  - split. reflexivity. reflexivity.
  - apply rows_pos.
  - apply cols_pos.
  - rewrite newH. apply data_length.
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
  m3[i H3i][j H3j] = bop m1[i H1i][j H1j] m2[i H2i][j H2j].
Proof.
  intros.
  eapply bop_lists_correct.
  - destruct Hbop as [e1 e2].
    apply matrix_shape_size.
    apply e1. apply e2.
  - unfold Mbop in H.
    destruct (bop_lists bop (data m1) (data m2) (matrix_shape_size m1 m2 Hrows Hcols)) as [x p] eqn:E.
    rewrite E.
    simpl.
    inversion H.
    reflexivity.
  - rewrite Hcols.
    reflexivity.
  - destruct Hbop as [E1 E2].
    rewrite E2.
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
  m3[i H3i][j H3j] = Cplus (m1[i H1i][j H1j]) (m2[i H2i][j H2j]).
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
  m3[i H3i][j H3j] = Cminus (m1[i H1i][j H1j]) (m2[i H2i][j H2j]).
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
  m3[i H3i][j H3j] = Cmult (m1[i H1i][j H1j]) (m2[i H2i][j H2j]).
Proof.
  apply Mbop_correct.
Qed.

(* ============================================================================================== *)
(* matrix multiplication ======================================================================== *)

Fixpoint dot_product (l1 l2: list C) (H: length l1 = length l2): C.
Proof.
  destruct (bop_lists Cmult l1 l2 H) as [l Hl].
  apply (fold_left Cplus l 0).
Defined.


Definition Mmult
  (m1 m2: Matrix) (H: cols m1 = rows m2): {m: Matrix | rows m = rows m1 /\ cols m = cols m2}.

(* ============================================================================================== *)

(* Definition Mmult (m1 m2: Matrix): option Matrix. *)
