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
(* extract i-th row ============================================================================= *)

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

(* ============================================================================================== *)
(* extract j-th column ========================================================================== *)

(* Fixpoint extract_col_suppl
  (data: list C) (cols: nat) (j: nat) (acc: list C) (H: j < cols): list C.
Proof.
  destruct data as [|h t].
  - exact acc.
  - refine (extract_col_suppl (skipn cols (h :: t)) cols j (acc ++ [nth_safe (firstn cols (h :: t)) j _]) H). *)

Definition ith_of_jth_col
  (m: Matrix) (j: nat) (Hj: j < cols m)
  (i: nat) (Hin: In i (range (rows m))): C.
Proof.
  refine (nth_safe (data m) (i * cols m + j) _).
  rewrite data_length.
  apply in_range_lt in Hin.
  nia.
Defined.

Definition extract_col (m: Matrix) (j: nat) (H: j < cols m): {l: list C | length l = rows m}.
Proof.
  refine (
    exist _
    (map_with_proof (range(rows m)) (ith_of_jth_col m j H))
    _
  ).
  rewrite length_map_with_proof.
  rewrite length_range.
  reflexivity.
Defined.

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
(* Definition transpose, dagger *)
(* Definition trace, partial trace *)
(* Definition tensor_product *)
