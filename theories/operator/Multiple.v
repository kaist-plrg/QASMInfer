Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.Single.
Require Import QASMInfer.operator.Projection.

From Stdlib Require Import List.

Bind Scope Complex_scope with Complex.
Open Scope Matrix_scope.

(** Definition *)

Section SWAP.

Definition mat_swap2: Matrix 2 :=
  rec_mat (rec_mat (bas_mat 1) (bas_mat 0)
                   (bas_mat 0) (bas_mat 0))  (rec_mat (bas_mat 0) (bas_mat 0)
                                                      (bas_mat 1) (bas_mat 0))
          (rec_mat (bas_mat 0) (bas_mat 1)
                   (bas_mat 0) (bas_mat 0))  (rec_mat (bas_mat 0) (bas_mat 0)
                                                      (bas_mat 0) (bas_mat 1)).

Fixpoint mat_swap_1n_suppl (n: nat) : Matrix (2 + n).
Proof.
  destruct n as [|n'].
  - exact mat_swap2.
  - exact ((mat_swap2 ⊗ mat_eye) * ((@mat_eye 1) ⊗ mat_swap_1n_suppl n') * (mat_swap2 ⊗ mat_eye)).
Defined.

Definition mat_swap_1n (n: nat) : Matrix n.
Proof.
  destruct n as [|[|n']].
  1-2: exact mat_eye.
  exact (mat_swap_1n_suppl n').
Defined.

Definition mat_swap {n} (q1 q2: nat) : Matrix n.
Proof.
  destruct (lt_dec q1 n) as [H1|H1], (lt_dec q2 n) as [H2|H2].
  - destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
    + replace n with (q1 + (q2 - q1 + 1) + (n - q2 - 1))%nat by lia.
      exact ((@mat_eye q1) ⊗ mat_swap_1n (q2 - q1 + 1) ⊗ @mat_eye (n - q2 - 1)).
    + exact mat_eye.
    + replace n with (q2 + (q1 - q2 + 1) + (n - q1 - 1))%nat by lia.
      exact ((@mat_eye q2) ⊗ mat_swap_1n (q1 - q2 + 1) ⊗ @mat_eye (n - q1 - 1)).
  - exact mat_eye.
  - exact mat_eye.
  - exact mat_eye.
Defined.

Definition mat_swap_op {n} (q1 q2: nat) (U: Matrix n) : Matrix n :=
  mat_swap q1 q2 * U * mat_swap q1 q2.

(* Function to describe the action of swap matrix *)
Definition swap_qbit (qbit1 qbit2: nat) (tq: nat): nat :=
  match Nat.eq_dec tq qbit1 with
  | left _ => qbit2
  | right _ =>
      match Nat.eq_dec tq qbit2 with
      | left _ => qbit1
      | right _ => tq
      end
  end.

End SWAP.

Section CNOT.

Fixpoint mat_ctrl_single (n c t: nat) (U: Matrix 1) : Matrix n :=
  match n, c, t with
  | 0, _, _ | S _, 0, 0 => mat_eye
  | S n', 0, S t' => mat_proj0_base ⊗ mat_eye + mat_proj1_base ⊗ mat_single n' t' U
  | S n', S c', 0 => mat_eye ⊗ mat_proj0 n' c' + U ⊗ mat_proj1 n' c'
  | S n', S c', S t' => (@mat_eye 1) ⊗ mat_ctrl_single n' c' t' U
  end.

Definition mat_not2: Matrix 1 := rec_mat (bas_mat 0) (bas_mat 1) (bas_mat 1) (bas_mat 0).

Definition mat_x01 : Matrix 1 := rec_mat (bas_mat 0) (bas_mat 1) (bas_mat 0) (bas_mat 0). (* |0><1| *)
Definition mat_x10 : Matrix 1 := rec_mat (bas_mat 0) (bas_mat 0) (bas_mat 1) (bas_mat 0). (* |1><0| *)

Definition mat_cnot {n} (qc qt: nat) : Matrix n := mat_ctrl_single n qc qt mat_not2.

End CNOT.

(** Properties *)

Section SWAP_PROPERTIES.

Lemma mat_swap2_unitary : mat_unitary mat_swap2.
Proof.
  unfold mat_swap2, mat_unitary, mat_eye; simpl; split.
  all: repeat f_equal; com_simpl.
Qed.

Lemma mat_swap_1n_unitary : forall {n}, mat_unitary (mat_swap_1n n).
Proof.
  induction n as [|[|[|n']]].
  1-3: unfold mat_unitary; simpl; split; repeat f_equal.
  all: try lca.
  unfold mat_unitary in *.
  split.
  all: unfold mat_swap_1n in *.
  all: unfold mat_swap_1n_suppl.
  all: repeat apply mat_mul_unitary.
  all: try apply (@tprod_unitary 2 (S n')).
  all: try apply (@tprod_unitary 1 (2 + n')).
  all: try apply mat_eye_unitary.
  all: try apply mat_swap2_unitary.
  all: auto.
Qed.

Lemma mat_swap_unitary : forall {n q1 q2}, mat_unitary (@mat_swap n q1 q2).
Proof.
  intros.
  unfold mat_swap; destruct (lt_dec q1 n) as [H1|H1], (lt_dec q2 n) as [H2|H2].
  - destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
    all: simpl_eq.
    all: repeat apply tprod_unitary.
    all: try apply mat_eye_unitary.
    all: apply mat_swap_1n_unitary.
  - apply mat_eye_unitary.
  - apply mat_eye_unitary.
  - apply mat_eye_unitary.
Qed.

Lemma mat_swap2_Hermitian : mat_Hermitian mat_swap2.
Proof.
  unfold mat_swap2, mat_Hermitian.
  f_equal; f_equal; f_equal; com_simpl.
Qed.

Lemma mat_swap_1n_Hermitian : forall {n}, mat_Hermitian (mat_swap_1n n).
Proof.
  induction n as [|[|[|n']]].
  1-3: unfold mat_Hermitian; simpl; repeat f_equal; com_simpl.
  unfold mat_Hermitian in *.
  unfold mat_swap_1n in *.
  replace (mat_swap_1n_suppl (S n')) with ((mat_swap2 ⊗ mat_eye) * ((@mat_eye 1) ⊗ mat_swap_1n_suppl n') * (mat_swap2 ⊗ mat_eye)) by reflexivity.
  replace (mat_swap2 ⊗ (@mat_eye (S n'))) with ((mat_swap2 ⊗ (@mat_eye (S n')))†) at 2 4.
  - apply mat_mul_conj_Hermitian.
    apply (tprod_Hermitian (m:=1) (n:=S (S n'))).
    + apply mat_eye_Hermitian.
    + apply IHn.
  - apply tprod_Hermitian.
    + apply mat_swap2_Hermitian.
    + apply mat_eye_Hermitian.
Qed.

Lemma mat_swap_Hermitian : forall {n q1 q2}, mat_Hermitian (@mat_swap n q1 q2).
Proof.
  intros.
  unfold mat_swap; destruct (lt_dec q1 n) as [H1|H1], (lt_dec q2 n) as [H2|H2].
  - destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
    all: simpl_eq.
    2: apply mat_eye_Hermitian.
    all: apply tprod_Hermitian.
    1, 3: apply tprod_Hermitian.
    all: try apply mat_eye_Hermitian.
    all: apply mat_swap_1n_Hermitian.
  - apply mat_eye_Hermitian.
  - apply mat_eye_Hermitian.
  - apply mat_eye_Hermitian.
Qed.

Lemma mat_swap_op_unitary : forall {n q1 q2} (U: Matrix n), mat_unitary U -> mat_unitary (mat_swap_op q1 q2 U).
Proof.
  intros.
  unfold mat_swap_op.
  repeat apply mat_mul_unitary.
  all: try apply mat_swap_unitary; auto.
Qed.

Lemma mat_swap_op_Hermitian : forall {n q1 q2} (U: Matrix n), mat_Hermitian U -> mat_Hermitian (mat_swap_op q1 q2 U).
Proof.
  intros.
  unfold mat_swap_op.
  replace (mat_swap q1 q2) with ((@mat_swap n q1 q2)†) at 2 by apply mat_swap_Hermitian.
  apply mat_mul_conj_Hermitian.
  apply H.
Qed.

Lemma mat_swap2_id:
  mat_swap2 = rec_mat mat_proj0_base mat_x10 mat_x01 mat_proj1_base.
Proof. reflexivity. Qed.

Lemma mat_swap_1n_suppl_id: forall {n},
  mat_swap_1n_suppl n = mat_ccast (
    rec_mat (mat_eye ⊗ mat_proj0_base) (mat_eye ⊗ mat_x10)
            (mat_eye ⊗ mat_x01) (mat_eye ⊗ mat_proj1_base)
  ) (@add_comm (S n) 1).
Proof.
  intros n.
  induction n.
  - simpl. unfold mat_swap2.
    f_equal; f_equal; f_equal; lca.
  - change (mat_swap_1n_suppl (S n)) with
      ((mat_swap2 ⊗ mat_eye) * ((@mat_eye 1) ⊗ mat_swap_1n_suppl n) * (mat_swap2 ⊗ mat_eye)).
    rewrite IHn.
    unfold mat_swap2.
    replace (@mat_eye (S n)) with (@mat_eye 1 ⊗ @mat_eye n) at 3 4 5 6 by apply tprod_eye_eye.
    change (@mat_eye 1) with (rec_mat (bas_mat 1) (bas_mat 0) (bas_mat 0) (bas_mat 1)).
    repeat rewrite tprod_one_step.
    repeat rewrite tprod_base.
    repeat rewrite mat_scale_1, mat_scale_0.
    rewrite rec_mat_ccast, rec_mat_ccast.
    repeat rewrite (mat_mul_one_step (n:= Nat.pred (Init.Nat.add (S (S O)) (S n)))).
    repeat rewrite mat_mul_0_r.
    repeat rewrite mat_add_0_r.
    repeat rewrite mat_add_0_l.
    repeat rewrite (mat_mul_one_step (n:= Nat.pred (Nat.pred (Init.Nat.add (S (S O)) (S n))))).
    repeat rewrite (rec_mat_ccast (n:= Nat.pred (Init.Nat.add (S n) (S O)))).
    repeat rewrite (mat_add_one_step (n:= Nat.pred (Nat.pred (Init.Nat.add (S (S O)) (S n))))).
    f_equal; f_equal.
    all: try rewrite tprod_0_l.
    all: mat_simpl.
    all: try replace (rec_mat (@mat_0 n) (@mat_0 n) (@mat_0 n) (@mat_0 n)) with (@mat_0 (S n)) by reflexivity.
    all: try apply mat_ccast_refl'.
    all: remember (Nat.succ_inj (n + 1) (S n) (Nat.succ_inj (S (n + 1)) (S (S n)) (@add_comm (S (S n)) (S O)))) as p.
    all: rewrite p; symmetry.
    all: apply mat_ccast_refl.
Qed.

Lemma mat_swap_1n_suppl_ge_2: forall {n} (H: n >= 2),
  mat_swap_1n n = mat_ccast (mat_swap_1n_suppl (n - 2))
  (eq_trans (Nat.add_comm 2 (n - 2)) (Nat.sub_add 2 n H)).
Proof.
  intros.
  unfold mat_swap_1n.
  destruct n as [|[|n']]; try lia.
  cbn [Nat.sub].
  remember (eq_trans (Nat.add_comm 2 (n' - 0)) (Nat.sub_add 2 (S (S n')) H)) as p.
  clear Heqp.
  revert p.
  rewrite (Nat.sub_0_r n').
  intro p.
  rewrite mat_ccast_refl.
  reflexivity.
Qed.

Lemma mat_swap_valid_left_id:
  forall {n q1 q2} (Hq1: q1 < n) (Hq2: q2 < n) (H: q1 < q2) (Hcast: (q1 + (q2 - q1 + 1) + (n - q2 - 1))%nat = n),
  @mat_swap n q1 q2 = 
  mat_ccast ((@mat_eye q1) ⊗ mat_swap_1n (q2 - q1 + 1) ⊗ @mat_eye (n - q2 - 1))
  Hcast.
Proof.
  intros.
  unfold mat_swap.
  destruct (lt_dec q1 n) as [H1|H1];
  destruct (lt_dec q2 n) as [H2|H2].
  all: try lia.
  destruct (lt_eq_lt_dec q1 q2) as [[Hlt|Heq]|Hgt].
  all: try lia.
  rewrite <- mat_cast_eq_rect.
  rewrite mat_cast_ccast.
  match goal with
  | |- mat_ccast ?X ?p0 = ?Y =>
      remember p0 as p
  end.
  apply mat_ccast_refl'.
Qed.

Lemma mat_swap_valid_right_id:
  forall {n q1 q2} (Hq1: q1 < n) (Hq2: q2 < n) (H: q1 > q2) (Hcast: (q2 + (q1 - q2 + 1) + (n - q1 - 1))%nat = n),
  mat_swap q1 q2 = 
  mat_ccast ((@mat_eye q2) ⊗ mat_swap_1n (q1 - q2 + 1) ⊗ @mat_eye (n - q1 - 1)) Hcast.
Proof.
  intros.
  unfold mat_swap.
  destruct (lt_dec q1 n) as [H1|H1];
  destruct (lt_dec q2 n) as [H2|H2].
  all: try lia.
  destruct (lt_eq_lt_dec q1 q2) as [[Hlt|Heq]|Hgt].
  all: try lia.
  rewrite <- mat_cast_eq_rect.
  rewrite mat_cast_ccast.
  match goal with
  | |- mat_ccast ?X ?p0 = ?Y =>
      remember p0 as p
  end.
  apply mat_ccast_refl'.
Qed.

Lemma mat_swap_symm:
  forall {n q1 q2} (Hq1: q1 < n) (Hq2: q2 < n),
  @mat_swap n q1 q2 = mat_swap q2 q1.
Proof.
  intros.
  destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
  - assert (Hcast: (q1 + (q2 - q1 + 1) + (n - q2 - 1))%nat = n) by lia.
    rewrite (mat_swap_valid_left_id Hq1 Hq2 H Hcast).
    rewrite (mat_swap_valid_right_id Hq2 Hq1 H Hcast).
    reflexivity.
  - rewrite H. reflexivity.
  - assert (Hcast: (q2 + (q1 - q2 + 1) + (n - q1 - 1))%nat = n) by lia.
    rewrite (mat_swap_valid_left_id Hq2 Hq1 H Hcast).
    rewrite (mat_swap_valid_right_id Hq1 Hq2 H Hcast).
    reflexivity.
Qed.

Lemma mat_swap_id' :
  forall {n c t},
    c < n -> t < n -> c <> t -> c < t ->
    @mat_swap n c t
    =
      mat_single n c mat_proj0_base * mat_single n t mat_proj0_base
    + mat_single n c mat_proj1_base * mat_single n t mat_proj1_base
    + mat_single n c mat_x01        * mat_single n t mat_x10
    + mat_single n c mat_x10        * mat_single n t mat_x01.
Proof.
  intros n c t Hcn Htn Hct H.
  assert (Hcast: (c + (t - c + 1) + (n - t - 1))%nat = n) by lia.
  rewrite (mat_swap_valid_left_id Hcn Htn H Hcast).
  assert (Hswap: t - c + 1 >= 2) by lia.
  rewrite (mat_swap_1n_suppl_ge_2 Hswap).
  rewrite (mat_swap_1n_suppl_id).
  rewrite <- Hcast.
  rewrite mat_ccast_refl.
  repeat rewrite (@mat_single_break_left _ (n - t - 1)%nat); try lia.
  repeat rewrite (@mat_single_break_right c); try lia.
  repeat rewrite tprod_mul.
  repeat rewrite mat_mul_eye_r.
  repeat rewrite <- tprod_add_dist_r.
  repeat rewrite <- tprod_add_dist_l.
  f_equal; f_equal.
  rewrite <- mat_ccast_trans.
  replace (c - c)%nat with 0 by lia.
  match goal with
  | |- mat_ccast ?X ?p0 = ?Y =>
      remember p0 as p
  end.
  clear Heqp.
  revert p.
  replace (t - c + 1 - 2)%nat with (t - c - 1)%nat by lia.
  replace (t - c + 1)%nat with (S (t - c))%nat by lia.
  intro p.
  assert (Hn: 0 <> (t - c)%nat) by lia.
  assert (Hcast': (1 + ((t - c) - 1) + 1)%nat = S ((t - c))) by lia.
  repeat rewrite (mat_single_start_end_id _ _ Hn Hcast').
  repeat rewrite <- tprod_assoc.
  unfold mat_proj0_base at 2, mat_proj1_base at 2, mat_x01 at 2, mat_x10 at 2.
  repeat rewrite tprod_one_step.
  mat_simpl.
  repeat rewrite <- mat_ccast_trans.
  repeat rewrite mat_add_ccast.
  mat_simpl.
  f_equal.
  all: unfold mat_x10.
  all: apply mat_ccast_refl'.
Qed.

Lemma mat_swap_id :
  forall {n c t},
    c < n -> t < n -> c <> t ->
    @mat_swap n c t
    =
      mat_single n c mat_proj0_base * mat_single n t mat_proj0_base
    + mat_single n c mat_proj1_base * mat_single n t mat_proj1_base
    + mat_single n c mat_x01        * mat_single n t mat_x10
    + mat_single n c mat_x10        * mat_single n t mat_x01.
Proof.
  intros n c t Hcn Htn Hct.
  destruct (lt_eq_lt_dec c t) as [[H|H]|H]; try lia.
  - apply mat_swap_id'.
    all: assumption.
  - rewrite mat_swap_symm.
    repeat rewrite (@mat_single_commute n c t).
    all: try assumption.
    rewrite <- mat_add_assoc.
    rewrite (mat_add_comm (mat_single n t mat_x10 * mat_single n c mat_x01)).
    rewrite mat_add_assoc.
    apply mat_swap_id'.
    all: lia.
Qed.

Lemma mat_swap_eq :
  forall {n c},
    c < n ->
    mat_swap c c = @mat_eye n.
Proof.
  intros n c H.
  unfold mat_swap.
  destruct (lt_dec c n); try lia.
  destruct (lt_eq_lt_dec c c) as [[Hc|Hc]|Hc]; try lia.
  reflexivity.
Qed.

Lemma mat_swap_out_of_bounds:
  forall {n q1 q2},
  (n <= q1 \/ n <= q2) ->
  @mat_swap n q1 q2 = mat_eye.
Proof.
  intros n q1 q2 H.
  unfold mat_swap.
  destruct (lt_dec q1 n) as [H1|H1];
  destruct (lt_dec q2 n) as [H2|H2].
  all: try lia.
  all: reflexivity.
Qed.

Lemma swap_swap_qbit:
  forall (qbit1 qbit2: nat) (tq: nat),
  swap_qbit qbit1 qbit2
  (swap_qbit qbit1 qbit2 tq) = tq.
Proof.
  intros q1 q2 tq.
  unfold swap_qbit.
  destruct (Nat.eq_dec tq q1) as [H1|H1].
  - destruct (Nat.eq_dec q2 q1) as [H2|H2]; try lia.
    destruct (Nat.eq_dec q2 q2) as [H3|H3]; try lia.
  - destruct (Nat.eq_dec tq q2) as [H2|H2].
    + destruct (Nat.eq_dec q1 q1) as [H3|H3]; try lia.
    + destruct (Nat.eq_dec tq q1) as [H3|H3]; try lia.
      destruct (Nat.eq_dec tq q2) as [H4|H4]; try lia.
Qed.

Lemma swap_qbit_right :
  forall qbit1 qbit2,
    swap_qbit qbit1 qbit2 qbit2 = qbit1.
Proof.
  intros qbit1 qbit2.
  unfold swap_qbit.
  destruct (Nat.eq_dec qbit2 qbit1) as [Heq | Hneq].
  - subst. reflexivity.
  - destruct (Nat.eq_dec qbit2 qbit2) as [_ | Hcontra].
    + reflexivity.
    + contradiction.
Qed.

Lemma swap_qbit_left :
  forall qbit1 qbit2,
    swap_qbit qbit1 qbit2 qbit1 = qbit2.
Proof.
  intros qbit1 qbit2.
  unfold swap_qbit.
  destruct (Nat.eq_dec qbit1 qbit1) as [_ | Hcontra].
  - reflexivity.
  - contradiction.
Qed.

Lemma swap_qbit_symm:
  forall (qbit1 qbit2: nat),
    swap_qbit qbit1 qbit2 =
    swap_qbit qbit2 qbit1.
Proof.
  intros qbit1 qbit2.
  apply functional_extensionality.
  intros tq.
  unfold swap_qbit.
  destruct (Nat.eq_dec tq qbit1) as [H1|H1].
  - destruct (Nat.eq_dec tq qbit2) as [H2|H2]; try lia.
  - reflexivity.
Qed.

Lemma swap_qbit_bound:
  forall {qbit1 qbit2 target n: nat},
    qbit1 < n -> qbit2 < n -> target < n ->
    swap_qbit qbit1 qbit2 target < n.
Proof.
  intros qbit1 qbit2 target n Hq1 Hq2 Ht.
  unfold swap_qbit.
  destruct (Nat.eq_dec target qbit1);
  destruct (Nat.eq_dec target qbit2);
  lia.
Qed.

Lemma swap_qbit_out_of_bounds:
  forall {qbit1 qbit2 target n: nat},
    qbit1 < n -> qbit2 < n -> n <= target ->
    n <= swap_qbit qbit1 qbit2 target.
Proof.
  intros qbit1 qbit2 target n Hq1 Hq2 Ht.
  unfold swap_qbit.
  destruct (Nat.eq_dec target qbit1);
  destruct (Nat.eq_dec target qbit2);
  lia.
Qed.

Lemma swap_qbit_eq_iff :
  forall qbit1 qbit2 qbit result,
    swap_qbit qbit1 qbit2 qbit = result ->
    qbit = swap_qbit qbit1 qbit2 result.
Proof.
  intros qbit1 qbit2 qbit result H.
  rewrite <- H.
  rewrite swap_swap_qbit.
  reflexivity.
Qed.

Lemma swap_qbit_neq :
  forall qbit1 qbit2 qbit result,
    qbit <> result ->
    qbit1 <> result ->
    qbit2 <> result ->
    swap_qbit qbit1 qbit2 qbit <> result.
Proof.
  intros qbit1 qbit2 qbit result Hqbit Hqbit1 Hqbit2 Heq.
  apply swap_qbit_eq_iff in Heq.
  unfold swap_qbit in Heq.
  destruct (Nat.eq_dec result qbit1) as [Hres1 | Hres1];
    [subst; contradiction |].
  destruct (Nat.eq_dec result qbit2) as [Hres2 | Hres2];
    [subst; contradiction |].
  contradiction.
Qed.

Lemma NoDup_map_swap_qbit :
  forall qbit1 qbit2 qbits,
    NoDup qbits ->
    NoDup (map (swap_qbit qbit1 qbit2) qbits).
Proof.
  intros qbit1 qbit2 qbits Hnodup.
  induction Hnodup as [| qbit qbits Hnotin Hnodup IH].
  - constructor.
  - simpl.
    constructor.
    + intros Hin.
      apply in_map_iff in Hin as [qbit' [Heq Hin]].
      apply Hnotin.
      apply swap_qbit_eq_iff in Heq.
      subst.
      rewrite swap_swap_qbit in Hin.
      exact Hin.
    + exact IH.
Qed.

Lemma mat_swap2_commute:
  forall (U1 U2: Matrix 1),
    (U1 ⊗ U2) * mat_swap2 = mat_swap2 * (U2 ⊗ U1).
Proof.
  intros U1 U2.
  destruct (mat_1_inv U1) as [a1 [b1 [c1 [d1 H1]]]]; subst.
  destruct (mat_1_inv U2) as [a2 [b2 [c2 [d2 H2]]]]; subst.
  unfold mat_swap2.
  mat_simpl.
  f_equal; f_equal; f_equal; lca.
Qed.

Lemma mat_swap_1n_single_commute':
  forall {n} (U: Matrix 1),
    mat_swap_1n (S n) * mat_single (S n) 0 U =
    mat_single (S n) n U * mat_swap_1n (S n).
Proof.
  intros n U.
  destruct n.
  - destruct (mat_1_inv U) as [a [b [c [d H]]]]; subst.
    mat_simpl.
    f_equal; f_equal; lca.
  - unfold mat_swap_1n.
    induction n.
    + unfold mat_swap_1n_suppl, mat_single.
      rewrite mat_swap2_commute.
      f_equal; f_equal.
      destruct (mat_1_inv U) as [a [b [c [d H]]]]; subst.
      simpl.
      f_equal; f_equal; lca.
    + cbn [mat_swap_1n_suppl].
      replace (mat_single (S (S (S n))) 0 U) with
      (U ⊗ @mat_eye 1 ⊗ @mat_eye (S n)).
      repeat rewrite <- mat_mul_assoc.
      rewrite (tprod_mul 2 (S n)), <- mat_swap2_commute, <- tprod_mul.
      rewrite (mat_mul_assoc (@mat_eye 1 ⊗ mat_swap_1n_suppl n)).
      rewrite <- tprod_assoc, mat_ccast_refl, tprod_mul.
      replace (U ⊗ @mat_eye (S n)) with (mat_single (S (S n)) 0 U) by reflexivity.
      cbn [Init.Nat.add].
      rewrite IHn, <- tprod_mul.
      replace (mat_single (S (S (S n))) (S (S n)) U) with (@mat_eye 1 ⊗ (@mat_eye 1 ⊗ mat_single (S n) n U)) by reflexivity.
      replace (mat_single (S (S n)) (S n) U) with (@mat_eye 1 ⊗ mat_single (S n) n U) by reflexivity.
      repeat rewrite mat_mul_assoc. f_equal; f_equal.
      replace (@mat_eye 1 ⊗ (@mat_eye 1 ⊗ mat_single (S n) n U)) with
      (@mat_eye 1 ⊗ @mat_eye 1 ⊗ mat_single (S n) n U).
      rewrite (tprod_mul 2 (S n)), mat_swap2_commute.
      replace (mat_single (S n) n U * @mat_eye (S n)) with
      (@mat_eye (S n) * mat_single (S n) n U) by mat_simpl.
      rewrite <- tprod_mul. f_equal.
      1-2: rewrite <- (tprod_assoc (@mat_eye 1)), mat_ccast_refl.
      3: cbn [mat_single].
      3: replace (@mat_eye (S (S n))) with (@mat_eye 1 ⊗ @mat_eye (S n)) by apply tprod_eye_eye.
      3: rewrite <- (tprod_assoc U), mat_ccast_refl.
      all: reflexivity.
Qed.

Lemma mat_swap_single_commute':
  forall {n q1 q2} (U: Matrix 1),
    q1 < n -> q2 < n ->
    mat_single n q2 U * mat_swap q1 q2 =
    mat_swap q1 q2 * mat_single n q1 U.
Proof.
  intros n q1 q2 U Hq1 Hq2.
  destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
  - assert (Hcast: (q1 + (q2 - q1 + 1) + (n - q2 - 1))%nat = n) by lia.
    rewrite (mat_swap_valid_left_id Hq1 Hq2 H Hcast).
    rewrite <- Hcast. mat_cast.
    rewrite mat_single_break_left; try lia.
    rewrite mat_single_break_right; try lia.
    symmetry.
    rewrite mat_single_break_left; try lia.
    rewrite mat_single_break_right; try lia.
    repeat rewrite tprod_mul. mat_simpl.
    f_equal; f_equal.
    replace (q2 - q1 + 1)%nat with (S (q2 - q1))%nat by lia.
    replace (q1 - q1)%nat with 0%nat by lia.
    apply mat_swap_1n_single_commute'.
  - rewrite <- H.
    unfold mat_swap.
    destruct (lt_dec q1 n); try lia.
    destruct (lt_eq_lt_dec q1 q1) as [[H'|H']|H']; try lia.
    mat_simpl.
  - rewrite mat_swap_symm; try lia.
    assert (Hcast: (q2 + (q1 - q2 + 1) + (n - q1 - 1))%nat = n) by lia.
    rewrite (mat_swap_valid_left_id Hq2 Hq1 H Hcast).
    rewrite <- Hcast. mat_cast.
    rewrite mat_single_break_left; try lia.
    rewrite mat_single_break_right; try lia.
    symmetry.
    rewrite mat_single_break_left; try lia.
    rewrite mat_single_break_right; try lia.
    repeat rewrite tprod_mul. mat_simpl.
    f_equal; f_equal.
    replace (q1 - q2 + 1)%nat with (S (q1 - q2))%nat by lia.
    replace (q2 - q2)%nat with 0%nat by lia.
    assert (HE: mat_swap_1n (S (q1 - q2)) * mat_swap_1n (S (q1 - q2)) * mat_single (S (q1 - q2)) 0 U * mat_swap_1n (S (q1 - q2)) =
    mat_swap_1n (S (q1 - q2)) * mat_single (S (q1 - q2)) (q1 - q2) U * mat_swap_1n (S (q1 - q2)) * mat_swap_1n (S (q1 - q2))).
    {
      f_equal. repeat rewrite <- mat_mul_assoc.
      f_equal. rewrite mat_swap_1n_single_commute'.
      reflexivity.
    }
    assert (Hinv: mat_swap_1n (S (q1 - q2)) * mat_swap_1n (S (q1 - q2)) = mat_eye).
    {
      rewrite <- mat_swap_1n_Hermitian at 2.
      apply mat_swap_1n_unitary.
    }
    rewrite Hinv, mat_mul_eye_l in HE.
    rewrite HE, <- mat_mul_assoc, Hinv.
    mat_simpl.
Qed.

Lemma mat_swap_1n_single_indep':
  forall {n q} (U: Matrix 1),
    q <> 0 -> q <> n ->
    mat_single (S n) q U * mat_swap_1n (S n) = mat_swap_1n (S n) * mat_single (S n) q U.
Proof.
  intros n q U Hq0 Hqn.
  destruct n; cbn [mat_swap_1n].
  1: mat_simpl.
  generalize dependent q.
  induction n; intros q Hq0 Hqn.
  - destruct q as [|[|q]]; try lia.
    cbn [mat_single].
    repeat rewrite tprod_eye_eye.
    mat_simpl.
  - cbn [mat_swap_1n_suppl].
    destruct q as [|[|q]]; try lia.
    + cbn [mat_single].
      assert (Hmat: @mat_eye 1 ⊗ (U ⊗ @mat_eye (S n)) = (@mat_eye 1 ⊗ U ⊗ @mat_eye (S n))).
      {
        rewrite <- tprod_assoc, mat_ccast_refl. reflexivity.
      }
      cbn [Init.Nat.add] in Hmat.
      rewrite Hmat.
      repeat rewrite mat_mul_assoc.
      rewrite (tprod_mul 2 (S n)), mat_swap2_commute, <- tprod_mul.
      repeat rewrite <- mat_mul_assoc.
      rewrite (tprod_mul 2 (S n)), <- mat_swap2_commute, <- tprod_mul.
      f_equal. repeat rewrite mat_mul_assoc. f_equal.
      cbn [Init.Nat.add].
      rewrite <- (tprod_assoc U), mat_ccast_refl, tprod_eye_eye.
      repeat rewrite (tprod_mul 1 (S (S n))).
      mat_simpl.
    + replace (mat_single (S (S (S n))) (S (S q)) U) with
      (@mat_eye 1 ⊗ @mat_eye 1 ⊗ mat_single (S n) q U).
      repeat rewrite mat_mul_assoc.
      rewrite (tprod_mul 2 (S n)), mat_swap2_commute, mat_eye_commute, <- tprod_mul.
      repeat rewrite <- mat_mul_assoc.
      rewrite (tprod_mul 2 (S n)), <- mat_swap2_commute, <- mat_eye_commute, <- tprod_mul.
      f_equal. repeat rewrite mat_mul_assoc. f_equal.
      cbn [Init.Nat.add].
      rewrite <- (tprod_assoc (@mat_eye 1) mat_eye), mat_ccast_refl.
      repeat rewrite (tprod_mul 1 (S (S n))). f_equal.
      replace ((@mat_eye 1) ⊗ mat_single (S n) q U) with (mat_single (S (S n)) (S q) U) by reflexivity.
      apply IHn.
      all: try lia.
      rewrite <- tprod_assoc, mat_ccast_refl.
      reflexivity.
Qed.

Lemma mat_swap_single_indep':
  forall {n q1 q2 target} (U: Matrix 1),
    q1 < n -> q2 < n -> target <> q1 -> target <> q2 -> q1 < q2 ->
    mat_single n target U * mat_swap q1 q2 = mat_swap q1 q2 * mat_single n target U.
Proof.
  intros n q1 q2 target U Hq1 Hq2 Ht1 Ht2 H.
  assert (Hcast: (q1 + (q2 - q1 + 1) + (n - q2 - 1))%nat = n) by lia.
  rewrite (mat_swap_valid_left_id Hq1 Hq2 H Hcast), <- Hcast.
  mat_cast. clear Hcast.
  destruct (lt_eq_lt_dec target q2) as [[Ht | Ht] | Ht]; try lia.
  - rewrite mat_single_break_left; try lia.
    repeat rewrite tprod_mul. f_equal.
    destruct (lt_eq_lt_dec target q1) as [[Ht' | Ht'] | Ht']; try lia.
    + rewrite mat_single_break_left; try lia.
      repeat rewrite tprod_mul.
      mat_simpl.
    + rewrite mat_single_break_right; try lia.
      repeat rewrite tprod_mul. f_equal.
      replace (q2 - q1 + 1)%nat with (S (q2 - q1))%nat by lia.
      apply mat_swap_1n_single_indep'.
      all: lia.
  - rewrite mat_single_break_right; try lia.
    repeat rewrite tprod_mul.
    mat_simpl.
Qed.

Lemma mat_swap_single_indep:
  forall {n q1 q2 target} (U: Matrix 1),
    q1 < n -> q2 < n -> target <> q1 -> target <> q2 ->
    mat_single n target U * mat_swap q1 q2 = mat_swap q1 q2 * mat_single n target U.
Proof.
  intros n q1 q2 target U Hq1 Hq2 Ht1 Ht2.
  destruct (lt_eq_lt_dec q1 q2) as [[H|H]|H].
  - apply mat_swap_single_indep'.
    all: assumption.
  - rewrite <- H.
    unfold mat_swap.
    destruct (lt_dec q1 n); try lia.
    destruct (lt_eq_lt_dec q1 q1) as [[H'|H']|H']; try lia.
    mat_simpl.
  - rewrite mat_swap_symm.
    apply mat_swap_single_indep'.
    all: assumption.
Qed.

Lemma mat_swap_single_commute:
  forall {n q1 q2} (target: nat) (U: Matrix 1),
    q1 < n -> q2 < n ->
    mat_single n (swap_qbit q1 q2 target) U * mat_swap q1 q2 =
    mat_swap q1 q2 * mat_single n target U.
Proof.
  intros n q1 q2 target U Hq1 Hq2.
  unfold swap_qbit.
  destruct (Nat.eq_dec target q1).
  - subst. apply mat_swap_single_commute'.
    all: assumption.
  - destruct (Nat.eq_dec target q2).
    + subst. rewrite mat_swap_symm.
      apply mat_swap_single_commute'.
      all: assumption.
    + apply mat_swap_single_indep.
      all: assumption.
Qed.

Lemma mat_swap_single_commute_right:
  forall {n q1 q2} (target: nat) (U: Matrix 1),
    q1 < n -> q2 < n ->
    mat_single n target U * mat_swap q1 q2 =
    mat_swap q1 q2 * mat_single n (swap_qbit q1 q2 target) U.
Proof.
  intros n q1 q2 target U Hq1 Hq2.
  replace (mat_single n (swap_qbit q1 q2 target) U) with
  (mat_single n (swap_qbit q1 q2 target) U * mat_eye) by mat_simpl.
  rewrite <- (proj1 (@mat_swap_unitary n q1 q2)).
  rewrite mat_swap_Hermitian.
  rewrite (mat_mul_assoc _ (mat_swap q1 q2) _).
  rewrite (mat_swap_single_commute _ _ Hq1 Hq2).
  repeat rewrite mat_mul_assoc.
  rewrite <- mat_swap_Hermitian at 2.
  rewrite (proj1 mat_swap_unitary).
  mat_simpl.
Qed.

Lemma mat_swap_proj0_commute:
  forall {n q1 q2} (target: nat),
    q1 < n -> q2 < n ->
    mat_proj0 n (swap_qbit q1 q2 target) * mat_swap q1 q2 =
    mat_swap q1 q2 * mat_proj0 n target.
Proof.
  intros n q1 q2 target Hq1 Hq2.
  destruct (le_lt_dec n target).
  - repeat rewrite mat_proj0_out_of_bounds.
    mat_simpl.
    apply l.
    apply (swap_qbit_out_of_bounds Hq1 Hq2 l).
  - repeat rewrite mat_proj0_eq_mat_single.
    rewrite mat_swap_single_commute.
    reflexivity.
    4: apply swap_qbit_bound.
    all: try apply Hq1.
    all: try apply Hq2.
    all: try apply l.
Qed.

Lemma mat_swap_proj1_commute:
  forall {n q1 q2} (target: nat),
    q1 < n -> q2 < n ->
    mat_proj1 n (swap_qbit q1 q2 target) * mat_swap q1 q2 =
    mat_swap q1 q2 * mat_proj1 n target.
Proof.
  intros n q1 q2 target Hq1 Hq2.
  destruct (le_lt_dec n target).
  - repeat rewrite mat_proj1_out_of_bounds.
    mat_simpl.
    apply l.
    apply (swap_qbit_out_of_bounds Hq1 Hq2 l).
  - repeat rewrite mat_proj1_eq_mat_single.
    rewrite mat_swap_single_commute.
    reflexivity.
    4: apply swap_qbit_bound.
    all: try apply Hq1.
    all: try apply Hq2.
    all: try apply l.
Qed.

End SWAP_PROPERTIES.

Section CNOT_PROPERTIES.

Lemma mat_ctrl_single_unitary : forall {n c t} (U: Matrix 1), mat_unitary U -> mat_unitary (mat_ctrl_single n c t U).
Proof.
  intros n c t U HU.
  revert c t.
  induction n.
  - intros; mat_simpl.
    unfold mat_unitary; split.
    all: repeat (f_equal; simpl; try lca).
  - intros; destruct c, t.
    + unfold mat_unitary; split.
      all: mat_simpl.
      all: repeat (f_equal; simpl).
      all: try apply mat_eye_Hermitian.
      all: try apply mat_0_Hermitian.
    + mat_simpl.
      unfold mat_unitary; split.
      all: mat_simpl.
      all: repeat (f_equal; simpl).
      all: try apply mat_eye_Hermitian.
      all: try rewrite mat_0_Hermitian; auto.
      all: mat_simpl.
      all: apply mat_single_unitary; assumption.
    + destruct HU as [HU0 HU1].
      destruct (mat_proj0_projection n c) as [HP0 HH0].
      destruct (mat_proj1_projection n c) as [HP1 HH1].
      unfold mat_ctrl_single.
      unfold mat_unitary; split.
      all: rewrite mat_add_conjtrans.
      all: repeat (try rewrite mat_mul_dist_l; try rewrite mat_mul_dist_r).
      all: repeat rewrite (@tprod_conjtrans 1 _).
      all: rewrite mat_eye_Hermitian.
      all: repeat rewrite (tprod_mul 1 _).
      all: try rewrite mat_mul_eye_r; try rewrite mat_mul_eye_l.
      all: try rewrite HU0; try rewrite HU1.
      all: try rewrite HH0; try rewrite HH1.
      all: try rewrite HP0; try rewrite HP1.
      all: try rewrite mat_proj_01_perp; try rewrite mat_proj_10_perp.
      all: rewrite mat_mul_eye_r.
      all: repeat rewrite tprod_0_r.
      all: rewrite mat_add_0_r; rewrite mat_add_0_l.
      all: rewrite <- (tprod_add_dist_l 1 _).
      all: rewrite mat_proj_sum.
      all: apply (tprod_eye_eye 1).
  + mat_simpl.
    apply unitary_diagonal.
    all: auto.
Qed.

Lemma mat_not2_unitary : mat_unitary mat_not2.
Proof.
  unfold mat_not2, mat_unitary; simpl; split; repeat f_equal; com_simpl.
Qed.

Lemma mat_cnot_unitary : forall {n qc qt}, mat_unitary (@mat_cnot n qc qt).
Proof.
  intros.
  apply mat_ctrl_single_unitary.
  apply mat_not2_unitary.
Qed.

Lemma mat_ctrl_single_Hermitian : forall {n c t} (U: Matrix 1), mat_Hermitian U -> mat_Hermitian (mat_ctrl_single n c t U).
Proof.
  intros n c t U HU.
  revert c t.
  induction n.
  - intros; mat_simpl.
    unfold mat_Hermitian.
    simpl; f_equal; lca.
  - intros; destruct c, t.
    + unfold mat_ctrl_single.
      apply mat_eye_Hermitian.
    + unfold mat_ctrl_single.
      apply mat_add_Hermitian; apply (tprod_Hermitian (m:=1)).
      * apply mat_proj0_base_Hermitian.
      * apply mat_eye_Hermitian.
      * apply mat_proj1_base_Hermitian.
      * apply mat_single_Hermitian. apply HU.
    + unfold mat_ctrl_single.
      apply mat_add_Hermitian; apply (tprod_Hermitian (m:=1)).
      * apply mat_eye_Hermitian.
      * apply mat_proj0_projection.
      * apply HU.
      * apply mat_proj1_projection.
    + replace (mat_ctrl_single (S n) (S c) (S t) U) with ((@mat_eye 1) ⊗ mat_ctrl_single n c t U) by reflexivity.
      apply (tprod_Hermitian (m:=1)).
      * apply mat_eye_Hermitian.
      * apply IHn.
Qed.

Lemma mat_not2_Hermitian : mat_Hermitian mat_not2.
Proof.
  unfold mat_not2, mat_Hermitian.
  simpl; f_equal; f_equal; lca.
Qed.

Lemma mat_cnot_Hermitian : forall {n c t}, mat_Hermitian (@mat_cnot n c t).
Proof.
  intros.
  apply mat_ctrl_single_Hermitian.
  apply mat_not2_Hermitian.
Qed.

Lemma mat_ctrl_single_left_form:
  forall {n c t} (U : Matrix 1),
  forall (Hcn: c < n) (Htn: t < n) (Hct: c < t) (Hcast: (c + (1 + (n - c - 1)))%nat = n),
    mat_ctrl_single n c t U
    =
    mat_ccast
    ((@mat_eye c) ⊗
      (mat_proj0_base ⊗ mat_eye
       + mat_proj1_base ⊗ mat_single (n - c - 1) (t - c - 1) U))
    Hcast.
Proof.
  intros n c.
  revert n.
  induction c as [|c']; intros.
  - destruct n as [|n']; try lia.
    destruct t as [|t']; try lia.
    unfold mat_ctrl_single.
    replace (S t' - 0 - 1)%nat with t' by lia.
    mat_simpl; simpl. f_equal.
    all: try apply mat_0_ccast.
    all: try apply mat_eye_ccast.
    remember (eq_add_S (n' - 0) n' Hcast) as p.
    rewrite p, mat_ccast_refl.
    reflexivity.
  - destruct n as [|n']; try lia.
    destruct t as [|t']; try lia.
    mat_simpl.
    assert (Hcn': c' < n') by lia.
    assert (Htn': t' < n') by lia.
    assert (Hct': c' < t') by lia.
    assert (Hcast': (c' + (1 + (n' - c' - 1)))%nat = n') by lia.
    rewrite (IHc' n' t' U Hcn' Htn' Hct' Hcast').
    f_equal.
    all: try (rewrite tprod_0_l; apply mat_0_ccast).
    all: mat_simpl.
    all: apply mat_ccast_refl'.
Qed.

Lemma mat_ctrl_single_right_form:
  forall {n c t} (U : Matrix 1),
  forall (Hcn: c < n) (Htn: t < n) (Hct: t < c) (Hcast: (t + (1 + (n - t - 1)))%nat = n),
    mat_ctrl_single n c t U
    =
    mat_ccast
    ((@mat_eye t) ⊗
      (mat_eye ⊗ mat_proj0 (n - t - 1) (c - t - 1) + U ⊗ mat_proj1 (n - t - 1) (c - t - 1)))
    Hcast.
Proof.
  intros n c t.
  revert n c.
  induction t as [|t']; intros.
  - destruct n as [|n']; try lia.
    destruct c as [|c']; try lia.
    unfold mat_ctrl_single.
    replace (S c' - 0 - 1)%nat with c' by lia.
    dependent destruction U.
    mat_simpl. f_equal.
    all: remember (eq_add_S (n' - 0) n' Hcast) as p.
    all: rewrite p, mat_ccast_refl; reflexivity.
  - destruct n as [|n']; try lia.
    destruct c as [|c']; try lia.
    mat_simpl.
    assert (Hcn': c' < n') by lia.
    assert (Htn': t' < n') by lia.
    assert (Hct': t' < c') by lia.
    assert (Hcast': (t' + (1 + (n' - t' - 1)))%nat = n') by lia.
    rewrite (IHt' n' c' U Hcn' Htn' Hct' Hcast').
    f_equal.
    all: try (rewrite tprod_0_l; apply mat_0_ccast).
    all: mat_simpl.
    all: apply mat_ccast_refl'.
Qed.

Lemma mat_ctrl_single_id:
  forall {n c t} (U: Matrix 1),
    c < n -> t < n -> c <> t ->
    mat_ctrl_single n c t U =
    mat_single n c mat_proj0_base
    + mat_single n c mat_proj1_base * mat_single n t U.
Proof.
  intros n c t U Hcn Htn Hct.
  revert c t Hcn Htn Hct.
  induction n; intros c t Hcn Htn Hct; try lia.
  destruct c, t; try lia.
  - cbn [mat_ctrl_single mat_single].
    rewrite (tprod_mul 1 n).
    mat_simpl.
  - cbn [mat_ctrl_single mat_single].
    rewrite (tprod_mul 1 n).
    rewrite mat_mul_eye_l, mat_mul_eye_r.
    assert (Hcn' : c < n) by lia.
    assert (Hcast : (c + 1 + (n - c - 1))%nat = n) by lia.
    rewrite (mat_proj0_id Hcn' Hcast).
    rewrite (mat_proj1_id Hcn' Hcast).
    rewrite <- (mat_single_id _ Hcn' Hcast).
    rewrite <- (mat_single_id _ Hcn' Hcast).
    reflexivity.
  - cbn [mat_ctrl_single mat_single].
    assert (Hcn' : c < n) by lia.
    assert (Htn' : t < n) by lia.
    assert (Hct' : c <> t) by lia.
    rewrite (IHn c t Hcn' Htn' Hct').
    rewrite tprod_add_dist_l.
    rewrite (tprod_mul 1 n).
    mat_simpl.
Qed.

Lemma mat_ctrl_single_eq: 
  forall {n c} (U: Matrix 1),
  mat_ctrl_single n c c U = mat_eye.
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - simpl. destruct c.
    + reflexivity.
    + mat_simpl. f_equal; apply IHn.
Qed.

Lemma mat_ctrl_single_out_of_bounds:
  forall {n c t} (U: Matrix 1),
  (n <= c \/ n <= t) ->
  mat_ctrl_single n c t U = mat_eye.
Proof.
  intros n c t U.
  revert c t.
  induction n; intros.
  - reflexivity.
  - destruct c; destruct t; try lia; cbn [mat_ctrl_single].
    + rewrite mat_single_out_of_bounds.
      rewrite <- tprod_add_dist_r.
      rewrite mat_proj_base_sum.
      apply (tprod_eye_eye 1 n).
      lia.
    + rewrite mat_proj0_out_of_bounds.
      rewrite mat_proj1_out_of_bounds.
      rewrite tprod_eye_eye, tprod_0_r.
      mat_simpl.
      all: lia.
    + rewrite IHn.
      apply (tprod_eye_eye 1 n).
      lia.
Qed.

Theorem mat_3cnot_swap : forall {n c t},
  @mat_cnot n c t * mat_cnot t c * mat_cnot c t = mat_swap c t.
Proof.
  intros.
  unfold mat_cnot.
  destruct (lt_dec c n) as [H1|H1] eqn:H1'.
  - destruct (lt_dec t n) as [H2|H2] eqn:H2'.
    + destruct (Nat.eq_dec c t) as [Hct|Hct] eqn:H3.
      * rewrite Hct.
        rewrite mat_ctrl_single_eq.
        rewrite (mat_swap_eq H2).
        mat_simpl.
      * repeat rewrite mat_ctrl_single_id; try lia.
        rewrite mat_swap_id; try lia.
        rewrite (mat_add_comm (mat_single n t _)).
        rewrite (@mat_single_commute n t c mat_proj1_base); try lia.
        repeat rewrite mat_mul_dist_l.
        repeat rewrite mat_mul_dist_r.
        repeat rewrite mat_mul_assoc.
        repeat rewrite mat_add_assoc.
        repeat (
          rewrite mat_single_factorized ||
          rewrite mat_single_ctc_reduce ||
          rewrite mat_single_ctt_reduce
        ).
        all: try lia.
        unfold mat_proj0_base, mat_proj1_base, mat_not2, mat_x01, mat_x10.
        mat_simpl. com_simpl.
        replace (rec_mat (bas_mat 0%R) (bas_mat 0%R) (bas_mat 0%R) (bas_mat 0%R)) with (@mat_0 1) by reflexivity.
        repeat rewrite mat_single_0; try lia.
        mat_simpl.
        replace (RTC 0%R) with (NTC 0) by lca.
        fold mat_proj0_base mat_proj1_base mat_x01 mat_x10.
        rewrite (mat_add_comm (mat_single n c mat_x10 * _)).
        repeat rewrite <- mat_add_assoc. f_equal.
        rewrite (mat_add_comm (mat_single n c mat_proj1_base * _)).
        repeat rewrite mat_add_assoc. f_equal.
        apply mat_add_comm.
    + repeat rewrite mat_ctrl_single_out_of_bounds; try lia.
      rewrite mat_swap_out_of_bounds; try lia.
      mat_simpl.
  - repeat rewrite mat_ctrl_single_out_of_bounds; try lia.
    rewrite mat_swap_out_of_bounds; try lia.
    mat_simpl.
Qed.

Lemma mat_ctrl_single_extend_right :
  forall {n extra c t} (U : Matrix 1),
    c < n ->
    t < n ->
    c <> t ->
    mat_ctrl_single (n + extra) c t U =
    mat_ctrl_single n c t U ⊗ @mat_eye extra.
Proof.
  intros n extra c t U Hc Ht Hneq.
  repeat rewrite mat_ctrl_single_id; try lia.
  repeat rewrite mat_single_break_left; try lia.
  rewrite tprod_add_dist_r.
  rewrite tprod_mul.
  mat_simpl.
Qed.

Lemma mat_cnot_extend_right :
  forall {n extra c t},
    c < n ->
    t < n ->
    c <> t ->
    @mat_cnot (n + extra) c t =
    @mat_cnot n c t ⊗ @mat_eye extra.
Proof.
  intros n extra c t Hc Ht Hneq.
  unfold mat_cnot.
  apply mat_ctrl_single_extend_right; assumption.
Qed.

Lemma mat_swap_extend_right :
  forall {n extra q1 q2},
    q1 < n ->
    q2 < n ->
    q1 <> q2 ->
    @mat_swap (n + extra) q1 q2 =
    @mat_swap n q1 q2 ⊗ @mat_eye extra.
Proof.
  intros n extra q1 q2 Hq1 Hq2 Hneq.
  rewrite <- (@mat_3cnot_swap (n + extra) q1 q2).
  rewrite <- (@mat_3cnot_swap n q1 q2).
  repeat rewrite mat_cnot_extend_right; try lia.
  repeat rewrite tprod_mul.
  mat_simpl.
Qed.

Lemma mat_swap_ctrl_commute:
  forall {n q1 q2} (c t: nat) (U: Matrix 1),
    q1 < n -> q2 < n ->
    mat_ctrl_single n (swap_qbit q1 q2 c) (swap_qbit q1 q2 t) U * mat_swap q1 q2 =
    mat_swap q1 q2 * mat_ctrl_single n c t U.
Proof.
  intros n q1 q2 c t U Hq1 Hq2.
  destruct (le_lt_dec n c) as [Hc|Hc].
  - assert (Hc': n <= swap_qbit q1 q2 c) by
      apply (swap_qbit_out_of_bounds Hq1 Hq2 Hc).
    rewrite mat_ctrl_single_out_of_bounds.
    rewrite mat_ctrl_single_out_of_bounds.
    mat_simpl.
    all: lia.
  - destruct (le_lt_dec n t) as [Ht|Ht].
    + assert (Ht': n <= swap_qbit q1 q2 t) by
        apply (swap_qbit_out_of_bounds Hq1 Hq2 Ht).
      rewrite mat_ctrl_single_out_of_bounds.
      rewrite mat_ctrl_single_out_of_bounds.
      mat_simpl.
      all: lia.
    + destruct (Nat.eq_dec c t) as [Hct|Hct].
      * rewrite Hct.
        rewrite mat_ctrl_single_eq.
        rewrite mat_ctrl_single_eq.
        mat_simpl.
      * rewrite mat_ctrl_single_id.
        rewrite mat_ctrl_single_id.
        rewrite mat_mul_dist_l, mat_mul_dist_r.
        f_equal.
        apply (mat_swap_single_commute _ _ Hq1 Hq2).
        rewrite <- mat_mul_assoc.
        rewrite (mat_swap_single_commute _ _ Hq1 Hq2).
        repeat rewrite mat_mul_assoc.
        rewrite (mat_swap_single_commute _ _ Hq1 Hq2).
        reflexivity.
        all: try assumption.
        1-2: apply swap_qbit_bound.
        all: try assumption.
        intro Heq.
        apply Hct.
        apply (f_equal (swap_qbit q1 q2)) in Heq.
        do 2 rewrite swap_swap_qbit in Heq.
        exact Heq.
Qed.

Lemma mat_swap_swap_commute:
  forall {n q1 q2} (c t: nat),
    q1 < n -> q2 < n ->
    mat_swap (swap_qbit q1 q2 c) (swap_qbit q1 q2 t) * @mat_swap n q1 q2 =
    mat_swap q1 q2 * mat_swap c t.
Proof.
  intros n q1 q2 c t Hq1 Hq2.
  remember (swap_qbit q1 q2 c) as c'.
  remember (swap_qbit q1 q2 t) as t'.
  rewrite <- (mat_3cnot_swap).
  rewrite Heqc', Heqt'.
  repeat rewrite <- mat_mul_assoc.
  unfold mat_cnot.
  rewrite (mat_swap_ctrl_commute c t _ Hq1 Hq2).
  rewrite (mat_mul_assoc _ (mat_swap q1 q2) _).
  rewrite (mat_swap_ctrl_commute t c _ Hq1 Hq2).
  rewrite <- mat_mul_assoc.
  rewrite (mat_mul_assoc _ (mat_swap q1 q2) _).
  rewrite (mat_swap_ctrl_commute c t _ Hq1 Hq2).
  rewrite <- (@mat_3cnot_swap n c t).
  unfold mat_cnot.
  repeat rewrite <- mat_mul_assoc.
  reflexivity.
Qed.


End CNOT_PROPERTIES.
