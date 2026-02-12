Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.Single.
Require Import QASMInfer.operator.Projection.

Bind Scope Complex_scope with Complex.
Open Scope Matrix_scope.

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

End SWAP.


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

Lemma mat_swap_1n_suppl_id: forall {n a b c d},
  mat_swap2 = rec_mat a b c d ->
  mat_swap_1n_suppl n = mat_ccast (rec_mat (mat_eye ⊗ a) (mat_eye ⊗ b) (mat_eye ⊗ c) (mat_eye ⊗ d)) (@add_comm (S n) 1).
Proof.
  intros n a b c d H.
  induction n.
  - simpl.
    rewrite H. f_equal; mat_simpl.
    all: rewrite mat_ccast_refl; reflexivity.
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

End SWAP_PROPERTIES.

Section CNOT.

Fixpoint mat_ctrl_single (n c t: nat) (U: Matrix 1) : Matrix n :=
  match n, c, t with
  | 0, _, _ | S _, 0, 0 => mat_eye
  | S n', 0, S t' => mat_proj0_base ⊗ mat_eye + mat_proj1_base ⊗ mat_single n' t' U
  | S n', S c', 0 => mat_eye ⊗ mat_proj0 n' c' + U ⊗ mat_proj1 n' c'
  | S n', S c', S t' => (@mat_eye 1) ⊗ mat_ctrl_single n' c' t' U
  end.

Definition mat_not2: Matrix 1 := rec_mat (bas_mat 0) (bas_mat 1) (bas_mat 1) (bas_mat 0).

Definition mat_cnot {n} (qc qt: nat) : Matrix n := mat_ctrl_single n qc qt mat_not2.

End CNOT.

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

Lemma mat_ctrl_single_left_form :
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

Lemma mat_ctrl_single_right_form :
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

Lemma mat_ctrl_single_eq_form : 
  forall {n c} (U: Matrix 1),
  mat_ctrl_single n c c U = mat_eye.
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - simpl. destruct c.
    + reflexivity.
    + mat_simpl. f_equal; apply IHn.
Qed.

Lemma mat_3cnot_swap_c_lt_t: forall {n c t}
    (Hcn: c < n) (Htn: t < n) (Hct: c < t),
    @mat_cnot n c t * mat_cnot t c * mat_cnot c t = mat_swap c t.
Proof.
  intros n c t Hcn Htn Hct.
  unfold mat_cnot.
  assert (Hcast_swap: (c + (t - c + 1) + (n - t - 1))%nat = n) by lia.
  rewrite (mat_swap_valid_left_id Hcn Htn Hct Hcast_swap).
  assert (Hcast_ctrl_single: (c + (1 + (n - c - 1)))%nat = n) by lia.
  rewrite (mat_ctrl_single_left_form _ Hcn Htn Hct Hcast_ctrl_single).
  rewrite (mat_ctrl_single_right_form _ Htn Hcn Hct Hcast_ctrl_single).
  simpl. mat_simpl.
  rewrite mat_mul_ccast, mat_mul_ccast.
  rewrite tprod_mul, tprod_mul.
  mat_simpl.
  assert (H: n - c - 1 > t - c - 1) by lia.
  assert (Hcast: (t - c - 1 + 1 + (n - c - 1 - (t - c - 1) - 1))%nat = (n - c - 1)%nat) by lia.
  rewrite (mat_proj0_id H Hcast), (mat_proj1_id H Hcast), (mat_single_id _ H Hcast).
  repeat rewrite mat_mul_ccast.
  rewrite ccast_rec_mat.
  repeat rewrite tprod_mul.
  repeat rewrite mat_mul_eye_r.
  assert (Hswap: t - c + 1 >= 2) by lia.
  rewrite mat_swap_1n_suppl_ge_2 with (H:= Hswap).
  assert (Hmat: mat_swap2 = rec_mat
    mat_proj0_base (mat_proj1_base * mat_not2)
    (mat_not2 * mat_proj1_base) (mat_not2 * mat_proj0_base * mat_not2)).
  {
    unfold mat_swap2. simpl.
    f_equal; f_equal; com_simpl.
  }
  rewrite (mat_swap_1n_suppl_id Hmat); clear Hmat.
  repeat rewrite tprod_ccast_left.
  repeat rewrite tprod_ccast_right.
  symmetry.
  rewrite <- tprod_assoc.
  rewrite tprod_one_step.
  repeat rewrite <- mat_ccast_trans.
  match goal with
  | |- mat_ccast ?X ?p0 = mat_ccast ?Y ?p1 =>
      remember p0 as Hcast1; remember p1 as Hcast2
  end.
  clear HeqHcast1 HeqHcast2.
  revert Hcast1 Hcast2.
  replace (n - c - 1 - (t - c - 1) - 1)%nat with (n - t - 1)%nat by lia.
  replace (t - c + 1 - 2)%nat with (t - c - 1)%nat by lia.
  intros Hcast1 Hcast2.
  apply mat_ccast_refl'.
Qed.

Lemma mat_3cnot_swap_c_gt_t: forall {n c t}
    (Hcn: c < n) (Htn: t < n) (Hct: c > t),
    @mat_cnot n c t * mat_cnot t c * mat_cnot c t = mat_swap c t.
Proof.
  intros n c t Hcn Htn Hct.
  unfold mat_cnot.
  assert (Hcast_swap: (t + (c - t + 1) + (n - c - 1))%nat = n) by lia.
  rewrite (mat_swap_valid_right_id Hcn Htn Hct Hcast_swap).
  assert (Hcast_ctrl_single: (t + (1 + (n - t - 1)))%nat = n) by lia.
  rewrite (mat_ctrl_single_left_form _ Htn Hcn Hct Hcast_ctrl_single).
  rewrite (mat_ctrl_single_right_form _ Hcn Htn Hct Hcast_ctrl_single).
  simpl. mat_simpl.
  rewrite mat_mul_ccast, mat_mul_ccast.
  rewrite tprod_mul, tprod_mul.
  mat_simpl.
  assert (H: n - t - 1 > c - t - 1) by lia.
  assert (Hcast: (c - t - 1 + 1 + (n - t - 1 - (c - t - 1) - 1))%nat = (n - t - 1)%nat) by lia.
  rewrite (mat_proj0_id H Hcast), (mat_proj1_id H Hcast), (mat_single_id _ H Hcast).
  repeat rewrite mat_mul_ccast.
  repeat rewrite mat_add_ccast.
  rewrite ccast_rec_mat.
  repeat rewrite tprod_mul.
  repeat rewrite mat_mul_eye_r.
  repeat rewrite <- tprod_add_dist_r.
  repeat rewrite <- tprod_add_dist_l.
  assert (Hswap: c - t + 1 >= 2) by lia.
  rewrite mat_swap_1n_suppl_ge_2 with (H:= Hswap).
  remember (mat_proj0_base * mat_proj0_base + mat_proj1_base * mat_not2 * mat_proj1_base) as P0.
  remember (mat_proj0_base * mat_proj1_base + mat_proj1_base * mat_not2 * mat_proj0_base) as P1.
  remember (mat_proj1_base * mat_proj0_base + mat_proj0_base * mat_not2 * mat_proj1_base) as P2.
  remember (mat_proj1_base * mat_proj1_base + mat_proj0_base * mat_not2 * mat_proj0_base) as P3.
  assert (Hmat: mat_swap2 = rec_mat P0 P1 P2 P3).
  {
    unfold mat_swap2. rewrite HeqP0, HeqP1, HeqP2, HeqP3. mat_simpl.
    f_equal; f_equal; com_simpl.
  }
  rewrite (mat_swap_1n_suppl_id Hmat); clear Hmat.
  repeat rewrite tprod_ccast_left.
  repeat rewrite tprod_ccast_right.
  symmetry.
  rewrite <- tprod_assoc.
  rewrite tprod_one_step.
  repeat rewrite <- mat_ccast_trans.
  match goal with
  | |- mat_ccast ?X ?p0 = mat_ccast ?Y ?p1 =>
      remember p0 as Hcast1; remember p1 as Hcast2
  end.
  clear HeqHcast1 HeqHcast2.
  revert Hcast1 Hcast2.
  replace (n - t - 1 - (c - t - 1) - 1)%nat with (n - c - 1)%nat by lia.
  replace (c - t + 1 - 2)%nat with (c - t - 1)%nat by lia.
  intros Hcast1 Hcast2.
  apply mat_ccast_refl'.
Qed.

Theorem mat_3cnot_swap : forall {n c t} (Hcn: c < n) (Htn: t < n),
  @mat_cnot n c t * mat_cnot t c * mat_cnot c t = mat_swap c t.
Proof.
  intros.
  destruct (lt_dec c n) as [H1|H1] eqn:H1';
  destruct (lt_dec t n) as [H2|H2] eqn:H2'.
  all: try lia.
  destruct (lt_eq_lt_dec c t) as [[Hlt|Heq]|Hgt] eqn:H3.
  - apply (mat_3cnot_swap_c_lt_t H1 H2 Hlt).
  - unfold mat_cnot, mat_swap.
    rewrite H1', H2', H3, Heq.
    rewrite mat_ctrl_single_eq_form.
    mat_simpl.
  - apply (mat_3cnot_swap_c_gt_t H1 H2 Hgt).
Qed.

End CNOT_PROPERTIES.
