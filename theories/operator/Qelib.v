(* Canonical qelib1 matrices and bodies.  Lists are in source execution order;
   the denotation multiplies the last operation on the left. *)
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.Single.
Require Import QASMInfer.operator.Multiple.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Matrix_scope.

Definition Gate_X_matrix: Matrix 1 :=
  rec_mat (bas_mat 0) (bas_mat 1)
          (bas_mat 1) (bas_mat 0).


Lemma Gate_X_matrix_unitary: mat_unitary Gate_X_matrix.
Proof.
  unfold mat_unitary, Gate_X_matrix. simpl.
  split; f_equal; f_equal; lca.
Qed.

Definition Gate_H_matrix: Matrix 1 :=
  (/ sqrt 2)%R .*
  rec_mat (bas_mat 1) (bas_mat 1)
          (bas_mat 1) (bas_mat (-1)%R).


Lemma Gate_H_matrix_Hermitian: mat_Hermitian Gate_H_matrix.
Proof.
  unfold mat_Hermitian, Gate_H_matrix. simpl.
  f_equal; f_equal; lca.
Qed.

Lemma Gate_H_matrix_unitary: mat_unitary Gate_H_matrix.
Proof.
  unfold mat_unitary.
  rewrite Gate_H_matrix_Hermitian.
  unfold Gate_H_matrix. simpl.
  split; f_equal; f_equal; com_simpl.
  all: apply com_proj_eq.
  all: simpl.
  all: try lra.
  all: ring_simplify; simpl.
  all: rewrite Rmult_1_r, <- Rinv_mult, sqrt_sqrt.
  all: lra.
Qed.

Definition phase_gate_matrix_multi (lambda : R) : Matrix 1 :=
  rec_mat (bas_mat Cone) (bas_mat Czero)
          (bas_mat Czero) (bas_mat (com_iexp lambda)).

Lemma phase_gate_matrix_unitary : forall lambda,
  mat_unitary (phase_gate_matrix_multi lambda).
Proof.
  intros. unfold mat_unitary, phase_gate_matrix_multi; simpl.
  split; f_equal; f_equal; com_simpl.
Qed.

Inductive QelibSingle := QH | QX | QS | QSdg | QT | QTdg.
Inductive QelibOp :=
| QSingle : QelibSingle -> nat -> QelibOp
| QCnot : nat -> nat -> QelibOp.

Definition qelib_single_matrix (g : QelibSingle) : Matrix 1 :=
  match g with
  | QH => Gate_H_matrix
  | QX => Gate_X_matrix
  | QS => phase_gate_matrix_multi PI2
  | QSdg => phase_gate_matrix_multi (- PI2)
  | QT => phase_gate_matrix_multi (PI / 4)
  | QTdg => phase_gate_matrix_multi (- PI / 4)
  end.

Definition qelib_op_matrix (n : nat) (op : QelibOp) : Matrix n :=
  match op with
  | QSingle g q => mat_single n q (qelib_single_matrix g)
  | QCnot c t => mat_cnot c t
  end.

Definition qelib_body_matrix (n : nat) (body : list QelibOp) : Matrix n :=
  fold_right (fun op acc => acc * qelib_op_matrix n op) mat_eye body.

Definition qelib_map_op (f : nat -> nat) (op : QelibOp) : QelibOp :=
  match op with
  | QSingle g q => QSingle g (f q)
  | QCnot c t => QCnot (f c) (f t)
  end.

Lemma qelib_body_matrix_unitary : forall n body,
  mat_unitary (qelib_body_matrix n body).
Proof.
  intros n body. induction body as [|op rest IH].
  - apply mat_eye_unitary.
  - cbn [qelib_body_matrix fold_right] in *.
    apply mat_mul_unitary; [exact IH |].
    destruct op as [g q | c t]; cbn [qelib_op_matrix].
    + apply mat_single_unitary. destruct g; cbn [qelib_single_matrix];
        auto using Gate_H_matrix_unitary, Gate_X_matrix_unitary,
          phase_gate_matrix_unitary.
    + apply mat_cnot_unitary.
Qed.

Lemma mat_swap_qelib_body_commute : forall n q1 q2 body,
  q1 < n -> q2 < n ->
  qelib_body_matrix n (map (qelib_map_op (swap_qbit q1 q2)) body) * mat_swap q1 q2 =
  mat_swap q1 q2 * qelib_body_matrix n body.
Proof.
  intros n q1 q2 body Hq1 Hq2.
  induction body as [|op rest IH].
  - cbn [map qelib_body_matrix fold_right]. mat_simpl.
  - cbn [map qelib_body_matrix fold_right].
    unfold qelib_body_matrix in IH.
    rewrite <- mat_mul_assoc.
    assert (Hop : qelib_op_matrix n (qelib_map_op (swap_qbit q1 q2) op) * mat_swap q1 q2 =
                  mat_swap q1 q2 * qelib_op_matrix n op).
    { destruct op; cbn [qelib_map_op qelib_op_matrix].
      - apply mat_swap_single_commute; assumption.
      - apply mat_swap_ctrl_commute; assumption. }
    rewrite Hop, mat_mul_assoc, IH, <- mat_mul_assoc. reflexivity.
Qed.

Definition qelib_body_cz (a b : nat) : list QelibOp :=
  [QSingle QH b; QCnot a b; QSingle QH b].

Definition mat_cz {n : nat} (a b : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_cz a b).

Lemma mat_cz_unitary : forall n a b, mat_unitary (@mat_cz n a b).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_cz_qelib_body : forall n a b,
  @mat_cz n a b = qelib_body_matrix n (qelib_body_cz a b).
Proof. reflexivity. Qed.

Lemma mat_swap_cz_commute : forall n q1 q2 a b,
  q1 < n -> q2 < n ->
  @mat_cz n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_cz a b.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_cz a b)); assumption. Qed.

Lemma mat_cz_extend_right : forall n extra a b,
  a < n -> b < n -> a <> b ->
  @mat_cz (n + extra) a b = @mat_cz n a b ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_cz, qelib_body_cz, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

Definition qelib_body_cy (a b : nat) : list QelibOp :=
  [QSingle QSdg b; QCnot a b; QSingle QS b].

Definition mat_cy {n : nat} (a b : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_cy a b).

Lemma mat_cy_unitary : forall n a b, mat_unitary (@mat_cy n a b).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_cy_qelib_body : forall n a b,
  @mat_cy n a b = qelib_body_matrix n (qelib_body_cy a b).
Proof. reflexivity. Qed.

Lemma mat_swap_cy_commute : forall n q1 q2 a b,
  q1 < n -> q2 < n ->
  @mat_cy n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_cy a b.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_cy a b)); assumption. Qed.

Lemma mat_cy_extend_right : forall n extra a b,
  a < n -> b < n -> a <> b ->
  @mat_cy (n + extra) a b = @mat_cy n a b ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_cy, qelib_body_cy, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

Definition qelib_body_ch (a b : nat) : list QelibOp :=
  [QSingle QH b; QSingle QSdg b; QCnot a b; QSingle QH b; QSingle QT b; QCnot a b; QSingle QT b; QSingle QH b; QSingle QS b; QSingle QX b; QSingle QS a].

Definition mat_ch {n : nat} (a b : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_ch a b).

Lemma mat_ch_unitary : forall n a b, mat_unitary (@mat_ch n a b).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_ch_qelib_body : forall n a b,
  @mat_ch n a b = qelib_body_matrix n (qelib_body_ch a b).
Proof. reflexivity. Qed.

Lemma mat_swap_ch_commute : forall n q1 q2 a b,
  q1 < n -> q2 < n ->
  @mat_ch n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_ch a b.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_ch a b)); assumption. Qed.

Lemma mat_ch_extend_right : forall n extra a b,
  a < n -> b < n -> a <> b ->
  @mat_ch (n + extra) a b = @mat_ch n a b ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_ch, qelib_body_ch, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

Definition qelib_body_csx (a b : nat) : list QelibOp :=
  [QSingle QH b; QSingle QT a; QCnot a b; QSingle QTdg b; QCnot a b; QSingle QT b; QSingle QH b].

Definition mat_csx {n : nat} (a b : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_csx a b).

Lemma mat_csx_unitary : forall n a b, mat_unitary (@mat_csx n a b).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_csx_qelib_body : forall n a b,
  @mat_csx n a b = qelib_body_matrix n (qelib_body_csx a b).
Proof. reflexivity. Qed.

Lemma mat_swap_csx_commute : forall n q1 q2 a b,
  q1 < n -> q2 < n ->
  @mat_csx n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_csx a b.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_csx a b)); assumption. Qed.

Lemma mat_csx_extend_right : forall n extra a b,
  a < n -> b < n -> a <> b ->
  @mat_csx (n + extra) a b = @mat_csx n a b ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_csx, qelib_body_csx, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

Definition qelib_body_ccx (a b c : nat) : list QelibOp :=
  [QSingle QH c; QCnot b c; QSingle QTdg c; QCnot a c; QSingle QT c; QCnot b c; QSingle QTdg c; QCnot a c; QSingle QT b; QSingle QT c; QSingle QH c; QCnot a b; QSingle QT a; QSingle QTdg b; QCnot a b].

Definition mat_ccx {n : nat} (a b c : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_ccx a b c).

Lemma mat_ccx_unitary : forall n a b c, mat_unitary (@mat_ccx n a b c).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_ccx_qelib_body : forall n a b c,
  @mat_ccx n a b c = qelib_body_matrix n (qelib_body_ccx a b c).
Proof. reflexivity. Qed.

Lemma mat_swap_ccx_commute : forall n q1 q2 a b c,
  q1 < n -> q2 < n ->
  @mat_ccx n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) (swap_qbit q1 q2 c) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_ccx a b c.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_ccx a b c)); assumption. Qed.

Lemma mat_ccx_extend_right : forall n extra a b c,
  a < n -> b < n -> c < n -> a <> b -> a <> c -> b <> c ->
  @mat_ccx (n + extra) a b c = @mat_ccx n a b c ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_ccx, qelib_body_ccx, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

Definition qelib_body_cswap (a b c : nat) : list QelibOp :=
  [QCnot c b; QSingle QH c; QCnot b c; QSingle QTdg c; QCnot a c; QSingle QT c; QCnot b c; QSingle QTdg c; QCnot a c; QSingle QT b; QSingle QT c; QSingle QH c; QCnot a b; QSingle QT a; QSingle QTdg b; QCnot a b; QCnot c b].

Definition mat_cswap {n : nat} (a b c : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_cswap a b c).

Lemma mat_cswap_unitary : forall n a b c, mat_unitary (@mat_cswap n a b c).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_cswap_qelib_body : forall n a b c,
  @mat_cswap n a b c = qelib_body_matrix n (qelib_body_cswap a b c).
Proof. reflexivity. Qed.

Lemma mat_swap_cswap_commute : forall n q1 q2 a b c,
  q1 < n -> q2 < n ->
  @mat_cswap n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) (swap_qbit q1 q2 c) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_cswap a b c.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_cswap a b c)); assumption. Qed.

Lemma mat_cswap_extend_right : forall n extra a b c,
  a < n -> b < n -> c < n -> a <> b -> a <> c -> b <> c ->
  @mat_cswap (n + extra) a b c = @mat_cswap n a b c ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_cswap, qelib_body_cswap, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

Definition qelib_body_rccx (a b c : nat) : list QelibOp :=
  [QSingle QH c; QSingle QT c; QCnot b c; QSingle QTdg c; QCnot a c; QSingle QT c; QCnot b c; QSingle QTdg c; QSingle QH c].

Definition mat_rccx {n : nat} (a b c : nat) : Matrix n :=
  qelib_body_matrix n (qelib_body_rccx a b c).

Lemma mat_rccx_unitary : forall n a b c, mat_unitary (@mat_rccx n a b c).
Proof. intros. apply qelib_body_matrix_unitary. Qed.

Lemma mat_rccx_qelib_body : forall n a b c,
  @mat_rccx n a b c = qelib_body_matrix n (qelib_body_rccx a b c).
Proof. reflexivity. Qed.

Lemma mat_swap_rccx_commute : forall n q1 q2 a b c,
  q1 < n -> q2 < n ->
  @mat_rccx n (swap_qbit q1 q2 a) (swap_qbit q1 q2 b) (swap_qbit q1 q2 c) * mat_swap q1 q2 =
  mat_swap q1 q2 * mat_rccx a b c.
Proof. intros. apply (mat_swap_qelib_body_commute n q1 q2 (qelib_body_rccx a b c)); assumption. Qed.

Lemma mat_rccx_extend_right : forall n extra a b c,
  a < n -> b < n -> c < n -> a <> b -> a <> c -> b <> c ->
  @mat_rccx (n + extra) a b c = @mat_rccx n a b c ⊗ @mat_eye extra.
Proof.
  intros. unfold mat_rccx, qelib_body_rccx, qelib_body_matrix.
  cbn [fold_right qelib_op_matrix].
  repeat rewrite mat_single_break_left by lia.
  repeat rewrite mat_cnot_extend_right by lia.
  rewrite <- (@tprod_eye_eye n extra) at 1.
  repeat rewrite tprod_mul. repeat rewrite mat_mul_eye_l. reflexivity.
Qed.

