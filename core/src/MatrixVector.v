Require Export Vector.
Require Export RingUtil.

Open Scope Matrix_scope.

Definition mat_trace_1 {n} (A : Matrix n) : Prop := mat_trace A = 1.

(* Vector Matrix multiplication is distributive *)
Lemma vec_mat_mul_dist_l: forall {n} (v: Vector n) (A B: Matrix n),
  v |* (A + B) = (v |* A) |+| (v |* B).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    f_equal.
    all: apply ring_util_1.
Qed.

Lemma vec_mat_mul_dist_r: forall {n} (v w: Vector n) (A: Matrix n),
  (v |+| w) |* A = (v |* A) |+| (w |* A).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (vec_0_inv w) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    f_equal.
    all: apply ring_util_3.
Qed.

Lemma mat_vec_mul_dist_l: forall {n} (A: Matrix n) (v w: Vector n),
  A *| (v |+| w) = (A *| v) |+| (A *| w).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (vec_0_inv w) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    f_equal.
    all: apply ring_util_4.
Qed.

Lemma mat_vec_mul_dist_r: forall {n} (A B: Matrix n) (v: Vector n),
  (A + B) *| v = (A *| v) |+| (B *| v).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    f_equal.
    all: apply ring_util_2.
Qed.

Ltac mat_expand := repeat (
  rewrite mat_mul_dist_l ||
  rewrite mat_mul_dist_r ||
  rewrite mat_scale_dist_l ||
  rewrite mat_scale_dist_r ||
  rewrite mat_add_trace ||
  rewrite vec_scale_dist_l ||
  rewrite vec_scale_dist_r ||
  rewrite vec_dot_dist_l ||
  rewrite vec_dot_dist_r ||
  rewrite vec_mat_mul_dist_l ||
  rewrite vec_mat_mul_dist_r ||
  rewrite mat_vec_mul_dist_l ||
  rewrite mat_vec_mul_dist_r ||
  auto
).

Ltac mat_expand_in_all := repeat (
  rewrite mat_mul_dist_l in * ||
  rewrite mat_mul_dist_r in * ||
  rewrite mat_scale_dist_l in * ||
  rewrite mat_scale_dist_r in * ||
  rewrite mat_add_trace in * ||
  rewrite vec_scale_dist_l in * ||
  rewrite vec_scale_dist_r in * ||
  rewrite vec_dot_dist_l in * ||
  rewrite vec_dot_dist_r in * ||
  rewrite vec_mat_mul_dist_l in * ||
  rewrite vec_mat_mul_dist_r in * ||
  rewrite mat_vec_mul_dist_l in * ||
  rewrite mat_vec_mul_dist_r in * ||
  auto
).

(* Matrix Vector multiplication is associative *)

Lemma mat_mat_vec_mul_assoc: forall {n} (A B: Matrix n) (v: Vector n),
  (A * B) *| v = A *| (B *| v).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 ?]]]]; subst.
    simpl.
    mat_expand.
    repeat rewrite IHn.
    f_equal.
    all: apply ring_util_6.
Qed.

Hint Extern 1 => (rewrite mat_mat_vec_mul_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- mat_mat_vec_mul_assoc) : assoc_db.

Lemma vec_mat_mat_mul_assoc: forall {n} (v: Vector n) (A B: Matrix n),
  v |* (A * B) = (v |* A) |* B.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    specialize (mat_0_inv B) as [b]; subst.
    simpl.
    f_equal.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    specialize (mat_S_inv B) as [B1 [B2 [B3 [B4 ?]]]]; subst.
    simpl.
    mat_expand.
    repeat rewrite IHn.
    f_equal.
    all: apply ring_util_5.
Qed.

Hint Extern 1 => (rewrite vec_mat_mat_mul_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- vec_mat_mat_mul_assoc) : assoc_db.

Lemma vec_mat_vec_mul_assoc: forall {n} (v w: Vector n) (A: Matrix n),
  (v |* A) |*| w = v |*| (A *| w).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (vec_0_inv w) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    mat_expand.
    repeat rewrite IHn.
    lca.
Qed.

Hint Extern 1 => (rewrite vec_mat_vec_mul_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- vec_mat_vec_mul_assoc) : assoc_db.

Lemma vec_vec_vec_mul_assoc: forall {n} (v w u: Vector n),
  v |* (w |✕| u) = (v |*| w) .*| u.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (vec_0_inv w) as [d]; subst.
    specialize (vec_0_inv u) as [e]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (vec_S_inv w) as [w1 [w2 ?]]; subst.
    specialize (vec_S_inv u) as [u1 [u2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite vec_scale_dist_r.
    reflexivity.
Qed.

Hint Extern 1 => (rewrite vec_vec_vec_mul_assoc) : assoc_db.
Hint Extern 1 => (rewrite <- vec_vec_vec_mul_assoc) : assoc_db.

Lemma mat_vec_mul_scale_comm_l: forall {n} (A: Matrix n) (v: Vector n) (c: Complex),
  (c .* A) *| v = c .*| (A *| v).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite vec_scale_dist_l.
    reflexivity.
Qed.

Lemma mat_vec_mul_scale_comm_r: forall {n} (A: Matrix n) (v: Vector n) (c: Complex),
  A *| (c .*| v) = c .*| (A *| v).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite vec_scale_dist_l.
    reflexivity.
Qed.

Lemma vec_mat_mul_scale_comm_l: forall {n} (v: Vector n) (A: Matrix n) (c: Complex),
  (c .*| v) |* A = c .*| (v |* A).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite vec_scale_dist_l.
    reflexivity.
Qed.

Lemma vec_mat_mul_scale_comm_r: forall {n} (v: Vector n) (A: Matrix n) (c: Complex),
  v |* (c .* A) = c .*| (v |* A).
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [d]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl.
    f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite vec_scale_dist_l.
    reflexivity.
Qed.

(* Multiplying zero vector to matrices *)
Lemma vec_mat_mul_0_l: forall {n} (A: Matrix n), vec_zero |* A = vec_zero.
Proof.
  intros.
  induction A.
  - simpl in *.
    f_equal; lca.
  - simpl.
    rewrite IHA1; rewrite IHA2; rewrite IHA3; rewrite IHA4.
    repeat rewrite vec_add_0_l.
    reflexivity.
Qed.

Lemma vec_mat_mul_0_r: forall {n} (v: Vector n), v |* mat_0 = vec_zero.
Proof.
  induction v.
  - simpl in *.
    f_equal; lca.
  - simpl.
    rewrite IHv1; rewrite IHv2.
    repeat rewrite vec_add_0_l.
    reflexivity.
Qed.

Lemma mat_vec_mul_0_l: forall {n} (v: Vector n), mat_0 *| v = vec_zero.
Proof.
  induction v.
  - simpl in *.
    f_equal; lca.
  - simpl.
    rewrite IHv1; rewrite IHv2.
    repeat rewrite vec_add_0_l.
    reflexivity.
Qed.

Lemma mat_vec_mul_0_r: forall {n} (A: Matrix n), A *| vec_zero = vec_zero.
Proof.
  induction A.
  - simpl in *.
    f_equal; lca.
  - simpl.
    rewrite IHA1; rewrite IHA2; rewrite IHA3; rewrite IHA4.
    repeat rewrite vec_add_0_l.
    reflexivity.
Qed.

Lemma mat_vec_mul_conjtrans: forall {n} (A: Matrix n) (v: Vector n),
  (A *| v)|† = v|† |* A†.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite vec_add_conjtrans.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma vec_mat_mul_conjtrans: forall {n} (v: Vector n) (A: Matrix n),
  (v |* A)|† = A† *| v|†.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    specialize (mat_0_inv A) as [a]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    specialize (mat_S_inv A) as [A1 [A2 [A3 [A4 ?]]]]; subst.
    simpl.
    repeat rewrite vec_add_conjtrans.
    repeat rewrite IHn.
    reflexivity.
Qed.

Lemma eye_vec_mul: forall {n} (v: Vector n), @mat_eye n *| v = v.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite mat_vec_mul_0_l.
    repeat (rewrite vec_add_0_l || rewrite vec_add_0_r).
    reflexivity.
Qed.

Lemma vec_eye_mul: forall {n} (v: Vector n), v |* @mat_eye n = v.
Proof.
  intros.
  induction n.
  - specialize (vec_0_inv v) as [c]; subst.
    simpl; f_equal; lca.
  - specialize (vec_S_inv v) as [v1 [v2 ?]]; subst.
    simpl.
    repeat rewrite IHn.
    repeat rewrite vec_mat_mul_0_r.
    repeat (rewrite vec_add_0_l || rewrite vec_add_0_r).
    reflexivity.
Qed.

Ltac mat_simpl := repeat (
  rewrite mat_add_0_l ||
  rewrite mat_add_0_r ||
  rewrite mat_add_inv ||
  rewrite mat_mul_0_l ||
  rewrite mat_mul_0_r ||
  rewrite mat_mul_eye_l ||
  rewrite mat_mul_eye_r ||
  rewrite mat_scale_0 ||
  rewrite mat_scale_1 ||
  rewrite mat_conjtrans_involutive ||
  rewrite vec_add_0_l ||
  rewrite vec_add_0_r ||
  rewrite vec_add_inv ||
  rewrite vec_dot_0_l ||
  rewrite vec_dot_0_r ||
  rewrite vec_conjtrans_involutive ||
  rewrite vec_conjtrans_0 ||
  rewrite vec_mat_mul_0_l ||
  rewrite vec_mat_mul_0_r ||
  rewrite mat_vec_mul_0_l ||
  rewrite mat_vec_mul_0_r ||
  rewrite com_add_0_l ||
  rewrite com_add_0_r ||
  rewrite com_mul_0_l ||
  rewrite com_mul_0_r ||
  rewrite com_conj_involutive ||
  rewrite eye_vec_mul ||
  rewrite vec_eye_mul ||
  auto
).

Ltac mat_simpl_in_all := repeat (
  rewrite mat_add_0_l in * ||
  rewrite mat_add_0_r in * ||
  rewrite mat_add_inv in * ||
  rewrite mat_mul_0_l in * ||
  rewrite mat_mul_0_r in * ||
  rewrite mat_mul_eye_l in * ||
  rewrite mat_mul_eye_r in * ||
  rewrite mat_scale_0 in * ||
  rewrite mat_scale_1 in * ||
  rewrite mat_conjtrans_involutive in * ||
  rewrite vec_add_0_l in * ||
  rewrite vec_add_0_r in * ||
  rewrite vec_add_inv in * ||
  rewrite vec_dot_0_l in * ||
  rewrite vec_dot_0_r in * ||
  rewrite vec_conjtrans_involutive in * ||
  rewrite vec_conjtrans_0 in * ||
  rewrite vec_mat_mul_0_l in * ||
  rewrite vec_mat_mul_0_r in * ||
  rewrite mat_vec_mul_0_l in * ||
  rewrite mat_vec_mul_0_r in * ||
  rewrite com_add_0_l in * ||
  rewrite com_add_0_r in * ||
  rewrite com_mul_0_l in * ||
  rewrite com_mul_0_r in * ||
  rewrite com_conj_involutive in * ||
  rewrite eye_vec_mul in * ||
  rewrite vec_eye_mul in * ||
  auto
).

Ltac mat_sort := repeat (
  rewrite mat_add_assoc ||
  rewrite mat_mul_assoc ||
  rewrite <- mat_scale_cmul_assoc ||
  rewrite <- mat_scale_mul_assoc ||
  rewrite <- mat_mat_vec_mul_assoc ||
  rewrite vec_mat_mat_mul_assoc ||
  rewrite <- vec_mat_vec_mul_assoc ||
  rewrite vec_vec_vec_mul_assoc ||
  rewrite vec_vec_scale_dot_assoc ||
  rewrite <- mat_scale_mul_comm ||
  rewrite mat_vec_mul_scale_comm_l ||
  rewrite mat_vec_mul_scale_comm_r ||
  rewrite vec_mat_mul_scale_comm_l ||
  rewrite vec_mat_mul_scale_comm_r ||
  f_equal ||
  auto
).

Ltac mat_sort_in_all := repeat (
  rewrite mat_add_assoc in * ||
  rewrite mat_mul_assoc in * ||
  rewrite <- mat_scale_cmul_assoc in * ||
  rewrite <- mat_scale_mul_assoc in * ||
  rewrite <- mat_mat_vec_mul_assoc in * ||
  rewrite vec_mat_mat_mul_assoc in * ||
  rewrite <- vec_mat_vec_mul_assoc in * ||
  rewrite vec_vec_vec_mul_assoc in * ||
  rewrite vec_vec_scale_dot_assoc in * ||
  rewrite <- mat_scale_mul_comm in * ||
  rewrite mat_vec_mul_scale_comm_l in * ||
  rewrite mat_vec_mul_scale_comm_r in * ||
  rewrite vec_mat_mul_scale_comm_l in * ||
  rewrite vec_mat_mul_scale_comm_r in * ||
  f_equal ||
  auto
).

Ltac mat_sort_rev := repeat (
  rewrite <- mat_add_assoc ||
  rewrite <- mat_mul_assoc ||
  rewrite mat_scale_cmul_assoc ||
  rewrite mat_scale_mul_assoc ||
  rewrite mat_mat_vec_mul_assoc ||
  rewrite <- vec_mat_mat_mul_assoc ||
  rewrite vec_mat_vec_mul_assoc ||
  rewrite <- vec_vec_vec_mul_assoc ||
  rewrite <- vec_vec_scale_dot_assoc ||
  rewrite mat_scale_mul_comm ||
  rewrite <- mat_vec_mul_scale_comm_l ||
  rewrite <- mat_vec_mul_scale_comm_r ||
  rewrite <- vec_mat_mul_scale_comm_l ||
  rewrite <- vec_mat_mul_scale_comm_r ||
  f_equal ||
  auto
).

Ltac mat_sort_rev_in_all := repeat (
  rewrite <- mat_add_assoc in * ||
  rewrite <- mat_mul_assoc in * ||
  rewrite mat_scale_cmul_assoc in * ||
  rewrite mat_scale_mul_assoc in * ||
  rewrite mat_mat_vec_mul_assoc in * ||
  rewrite <- vec_mat_mat_mul_assoc in * ||
  rewrite vec_mat_vec_mul_assoc in * ||
  rewrite <- vec_vec_vec_mul_assoc in * ||
  rewrite vec_vec_scale_dot_assoc in * ||
  rewrite mat_scale_mul_comm in * ||
  rewrite <- mat_vec_mul_scale_comm_l in * ||
  rewrite <- mat_vec_mul_scale_comm_r in * ||
  rewrite <- vec_mat_mul_scale_comm_l in * ||
  rewrite <- vec_mat_mul_scale_comm_r in * ||
  f_equal ||
  auto
).
