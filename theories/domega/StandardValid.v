Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.All.

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import QArith.
From Stdlib Require Import Qreals.
From Stdlib Require Import String.

Import ListNotations.

Open Scope Q_scope.
Open Scope string_scope.

Section STANDARD_GATE_SYNTAX.

Inductive StandardGate : Type :=
| Std_I
| Std_X
| Std_Y
| Std_Z
| Std_H
| Std_S
| Std_Sdg
| Std_T
| Std_Tdg
| Std_SX
| Std_SXdg.

Definition standard_gate_name (gate : StandardGate) : string :=
  match gate with
  | Std_I => "id"
  | Std_X => "x"
  | Std_Y => "y"
  | Std_Z => "z"
  | Std_H => "h"
  | Std_S => "s"
  | Std_Sdg => "sdg"
  | Std_T => "t"
  | Std_Tdg => "tdg"
  | Std_SX => "sx"
  | Std_SXdg => "sxdg"
  end.

Definition standard_gate_instr (gate : StandardGate) (qbit : nat)
    : Instruction :=
  match gate with
  | Std_I => Gate_I qbit
  | Std_X => Gate_X qbit
  | Std_Y => Gate_Y qbit
  | Std_Z => Gate_Z qbit
  | Std_H => Gate_H qbit
  | Std_S => Gate_S qbit
  | Std_Sdg => Gate_Sdg qbit
  | Std_T => Gate_T qbit
  | Std_Tdg => Gate_Tdg qbit
  | Std_SX => Gate_SX qbit
  | Std_SXdg => Gate_SXdg qbit
  end.

End STANDARD_GATE_SYNTAX.

Section DOMEGA_ARITHMETIC.

Record DOmega : Type := {
  domega_c0 : Q;
  domega_c1 : Q;
  domega_c2 : Q;
  domega_c3 : Q
}.

Definition domega_make c0 c1 c2 c3 : DOmega :=
  {| domega_c0 := c0; domega_c1 := c1; domega_c2 := c2; domega_c3 := c3 |}.

Definition domega_zero : DOmega := domega_make 0 0 0 0.
Definition domega_one : DOmega := domega_make 1 0 0 0.
Definition domega_w : DOmega := domega_make 0 1 0 0.
Definition domega_w2 : DOmega := domega_make 0 0 1 0.
Definition domega_w3 : DOmega := domega_make 0 0 0 1.

Definition domega_add (x y : DOmega) : DOmega :=
  domega_make
    (domega_c0 x + domega_c0 y)
    (domega_c1 x + domega_c1 y)
    (domega_c2 x + domega_c2 y)
    (domega_c3 x + domega_c3 y).

Definition domega_neg (x : DOmega) : DOmega :=
  domega_make
    (- domega_c0 x)
    (- domega_c1 x)
    (- domega_c2 x)
    (- domega_c3 x).

Definition domega_sub (x y : DOmega) : DOmega :=
  domega_add x (domega_neg y).

Definition domega_scale (q : Q) (x : DOmega) : DOmega :=
  domega_make
    (q * domega_c0 x)
    (q * domega_c1 x)
    (q * domega_c2 x)
    (q * domega_c3 x).

Definition domega_mul (x y : DOmega) : DOmega :=
  let a0 := domega_c0 x in
  let a1 := domega_c1 x in
  let a2 := domega_c2 x in
  let a3 := domega_c3 x in
  let b0 := domega_c0 y in
  let b1 := domega_c1 y in
  let b2 := domega_c2 y in
  let b3 := domega_c3 y in
  let p0 := a0 * b0 in
  let p1 := a0 * b1 + a1 * b0 in
  let p2 := a0 * b2 + a1 * b1 + a2 * b0 in
  let p3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
  let p4 := a1 * b3 + a2 * b2 + a3 * b1 in
  let p5 := a2 * b3 + a3 * b2 in
  let p6 := a3 * b3 in
  domega_make (p0 - p4) (p1 - p5) (p2 - p6) p3.

Definition complex_of_Q (q : Q) : Complex :=
  RTC (Q2R q).

Definition omega : Complex :=
  com_iexp (PI / 4)%R.

Definition complex_of_domega (x : DOmega) : Complex :=
  (complex_of_Q (domega_c0 x)
   + complex_of_Q (domega_c1 x) * omega
   + complex_of_Q (domega_c2 x) * (omega * omega)
   + complex_of_Q (domega_c3 x)
     * (omega * omega * omega))%com.

Definition domega_eqb (x y : DOmega) : bool :=
  Qeq_bool (domega_c0 x) (domega_c0 y)
  && Qeq_bool (domega_c1 x) (domega_c1 y)
  && Qeq_bool (domega_c2 x) (domega_c2 y)
  && Qeq_bool (domega_c3 x) (domega_c3 y).

Definition domega_equiv (x y : DOmega) : Prop :=
  complex_of_domega x = complex_of_domega y.

Lemma complex_of_Q_eq :
  forall x y,
    x == y ->
    complex_of_Q x = complex_of_Q y.
Proof.
  intros x y H.
  unfold complex_of_Q.
  rewrite (Qeq_eqR x y H).
  reflexivity.
Qed.

Lemma domega_eqb_sound :
  forall x y,
    domega_eqb x y = true ->
    domega_equiv x y.
Proof.
  intros x y H.
  unfold domega_eqb in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[H0 H1] H2] H3].
  unfold domega_equiv, complex_of_domega.
  apply Qeq_bool_eq in H0, H1, H2, H3.
  rewrite (complex_of_Q_eq _ _ H0).
  rewrite (complex_of_Q_eq _ _ H1).
  rewrite (complex_of_Q_eq _ _ H2).
  rewrite (complex_of_Q_eq _ _ H3).
  reflexivity.
Qed.

Lemma complex_of_domega_add :
  forall x y,
    complex_of_domega (domega_add x y) =
    (complex_of_domega x + complex_of_domega y)%com.
Proof.
  intros [a0 a1 a2 a3] [b0 b1 b2 b3].
  unfold complex_of_domega, domega_add, domega_make, complex_of_Q.
  simpl.
  repeat rewrite Q2R_plus.
  apply com_proj_eq; simpl; lra.
Qed.

Lemma omega_sq :
  (omega * omega)%com = Ione.
Proof.
  unfold omega.
  rewrite <- com_iexp_mul.
  replace (PI / 4 + PI / 4)%R with (PI / 2)%R by field.
  apply com_iexp_PI2.
Qed.

Lemma complex_of_domega_neg :
  forall x,
    complex_of_domega (domega_neg x) = (- complex_of_domega x)%com.
Proof.
  intros [a0 a1 a2 a3].
  unfold complex_of_domega, domega_neg, domega_make, complex_of_Q.
  simpl.
  repeat rewrite Q2R_opp.
  apply com_proj_eq; simpl; lra.
Qed.

Lemma complex_of_domega_mul :
  forall x y,
    complex_of_domega (domega_mul x y) =
    (complex_of_domega x * complex_of_domega y)%com.
Proof.
  intros [a0 a1 a2 a3] [b0 b1 b2 b3].
  unfold complex_of_domega, domega_mul, domega_make, complex_of_Q.
  simpl.
  repeat (rewrite Q2R_plus || rewrite Q2R_minus || rewrite Q2R_mult).
  repeat rewrite omega_sq.
  repeat rewrite com_Ione_sq'.
  repeat rewrite com_Ione_sq.
  apply com_proj_eq; simpl.
  all: rewrite cos_PI4, sin_PI4.
  all: field_simplify_eq; try solve [apply sqrt2_neq_0].
  all: replace (sqrt 2 ^ 2)%R with 2%R by
    (simpl; rewrite Rmult_1_r; rewrite sqrt_sqrt; lra).
  all: nra.
Qed.

Definition domega_pow8 (n : nat) : DOmega :=
  match n with
  | O => domega_one
  | S O => domega_w
  | S (S O) => domega_w2
  | S (S (S O)) => domega_w3
  | S (S (S (S O))) => domega_neg domega_one
  | S (S (S (S (S O)))) => domega_neg domega_w
  | S (S (S (S (S (S O))))) => domega_neg domega_w2
  | _ => domega_neg domega_w3
  end.

Definition domega_phase_list : list DOmega :=
  [ domega_pow8 0; domega_pow8 1; domega_pow8 2; domega_pow8 3;
    domega_pow8 4; domega_pow8 5; domega_pow8 6; domega_pow8 7 ].

End DOMEGA_ARITHMETIC.

Section DOMEGA_MATRIX.

Record DOmegaMatrix : Type := {
  domega_matrix_00 : DOmega;
  domega_matrix_01 : DOmega;
  domega_matrix_10 : DOmega;
  domega_matrix_11 : DOmega
}.

Definition domega_matrix_make a b c d : DOmegaMatrix :=
  {| domega_matrix_00 := a; domega_matrix_01 := b; domega_matrix_10 := c; domega_matrix_11 := d |}.

Definition domega_matrix_zero : DOmegaMatrix :=
  domega_matrix_make domega_zero domega_zero domega_zero domega_zero.

Definition domega_matrix_eye : DOmegaMatrix :=
  domega_matrix_make domega_one domega_zero domega_zero domega_one.

Definition domega_matrix_add (x y : DOmegaMatrix) : DOmegaMatrix :=
  domega_matrix_make
    (domega_add (domega_matrix_00 x) (domega_matrix_00 y))
    (domega_add (domega_matrix_01 x) (domega_matrix_01 y))
    (domega_add (domega_matrix_10 x) (domega_matrix_10 y))
    (domega_add (domega_matrix_11 x) (domega_matrix_11 y)).

Definition domega_matrix_scale (scalar : DOmega) (x : DOmegaMatrix) : DOmegaMatrix :=
  domega_matrix_make
    (domega_mul scalar (domega_matrix_00 x))
    (domega_mul scalar (domega_matrix_01 x))
    (domega_mul scalar (domega_matrix_10 x))
    (domega_mul scalar (domega_matrix_11 x)).

Definition domega_matrix_mul (x y : DOmegaMatrix) : DOmegaMatrix :=
  domega_matrix_make
    (domega_add
       (domega_mul (domega_matrix_00 x) (domega_matrix_00 y))
       (domega_mul (domega_matrix_01 x) (domega_matrix_10 y)))
    (domega_add
       (domega_mul (domega_matrix_00 x) (domega_matrix_01 y))
       (domega_mul (domega_matrix_01 x) (domega_matrix_11 y)))
    (domega_add
       (domega_mul (domega_matrix_10 x) (domega_matrix_00 y))
       (domega_mul (domega_matrix_11 x) (domega_matrix_10 y)))
    (domega_add
       (domega_mul (domega_matrix_10 x) (domega_matrix_01 y))
       (domega_mul (domega_matrix_11 x) (domega_matrix_11 y))).

Definition domega_matrix_eqb (x y : DOmegaMatrix) : bool :=
  domega_eqb (domega_matrix_00 x) (domega_matrix_00 y)
  && domega_eqb (domega_matrix_01 x) (domega_matrix_01 y)
  && domega_eqb (domega_matrix_10 x) (domega_matrix_10 y)
  && domega_eqb (domega_matrix_11 x) (domega_matrix_11 y).

Definition domega_matrix_equiv (x y : DOmegaMatrix) : Prop :=
  domega_equiv (domega_matrix_00 x) (domega_matrix_00 y)
  /\ domega_equiv (domega_matrix_01 x) (domega_matrix_01 y)
  /\ domega_equiv (domega_matrix_10 x) (domega_matrix_10 y)
  /\ domega_equiv (domega_matrix_11 x) (domega_matrix_11 y).

Lemma domega_matrix_eqb_sound :
  forall x y,
    domega_matrix_eqb x y = true ->
    domega_matrix_equiv x y.
Proof.
  intros x y H.
  unfold domega_matrix_eqb in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[H00 H01] H10] H11].
  unfold domega_matrix_equiv.
  repeat split; apply domega_eqb_sound; assumption.
Qed.

Definition domega_matrix_eq_up_to_phaseb (x y : DOmegaMatrix) : bool :=
  existsb (fun phase => domega_matrix_eqb x (domega_matrix_scale phase y)) domega_phase_list.

Lemma domega_matrix_eq_up_to_phaseb_sound :
  forall x y,
    domega_matrix_eq_up_to_phaseb x y = true ->
    exists phase,
      In phase domega_phase_list /\ domega_matrix_equiv x (domega_matrix_scale phase y).
Proof.
  intros x y H.
  unfold domega_matrix_eq_up_to_phaseb in H.
  apply existsb_exists in H as [phase [Hin Heq]].
  exists phase.
  split.
  - assumption.
  - apply domega_matrix_eqb_sound.
    assumption.
Qed.

Definition domega_matrix_to_matrix (x : DOmegaMatrix) : Matrix 1%nat :=
  rec_mat
    (bas_mat (complex_of_domega (domega_matrix_00 x)))
    (bas_mat (complex_of_domega (domega_matrix_01 x)))
    (bas_mat (complex_of_domega (domega_matrix_10 x)))
    (bas_mat (complex_of_domega (domega_matrix_11 x))).

Lemma domega_matrix_eye_to_matrix :
  domega_matrix_to_matrix domega_matrix_eye = mat_eye.
Proof.
  unfold domega_matrix_to_matrix, domega_matrix_eye, domega_matrix_make,
    complex_of_domega, domega_one, domega_zero, domega_make, complex_of_Q,
    Q2R.
  simpl.
  repeat (f_equal; try lca).
Qed.

Lemma domega_matrix_equiv_to_matrix :
  forall x y,
    domega_matrix_equiv x y ->
    domega_matrix_to_matrix x = domega_matrix_to_matrix y.
Proof.
  intros x y [H00 [H01 [H10 H11]]].
  unfold domega_matrix_to_matrix.
  unfold domega_equiv in *.
  destruct x as [x00 x01 x10 x11].
  destruct y as [y00 y01 y10 y11].
  simpl in *.
  rewrite H00, H01, H10, H11.
  reflexivity.
Qed.

Lemma domega_matrix_scale_to_matrix :
  forall scalar x,
    domega_matrix_to_matrix (domega_matrix_scale scalar x) =
    complex_of_domega scalar .* domega_matrix_to_matrix x.
Proof.
  intros scalar [a b c d].
  unfold domega_matrix_to_matrix, domega_matrix_scale, domega_matrix_make.
  simpl.
  repeat rewrite complex_of_domega_mul.
  reflexivity.
Qed.

Lemma domega_matrix_mul_to_matrix :
  forall x y,
    domega_matrix_to_matrix (domega_matrix_mul x y) =
    mat_mul (domega_matrix_to_matrix x) (domega_matrix_to_matrix y).
Proof.
  intros [a b c d] [e f g h].
  unfold domega_matrix_to_matrix, domega_matrix_mul, domega_matrix_make.
  simpl.
  repeat rewrite complex_of_domega_add.
  repeat rewrite complex_of_domega_mul.
  reflexivity.
Qed.

End DOMEGA_MATRIX.

Section STANDARD_GATE_MATRICES.

Definition qhalf : Q := 1 # 2.
Definition domega_half : DOmega := domega_make qhalf 0 0 0.

Definition domega_minus_i : DOmega := domega_neg domega_w2.
Definition domega_h_scalar : DOmega := domega_make 0 qhalf 0 (- qhalf).

Definition domega_matrix_x : DOmegaMatrix :=
  domega_matrix_make domega_zero domega_one domega_one domega_zero.

Definition domega_matrix_y : DOmegaMatrix :=
  domega_matrix_make domega_zero domega_minus_i domega_w2 domega_zero.

Definition domega_matrix_z : DOmegaMatrix :=
  domega_matrix_make domega_one domega_zero domega_zero (domega_neg domega_one).

Definition domega_matrix_h : DOmegaMatrix :=
  domega_matrix_make
    domega_h_scalar domega_h_scalar domega_h_scalar
    (domega_neg domega_h_scalar).

Definition domega_matrix_s : DOmegaMatrix :=
  domega_matrix_make domega_one domega_zero domega_zero domega_w2.

Definition domega_matrix_sdg : DOmegaMatrix :=
  domega_matrix_make domega_one domega_zero domega_zero (domega_neg domega_w2).

Definition domega_matrix_t : DOmegaMatrix :=
  domega_matrix_make domega_one domega_zero domega_zero domega_w.

Definition domega_matrix_tdg : DOmegaMatrix :=
  domega_matrix_make domega_one domega_zero domega_zero (domega_neg domega_w3).

Definition domega_one_plus_i : DOmega := domega_add domega_one domega_w2.
Definition domega_one_minus_i : DOmega := domega_sub domega_one domega_w2.
Definition domega_half_one_plus_i : DOmega :=
  domega_scale qhalf domega_one_plus_i.
Definition domega_half_one_minus_i : DOmega :=
  domega_scale qhalf domega_one_minus_i.

Definition domega_matrix_sx : DOmegaMatrix :=
  domega_matrix_make
    domega_half_one_plus_i domega_half_one_minus_i
    domega_half_one_minus_i domega_half_one_plus_i.

Definition domega_matrix_sxdg : DOmegaMatrix :=
  domega_matrix_make
    domega_half_one_minus_i domega_half_one_plus_i
    domega_half_one_plus_i domega_half_one_minus_i.

Definition standard_gate_domega_matrix (gate : StandardGate) : DOmegaMatrix :=
  match gate with
  | Std_I => domega_matrix_eye
  | Std_X => domega_matrix_x
  | Std_Y => domega_matrix_y
  | Std_Z => domega_matrix_z
  | Std_H => domega_matrix_h
  | Std_S => domega_matrix_s
  | Std_Sdg => domega_matrix_sdg
  | Std_T => domega_matrix_t
  | Std_Tdg => domega_matrix_tdg
  | Std_SX => domega_matrix_sx
  | Std_SXdg => domega_matrix_sxdg
  end.

Definition standard_gate_matrix (gate : StandardGate) : Matrix 1%nat :=
  domega_matrix_to_matrix (standard_gate_domega_matrix gate).

Definition standard_seq_domega_matrix (gates : list StandardGate)
    : DOmegaMatrix :=
  fold_left
    (fun acc gate => domega_matrix_mul (standard_gate_domega_matrix gate) acc)
    gates
    domega_matrix_eye.

Definition standard_seq_matrix (gates : list StandardGate) : Matrix 1%nat :=
  domega_matrix_to_matrix (standard_seq_domega_matrix gates).

Lemma standard_seq_matrix_fold_left :
  forall gates acc,
    domega_matrix_to_matrix
      (fold_left
         (fun acc gate =>
            domega_matrix_mul (standard_gate_domega_matrix gate) acc)
         gates
         acc) =
    fold_left
      (fun acc gate => mat_mul (standard_gate_matrix gate) acc)
      gates
      (domega_matrix_to_matrix acc).
Proof.
  induction gates as [| gate rest IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite domega_matrix_mul_to_matrix.
    reflexivity.
Qed.

Lemma standard_seq_matrix_fold_right :
  forall gates,
    standard_seq_matrix gates =
    fold_right
      (fun gate acc => mat_mul acc (standard_gate_matrix gate))
      mat_eye
      gates.
Proof.
  intro gates.
  unfold standard_seq_matrix, standard_seq_domega_matrix.
  rewrite standard_seq_matrix_fold_left.
  assert (Hfold :
    forall acc,
      fold_left
        (fun acc gate => mat_mul (standard_gate_matrix gate) acc)
        gates
        acc =
      mat_mul
        (fold_right
           (fun gate prod => mat_mul prod (standard_gate_matrix gate))
           mat_eye
           gates)
        acc).
  { induction gates as [| gate rest IH]; intros acc; cbn [fold_left fold_right].
    - rewrite mat_mul_eye_l.
      reflexivity.
    - rewrite IH.
      rewrite mat_mul_assoc.
      reflexivity. }
  rewrite Hfold.
  rewrite domega_matrix_eye_to_matrix.
  rewrite mat_mul_eye_r.
  reflexivity.
Qed.

Lemma standard_seq_matrix_fold_right_map :
  forall gates,
    standard_seq_matrix gates =
    fold_right
      (fun mat acc => mat_mul acc mat)
      mat_eye
      (map standard_gate_matrix gates).
Proof.
  intro gates.
  rewrite standard_seq_matrix_fold_right.
  induction gates as [| gate rest IH]; cbn [map fold_right].
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

End STANDARD_GATE_MATRICES.

Section MATRIX_CORRESPONDENCE.

Lemma complex_of_domega_zero :
  complex_of_domega domega_zero = Czero.
Proof.
  unfold complex_of_domega, domega_zero, domega_make, complex_of_Q, Q2R.
  simpl; lca.
Qed.

Lemma complex_of_domega_one :
  complex_of_domega domega_one = Cone.
Proof.
  unfold complex_of_domega, domega_one, domega_make, complex_of_Q, Q2R.
  simpl; lca.
Qed.

Lemma complex_of_domega_w :
  complex_of_domega domega_w = omega.
Proof.
  unfold complex_of_domega, domega_w, domega_make, complex_of_Q, Q2R.
  simpl; lca.
Qed.

Lemma complex_of_domega_w2 :
  complex_of_domega domega_w2 = Ione.
Proof.
  unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
  simpl.
  replace (omega * omega)%com with (com_iexp (PI / 2)).
  - rewrite com_iexp_PI2. lca.
  - unfold omega.
    rewrite <- com_iexp_mul.
    replace (PI / 4 + PI / 4)%R with (PI / 2)%R by field.
    reflexivity.
Qed.

Lemma complex_of_domega_w3 :
  complex_of_domega domega_w3 = (omega * Ione)%com.
Proof.
  unfold complex_of_domega, domega_w3, domega_make, complex_of_Q, Q2R.
  simpl.
  replace (omega * omega)%com with Ione.
  - lca.
  - rewrite <- complex_of_domega_w2.
    unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
    simpl; lca.
Qed.

Lemma complex_of_domega_neg_one :
  complex_of_domega (domega_neg domega_one) = (- Cone)%com.
Proof.
  unfold complex_of_domega, domega_neg, domega_one, domega_make, complex_of_Q,
    Q2R.
  simpl.
  lca.
Qed.

Lemma complex_of_domega_neg_w2 :
  complex_of_domega (domega_neg domega_w2) = (- Ione)%com.
Proof.
  unfold complex_of_domega, domega_neg, domega_w2, domega_make, complex_of_Q,
    Q2R.
  simpl.
  replace (omega * omega)%com with Ione.
  - lca.
  - rewrite <- complex_of_domega_w2.
    unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
    simpl.
    lca.
Qed.

Lemma complex_of_domega_neg_w3 :
  complex_of_domega (domega_neg domega_w3) = (- (omega * Ione))%com.
Proof.
  unfold complex_of_domega, domega_neg, domega_w3, domega_make, complex_of_Q,
    Q2R.
  simpl.
  replace (omega * omega)%com with Ione.
  - lca.
  - rewrite <- complex_of_domega_w2.
    unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
    simpl.
    lca.
Qed.

Lemma standard_gate_matrix_I :
  standard_gate_matrix Std_I = mat_eye.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_to_matrix, domega_matrix_eye,
    domega_matrix_make.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_matrix_X :
  standard_gate_matrix Std_X = Gate_X_matrix.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_x,
    domega_matrix_to_matrix, domega_matrix_make, Gate_X_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_matrix_Y :
  standard_gate_matrix Std_Y = Gate_Y_matrix.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_y,
    domega_matrix_to_matrix, domega_matrix_make, Gate_Y_matrix, domega_minus_i.
  simpl.
  rewrite complex_of_domega_zero, complex_of_domega_w2, complex_of_domega_neg_w2.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_matrix_Z :
  standard_gate_matrix Std_Z = Gate_Z_matrix.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_z,
    domega_matrix_to_matrix, domega_matrix_make, Gate_Z_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_neg_one.
  repeat (f_equal; try lca).
Qed.

Lemma domega_h_scalar_to_complex :
  complex_of_domega domega_h_scalar = (/ sqrt 2)%R.
Proof.
  replace (complex_of_domega domega_h_scalar)
    with
      (complex_of_Q qhalf
       * (omega - (omega * Ione)))%com.
  - unfold complex_of_Q, Q2R, qhalf, omega.
    simpl.
    unfold com_iexp.
    rewrite cos_PI4, sin_PI4.
    lca.
  - unfold domega_h_scalar, complex_of_domega, domega_make, complex_of_Q,
      Q2R, qhalf.
    simpl.
    replace (omega * omega)%com with Ione.
    + lca.
    + rewrite <- complex_of_domega_w2.
      unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
      simpl.
      lca.
Qed.

Lemma standard_gate_matrix_H :
  standard_gate_matrix Std_H = Gate_H_matrix.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_h,
    domega_matrix_to_matrix, domega_matrix_make, Gate_H_matrix.
  simpl.
  rewrite domega_h_scalar_to_complex.
  replace (complex_of_domega (domega_neg domega_h_scalar))
    with (- (/ sqrt 2)%R)%com.
  - repeat (f_equal; try lca).
  - unfold domega_h_scalar, complex_of_domega, domega_neg, domega_make,
      complex_of_Q, Q2R, qhalf.
    simpl.
    replace (omega * omega)%com with Ione.
    + unfold omega, com_iexp.
      rewrite cos_PI4, sin_PI4.
      lca.
    + rewrite <- complex_of_domega_w2.
      unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
      simpl.
      lca.
Qed.

Definition phase_gate_matrix (lambda : R) : Matrix 1%nat :=
  rec_mat
    (bas_mat Cone)
    (bas_mat Czero)
    (bas_mat Czero)
    (bas_mat (com_iexp lambda)).

Lemma phase_gate_matrix_gphase :
  forall lambda,
    mat_rot 0 0 lambda =
    gphase (- lambda / 2) .* phase_gate_matrix lambda.
Proof.
  intros lambda.
  unfold mat_rot, phase_gate_matrix, gphase.
  rewrite mat_rot_y_0_eye, mat_rot_z_0_eye.
  repeat rewrite mat_mul_eye_l.
  unfold mat_rot_z.
  simpl.
  f_equal; f_equal; try lca.
  rewrite <- com_iexp_mul.
  replace (- lambda / 2 + lambda)%R with (lambda / 2)%R by field.
  reflexivity.
Qed.

Lemma standard_gate_matrix_S :
  standard_gate_matrix Std_S = phase_gate_matrix PI2.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_s,
    domega_matrix_to_matrix, domega_matrix_make, phase_gate_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_w2, com_iexp_pi2.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_matrix_Sdg :
  standard_gate_matrix Std_Sdg = phase_gate_matrix (- PI2).
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_sdg,
    domega_matrix_to_matrix, domega_matrix_make, phase_gate_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_neg_w2, com_iexp_neg_pi2.
  repeat (f_equal; try lca).
Qed.

Lemma standard_gate_matrix_T :
  standard_gate_matrix Std_T = phase_gate_matrix (PI / 4).
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_t,
    domega_matrix_to_matrix, domega_matrix_make, phase_gate_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_w.
  unfold omega.
  repeat (f_equal; try lca).
Qed.

Lemma complex_of_domega_neg_w3_exp :
  complex_of_domega (domega_neg domega_w3) = com_iexp (- PI / 4).
Proof.
  rewrite complex_of_domega_neg_w3.
  replace (- PI / 4)%R with (-(PI / 4))%R by field.
  unfold omega, com_iexp.
  rewrite cos_neg, sin_neg, cos_PI4, sin_PI4.
  lca.
Qed.

Lemma standard_gate_matrix_Tdg :
  standard_gate_matrix Std_Tdg = phase_gate_matrix (- PI / 4).
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix, domega_matrix_tdg,
    domega_matrix_to_matrix, domega_matrix_make, phase_gate_matrix.
  simpl.
  rewrite complex_of_domega_one, complex_of_domega_zero,
    complex_of_domega_neg_w3_exp.
  repeat (f_equal; try lca).
Qed.

Lemma complex_of_domega_half_one_plus_i :
  complex_of_domega domega_half_one_plus_i =
  (RTC (1 / 2) * (Cone + Ione))%com.
Proof.
  unfold domega_half_one_plus_i, domega_one_plus_i, domega_add,
    domega_scale, domega_make, domega_one, domega_w2.
  unfold complex_of_domega, complex_of_Q, Q2R.
  simpl.
  replace (omega * omega)%com with Ione.
  - lca.
  - rewrite <- complex_of_domega_w2.
    unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
    simpl.
    lca.
Qed.

Lemma complex_of_domega_half_one_minus_i :
  complex_of_domega domega_half_one_minus_i =
  (RTC (1 / 2) * (Cone - Ione))%com.
Proof.
  unfold domega_half_one_minus_i, domega_one_minus_i, domega_sub,
    domega_add, domega_neg, domega_scale, domega_make, domega_one,
    domega_w2.
  unfold complex_of_domega, complex_of_Q, Q2R.
  simpl.
  replace (omega * omega)%com with Ione.
  - lca.
  - rewrite <- complex_of_domega_w2.
    unfold complex_of_domega, domega_w2, domega_make, complex_of_Q, Q2R.
    simpl.
    lca.
Qed.

Ltac close_sqrt2_field :=
  apply com_proj_eq; simpl; field_simplify_eq;
  try solve [apply sqrt2_neq_0];
  try replace (sqrt 2 ^ 2)%R with 2%R by
    (simpl; rewrite Rmult_1_r; rewrite sqrt_sqrt; lra);
  lra.

Lemma standard_gate_matrix_SX_gphase :
  mat_rot PI2 (- PI2) PI2 =
  gphase (- PI / 4) .* standard_gate_matrix Std_SX.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix,
    domega_matrix_sx, domega_matrix_to_matrix, domega_matrix_make.
  simpl.
  rewrite complex_of_domega_half_one_plus_i,
    complex_of_domega_half_one_minus_i.
  unfold mat_rot, mat_rot_y, mat_rot_z, gphase.
  simpl.
  replace (PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  replace (- PI2 / 2)%R with (- (PI / 4))%R by (unfold PI; field).
  replace (- - PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  replace (- PI / 4)%R with (-(PI / 4))%R by field.
  unfold com_iexp.
  rewrite !cos_neg, !sin_neg, !cos_PI4, !sin_PI4.
  repeat match goal with
  | |- rec_mat _ _ _ _ = rec_mat _ _ _ _ => f_equal
  | |- bas_mat _ = bas_mat _ => f_equal
  end.
  all: close_sqrt2_field.
Qed.

Lemma standard_gate_matrix_SXdg_gphase :
  mat_rot PI2 PI2 (- PI2) =
  gphase (PI / 4) .* standard_gate_matrix Std_SXdg.
Proof.
  unfold standard_gate_matrix, standard_gate_domega_matrix,
    domega_matrix_sxdg, domega_matrix_to_matrix, domega_matrix_make.
  simpl.
  rewrite complex_of_domega_half_one_plus_i,
    complex_of_domega_half_one_minus_i.
  unfold mat_rot, mat_rot_y, mat_rot_z, gphase.
  simpl.
  replace (PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  replace (- PI2 / 2)%R with (- (PI / 4))%R by (unfold PI; field).
  replace (- - PI2 / 2)%R with (PI / 4)%R by (unfold PI; field).
  unfold com_iexp.
  rewrite !cos_neg, !sin_neg, !cos_PI4, !sin_PI4.
  repeat match goal with
  | |- rec_mat _ _ _ _ = rec_mat _ _ _ _ => f_equal
  | |- bas_mat _ = bas_mat _ => f_equal
  end.
  all: close_sqrt2_field.
Qed.

Lemma Matrix_of_rotate_with_global_phase :
  forall nq theta phi lambda qbit phase U,
    mat_rot (Angle_to_R theta) (Angle_to_R phi) (Angle_to_R lambda) =
    gphase phase .* U ->
    Matrix_of nq (RotateInstr theta phi lambda qbit)
      (mat_single nq qbit U).
Proof.
  intros nq theta phi lambda qbit phase U Hphase ps cstate.
  simpl.
  unfold Execute_rotate_instr, Execute_rotate_instr_branch.
  f_equal; f_equal.
  apply functional_extensionality.
  intros branch.
  f_equal.
  rewrite Hphase.
  destruct (le_lt_dec nq qbit) as [Hout | Hin].
  - repeat rewrite (mat_single_out_of_bounds _ Hout).
    reflexivity.
  - rewrite (mat_single_scale _ _ Hin).
    rewrite den_uop_gphase.
    reflexivity.
Qed.

Theorem Matrix_of_standard_gate :
  forall nq gate qbit,
    Matrix_of nq (standard_gate_instr gate qbit)
      (mat_single nq qbit (standard_gate_matrix gate)).
Proof.
  intros nq gate qbit.
  destruct gate; simpl.
  - rewrite standard_gate_matrix_I, mat_single_eye.
    apply Matrix_of_I.
  - rewrite standard_gate_matrix_X.
    apply Matrix_of_X.
  - rewrite standard_gate_matrix_Y.
    apply Matrix_of_Y.
  - rewrite standard_gate_matrix_Z.
    apply Matrix_of_Z.
  - rewrite standard_gate_matrix_H.
    apply Matrix_of_H.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_S.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_Sdg.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_T.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    replace (-(PI / 4))%R with (- PI / 4)%R by field.
    rewrite standard_gate_matrix_Tdg.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    apply standard_gate_matrix_SX_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    apply standard_gate_matrix_SXdg_gphase.
Qed.

End MATRIX_CORRESPONDENCE.

Section STANDARD_CHECKER.

Definition standard_transform_validb
    (lhs rhs : list StandardGate) : bool :=
  domega_matrix_eq_up_to_phaseb
    (standard_seq_domega_matrix lhs)
    (standard_seq_domega_matrix rhs).

Lemma standard_transform_validb_sound :
  forall lhs rhs,
    standard_transform_validb lhs rhs = true ->
    exists phase,
      In phase domega_phase_list
      /\ domega_matrix_equiv
           (standard_seq_domega_matrix lhs)
           (domega_matrix_scale phase (standard_seq_domega_matrix rhs)).
Proof.
  intros lhs rhs H.
  unfold standard_transform_validb in H.
  apply domega_matrix_eq_up_to_phaseb_sound.
  assumption.
Qed.

Definition standard_gate_pattern
    (gate : StandardGate) (qbit_pattern : NatPattern)
    : InstructionPattern :=
  match gate with
  | Std_I => PRotate A0 A0 A0 qbit_pattern
  | Std_X => PRotate API A0 API qbit_pattern
  | Std_Y => PRotate API API2 API2 qbit_pattern
  | Std_Z => PRotate A0 A0 API qbit_pattern
  | Std_H => PRotate API2 A0 API qbit_pattern
  | Std_S => PRotate A0 A0 API2 qbit_pattern
  | Std_Sdg => PRotate A0 A0 ANPI2 qbit_pattern
  | Std_T => PRotate A0 A0 API4 qbit_pattern
  | Std_Tdg => PRotate A0 A0 ANPI4 qbit_pattern
  | Std_SX => PRotate API2 ANPI2 API2 qbit_pattern
  | Std_SXdg => PRotate API2 API2 ANPI2 qbit_pattern
  end.

Definition standard_gate_pattern_instr
    (gate : StandardGate) (qbit : nat)
    : Instruction :=
  match gate with
  | Std_I => RotateInstr A0 A0 A0 qbit
  | Std_X => RotateInstr API A0 API qbit
  | Std_Y => RotateInstr API API2 API2 qbit
  | Std_Z => RotateInstr A0 A0 API qbit
  | Std_H => RotateInstr API2 A0 API qbit
  | Std_S => RotateInstr A0 A0 API2 qbit
  | Std_Sdg => RotateInstr A0 A0 ANPI2 qbit
  | Std_T => RotateInstr A0 A0 API4 qbit
  | Std_Tdg => RotateInstr A0 A0 ANPI4 qbit
  | Std_SX => RotateInstr API2 ANPI2 API2 qbit
  | Std_SXdg => RotateInstr API2 API2 ANPI2 qbit
  end.

Lemma Matrix_of_standard_gate_pattern :
  forall nq gate qbit,
    Matrix_of nq (standard_gate_pattern_instr gate qbit)
      (mat_single nq qbit (standard_gate_matrix gate)).
Proof.
  intros nq gate qbit.
  destruct gate; unfold standard_gate_pattern_instr.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_I.
    rewrite Gate_P_matrix_0_eye.
    unfold gphase.
    rewrite com_iexp_0, mat_scale_1.
    reflexivity.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_X.
    apply Gate_X_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_Y.
    apply Gate_Y_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_Z.
    apply Gate_Z_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_H.
    apply Gate_H_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_S.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_Sdg.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    rewrite standard_gate_matrix_T.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    replace (-(PI / 4))%R with (- PI / 4)%R by field.
    rewrite standard_gate_matrix_Tdg.
    apply phase_gate_matrix_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    apply standard_gate_matrix_SX_gphase.
  - eapply Matrix_of_rotate_with_global_phase.
    angle_to_R_simpl.
    apply standard_gate_matrix_SXdg_gphase.
Qed.

Definition standard_rule_of_sequences
    (lhs rhs : list StandardGate) : option RewriteRule :=
  if standard_transform_validb lhs rhs then
    Some
      {|
        rule_lhs := map (fun gate => standard_gate_pattern gate (NatVar 0)) lhs;
        rule_rhs := map (fun gate => standard_gate_pattern gate (NatVar 0)) rhs
      |}
  else
    None.

Lemma domega_phase_gphase :
  forall phase,
    In phase domega_phase_list ->
    exists lambda,
      complex_of_domega phase = gphase lambda.
Proof.
  intros phase Hin.
  simpl in Hin.
  repeat destruct Hin as [Hin | Hin]; subst; try contradiction.
  - exists 0%R.
    rewrite complex_of_domega_one.
    unfold gphase.
    rewrite com_iexp_0.
    reflexivity.
  - exists (PI / 4)%R.
    rewrite complex_of_domega_w.
    unfold omega, gphase.
    reflexivity.
  - exists (PI / 2)%R.
    rewrite complex_of_domega_w2.
    unfold gphase.
    rewrite com_iexp_PI2.
    reflexivity.
  - exists (PI / 4 + PI / 2)%R.
    rewrite complex_of_domega_w3.
    unfold omega, gphase.
    rewrite <- com_iexp_PI2.
    rewrite <- com_iexp_mul.
    reflexivity.
  - exists PI.
    rewrite complex_of_domega_neg_one.
    unfold gphase.
    rewrite com_iexp_PI.
    lca.
  - exists (PI + PI / 4)%R.
    rewrite complex_of_domega_neg, complex_of_domega_w.
    unfold omega, gphase.
    replace (- com_iexp (PI / 4))%com
      with (com_iexp PI * com_iexp (PI / 4))%com
      by (rewrite com_iexp_PI; lca).
    rewrite <- com_iexp_mul.
    reflexivity.
  - exists (PI + PI / 2)%R.
    rewrite complex_of_domega_neg_w2.
    unfold gphase.
    replace (- Ione)%com with (com_iexp PI * Ione)%com
      by (rewrite com_iexp_PI; lca).
    rewrite <- com_iexp_PI2.
    rewrite <- com_iexp_mul.
    reflexivity.
  - exists (PI + PI / 4 + PI / 2)%R.
    rewrite complex_of_domega_neg_w3.
    unfold omega, gphase.
    replace (- (com_iexp (PI / 4) * Ione))%com
      with (com_iexp PI * (com_iexp (PI / 4) * Ione))%com
      by (rewrite com_iexp_PI; lca).
    rewrite <- com_iexp_PI2.
    rewrite com_mul_assoc.
    repeat rewrite <- com_iexp_mul.
    reflexivity.
Qed.

Lemma standard_transform_validb_matrix_sound :
  forall lhs rhs,
    standard_transform_validb lhs rhs = true ->
    exists lambda,
      standard_seq_matrix lhs =
      mat_scale (gphase lambda) (standard_seq_matrix rhs).
Proof.
  intros lhs rhs Hvalid.
  destruct (standard_transform_validb_sound _ _ Hvalid)
    as [phase [Hphase Hequiv]].
  destruct (domega_phase_gphase _ Hphase) as [lambda Hlambda].
  exists lambda.
  unfold standard_seq_matrix.
  rewrite (domega_matrix_equiv_to_matrix _ _ Hequiv).
  rewrite domega_matrix_scale_to_matrix.
  rewrite Hlambda.
  reflexivity.
Qed.

Lemma standard_gate_pattern_inst :
  forall gate subst qbit,
    NatMap.find 0%nat (pattern_nat_map subst) = Some qbit ->
    InstructionPattern_inst
      (standard_gate_pattern gate (NatVar 0))
      subst =
    Some (standard_gate_pattern_instr gate qbit).
Proof.
  intros gate subst qbit Hfind.
  destruct gate; simpl; rewrite Hfind; reflexivity.
Qed.

Lemma standard_gate_pattern_inst_list :
  forall gates subst qbit,
    NatMap.find 0%nat (pattern_nat_map subst) = Some qbit ->
    InstructionPattern_inst_list
      (map (fun gate => standard_gate_pattern gate (NatVar 0)) gates)
      subst =
    Some (map (fun gate => standard_gate_pattern_instr gate qbit) gates).
Proof.
  induction gates as [| gate rest IH]; intros subst qbit Hfind; simpl.
  - reflexivity.
  - rewrite standard_gate_pattern_inst with (qbit := qbit).
    + rewrite IH with (qbit := qbit).
      * reflexivity.
      * assumption.
    + assumption.
Qed.

Lemma standard_gate_pattern_inst_list_none :
  forall gates subst,
    NatMap.find 0%nat (pattern_nat_map subst) = None ->
    InstructionPattern_inst_list
      (map (fun gate => standard_gate_pattern gate (NatVar 0)) gates)
      subst =
    match gates with
    | [] => Some []
    | _ :: _ => None
    end.
Proof.
  destruct gates as [| gate rest]; intros subst Hfind; simpl.
  - reflexivity.
  - destruct gate; simpl; rewrite Hfind; reflexivity.
Qed.

Lemma Matrix_of_standard_gate_pattern_list :
  forall nq qbit gates,
    Matrix_of_list nq
      (map (fun gate => standard_gate_pattern_instr gate qbit) gates)
      (map (fun gate => mat_single nq qbit (standard_gate_matrix gate)) gates).
Proof.
  induction gates as [| gate rest IH]; simpl.
  - apply nil_mat.
  - apply cons_mat.
    + apply Matrix_of_standard_gate_pattern.
    + apply IH.
Qed.

Lemma standard_sequence_matrix_of_list_product :
  forall nq qbit gates,
    fold_right
      (fun mat acc => mat_mul acc mat)
      mat_eye
      (map (fun gate => mat_single nq qbit (standard_gate_matrix gate)) gates) =
    if Nat.ltb qbit nq
    then mat_single nq qbit (standard_seq_matrix gates)
    else mat_eye.
Proof.
  intros nq qbit gates.
  destruct (Nat.ltb qbit nq) eqn:Hqbit.
  - apply Nat.ltb_lt in Hqbit.
    rewrite standard_seq_matrix_fold_right_map.
    induction gates as [| gate rest IH]; cbn [map fold_right].
    + rewrite mat_single_eye.
      reflexivity.
    + rewrite IH.
      rewrite mat_single_factorized.
      reflexivity.
  - apply Nat.ltb_ge in Hqbit.
    induction gates as [| gate rest IH]; cbn [map fold_right].
    + reflexivity.
    + rewrite IH.
      rewrite mat_single_out_of_bounds by lia.
      rewrite mat_mul_eye_l.
      reflexivity.
Qed.

Lemma standard_transform_validb_matrix_list_sound :
  forall nq qbit lhs rhs,
    standard_transform_validb lhs rhs = true ->
    exists lambda,
      fold_right
        (fun mat acc => mat_mul acc mat)
        mat_eye
        (map (fun gate => mat_single nq qbit (standard_gate_matrix gate)) lhs) =
      mat_scale
        (gphase lambda)
        (fold_right
           (fun mat acc => mat_mul acc mat)
           mat_eye
           (map
              (fun gate => mat_single nq qbit (standard_gate_matrix gate))
              rhs)).
Proof.
  intros nq qbit lhs rhs Hvalid.
  destruct (standard_transform_validb_matrix_sound _ _ Hvalid)
    as [lambda Hmatrix].
  destruct (Nat.ltb qbit nq) eqn:Hqbit.
  - exists lambda.
    rewrite (standard_sequence_matrix_of_list_product nq qbit lhs).
    rewrite (standard_sequence_matrix_of_list_product nq qbit rhs).
    rewrite Hqbit.
    apply Nat.ltb_lt in Hqbit.
    rewrite Hmatrix.
    rewrite mat_single_scale by lia.
    reflexivity.
  - exists 0%R.
    rewrite (standard_sequence_matrix_of_list_product nq qbit lhs).
    rewrite (standard_sequence_matrix_of_list_product nq qbit rhs).
    rewrite Hqbit.
    unfold gphase.
    rewrite com_iexp_0, mat_scale_1.
    reflexivity.
Qed.

Lemma standard_transform_rule_pattern_valid :
  forall nq name lhs_gates rhs_gates,
    standard_transform_validb lhs_gates rhs_gates = true ->
    PatternRuleEquivValid nq
      (TransformSpec_simple_rule name
        {|
          rule_lhs :=
            map (fun gate => standard_gate_pattern gate (NatVar 0)) lhs_gates;
          rule_rhs :=
            map (fun gate => standard_gate_pattern gate (NatVar 0)) rhs_gates
        |})
      Param_None.
Proof.
  intros nq name lhs_gates rhs_gates Hvalid.
  simpl.
  intros rule Hrule subst lhs rhs Hlhs Hrhs _.
  inversion Hrule; subst rule; clear Hrule.
  simpl in *.
    destruct (NatMap.find 0%nat (pattern_nat_map subst))
      as [qbit |] eqn:Hfind.
    + rewrite (standard_gate_pattern_inst_list lhs_gates subst qbit Hfind) in Hlhs.
    rewrite (standard_gate_pattern_inst_list rhs_gates subst qbit Hfind) in Hrhs.
    inversion Hlhs; inversion Hrhs; subst; clear Hlhs Hrhs.
    eapply Instruction_equiv_of_seqs_from_matrix.
    * apply Matrix_of_standard_gate_pattern_list.
    * apply Matrix_of_standard_gate_pattern_list.
    * apply standard_transform_validb_matrix_list_sound.
      assumption.
    + rewrite (standard_gate_pattern_inst_list_none lhs_gates subst Hfind) in Hlhs.
    rewrite (standard_gate_pattern_inst_list_none rhs_gates subst Hfind) in Hrhs.
    destruct lhs_gates as [| lhs_gate lhs_rest]; try discriminate.
    destruct rhs_gates as [| rhs_gate rhs_rest]; try discriminate.
    inversion Hlhs; inversion Hrhs; subst.
    reflexivity.
Qed.

Lemma standard_rule_of_sequences_pattern_valid :
  forall nq name lhs rhs rule,
    standard_rule_of_sequences lhs rhs = Some rule ->
    PatternRuleEquivValid nq
      (TransformSpec_simple_rule name rule)
      Param_None.
Proof.
  intros nq name lhs rhs rule Hrule.
  unfold standard_rule_of_sequences in Hrule.
  destruct (standard_transform_validb lhs rhs) eqn:Hvalid; try discriminate.
  inversion Hrule; subst; clear Hrule.
  apply standard_transform_rule_pattern_valid.
  assumption.
Qed.

Theorem standard_rule_transform_spec_valid :
  forall nq name lhs rhs rule,
    standard_rule_of_sequences lhs rhs = Some rule ->
    TransformSpecValid nq (TransformSpec_simple_rule name rule).
Proof.
  intros nq name lhs rhs rule Hrule.
  unfold TransformSpecValid.
  intros param.
  destruct param; simpl.
  all: try (intros rule' Hnone; discriminate).
  eapply standard_rule_of_sequences_pattern_valid.
  apply Hrule.
Qed.

End STANDARD_CHECKER.
