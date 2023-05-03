Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export List.
Import ListNotations.

Open Scope bool_scope.
Open Scope list_scope.

(* get an nth element of a list safely ========================================================== *)
Fixpoint nth_safe {A: Type} (l: list A) (n: nat) (H: n < length l): A.
Proof.
  destruct l as [|h t].
  - simpl in H.
    lia.
  - destruct n as [|n'].
    + exact h.
    + simpl in H.
      refine (nth_safe A t n' _).
      lia.
Defined.

(* We can believe that built-in `nth_error` function is correct. *)
Property nth_safe_correct: forall (A: Type) (n: nat) (l: list A) (H: n < length l),
  nth_error l n = Some (nth_safe l n H).
Proof.
  intros.
  revert H.
  revert n.
  induction l as [|h t].
  - intros.
    simpl in H.
    lia.
  - intros.
    destruct n as [|n'].
    + reflexivity.
    + simpl in H.
      simpl.
      apply IHt.
Qed.

(* ============================================================================================== *)

Fixpoint bop_lists {A: Type} (bop: A -> A -> A) (l1 l2: list A) (H: length l1 = length l2):
{l: list A | length l = length l1} :=
  match l1, l2 return length l1 = length l2 -> {l: list A | length l = length l1} with
  | [], [] => fun _ => exist _ [] eq_refl
  | (x1::xs1), (x2::xs2) => fun H =>
      let res := bop_lists bop xs1 xs2 (f_equal pred H) in
      exist _ ((bop x1 x2) :: proj1_sig res) (f_equal S (proj2_sig res))
  | _, _ => fun H => ltac:(discriminate H)
  end H.

(* Fixpoint bop_lists {A: Type} (bop: A -> A -> A) (l1 l2: list A) (H: length l1 = length l2): list A :=
  match l1, l2 return length l1 = length l2 -> list A with
  | [], [] => fun _ => []
  | (x1::xs1), (x2::xs2) => fun H =>
      (bop x1 x2) :: (bop_lists bop xs1 xs2 (f_equal pred H))
  | _, _ => fun H => ltac:(discriminate H)
  end H.

Lemma bop_lists_same_length: forall (A: Type) (bop: A -> A -> A) (l1 l2: list A) (H: length l1 = length l2),
  length l1 = length (bop_lists bop l1 l2 H).
Proof.
  intros A bop l1 l2 H.
  induction l1 as [|h1 t1].
  - simpl in H.
    pose proof H as H'.
    symmetry in H'.
    apply length_zero_iff_nil in H'.
    now subst l2.
  - simpl.
  simpl in *. *)
