Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export List.
Require Export Coq.Logic.ProofIrrelevance.
Import ListNotations.

Open Scope nat_scope.
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

(* It is okay to believe that built-in `nth_error` function is correct. *)
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
(* combine two lists using the given binary operator============================================= *)

Fixpoint bop_lists {A: Type} (bop: A -> A -> A) (l1 l2: list A) (H: length l1 = length l2):
{l: list A | length l = length l1} :=
  match l1, l2 return length l1 = length l2 -> {l: list A | length l = length l1} with
  | [], [] => fun _ => exist _ [] eq_refl
  | (x1::xs1), (x2::xs2) => fun H =>
      let res := bop_lists bop xs1 xs2 (f_equal pred H) in
      exist _ ((bop x1 x2) :: proj1_sig res) (f_equal S (proj2_sig res))
  | _, _ => fun H => ltac:(discriminate H)
  end H.

Fact eq_le_trans: forall l m n: nat, l = m -> n < m -> n < l.
Proof. intros. lia. Qed.

Fact n_lt_l_new: forall
  (A: Type) (n: nat) (l1 l_new: list A) (H_new: length l_new = length l1) (Hn: n < length l1),
  n < length l_new.
Proof. intros. rewrite H_new. apply Hn. Qed.

Fact n_lt_l2: forall
  (A: Type) (n: nat) (l1 l2: list A) (H: length l1 = length l2) (Hn: n < length l1),
  n < length l2.
Proof. intros. rewrite <- H. apply Hn.
Qed.

Fact lt_pred: forall n m, S n < S m -> n < m.
Proof. lia. Qed.

Fact eq_pred: forall n m, S n = S m <-> n = m.
Proof. lia. Qed.


Property bop_lists_correct: forall
  (A: Type)
  (bop: A -> A -> A)
  (l1 l2 lz: list A)
  (H12: length l1 = length l2)
  (n: nat)
  (H1z: length lz = length l1)
  (H1n: n < length l1)
  (H2n: n < length l2)
  (Hzn: n < length lz),
  lz = proj1_sig (bop_lists bop l1 l2 H12) ->
  nth_safe lz n Hzn = bop (nth_safe l1 n H1n) (nth_safe l2 n H2n).
Proof.
  intros A bop l1.
  induction l1 as [|h1 t1].
  { intros.
    simpl in H1n.
    lia. }
  { destruct l2 as [|h2 t2].
    { discriminate H12. }
    { intros lz H12 n.
      revert H12.
      destruct lz as [|hz tz].
      { intros.
        simpl in Hzn.
        lia. }
      { destruct n as [|n'].
        { simpl.
          intros.
          injection H as Hh _.
          apply Hh. }
        { intros.
          simpl in H12, H1z.
          injection H12 as Ht12.
          injection H1z as Ht1z.
          specialize (IHt1 t2 tz Ht12).
          apply IHt1.
          { apply Ht1z. }
          { injection H.
            simpl.
            intros.
            replace Ht12 with (f_equal pred H12).
            { apply H0. }
            { apply proof_irrelevance. }
          }
        }
      }
    }
  }
Qed.

(* ============================================================================================== *)