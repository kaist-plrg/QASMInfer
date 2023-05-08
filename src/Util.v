Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export List.
Require Export Coq.Logic.ProofIrrelevance.
Require Export Coq.Logic.PropExtensionality.
Import ListNotations.

Open Scope nat_scope.
Open Scope bool_scope.
Open Scope list_scope.
Declare Scope util_scope.

(* a list of range 0..n ========================================================================= *)

Fixpoint range_suppl (n i: nat): list nat.
Proof.
  destruct n as [|n'].
  - exact [].
  - exact (i :: range_suppl n' (i + 1)).
Defined.

Definition range (n: nat): list nat := range_suppl n 0.

Fact in_range_suppl_lt: forall (x n m: nat), In x (range_suppl n m) -> x < n + m.
Proof.
  induction n as [|n'].
  - simpl. contradiction.
  - simpl.
    intros.
    destruct H.
    + lia.
    + apply IHn' in H.
      lia.
Qed.

Fact in_range_lt: forall (x n: nat), In x (range n) -> x < n.
Proof.
  unfold range.
  intros.
  replace n with (n + 0).
  apply in_range_suppl_lt.
  apply H.
  lia.
Qed.

Fact length_range_suppl: forall n m: nat, length (range_suppl n m) = n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    intros.
    f_equal.
    apply IHn'.
Qed.

Fact length_range: forall n: nat, length (range n) = n.
Proof.
  unfold range.
  intros.
  apply length_range_suppl.
Qed.

(* ============================================================================================== *)
(* mapping list with the proof of inclusion ===================================================== *)

Fixpoint map_with_proof {A B: Type} (l: list A): (forall x, In x l -> B) -> list B :=
  match l with
  | [] => fun _ => []
  | h :: t => fun f => (f h (in_eq h t)) :: (map_with_proof t (fun x H => f x (in_cons h x t H)))
  end.

Fixpoint map_range_with_proof {A: Type} (n m: nat): (forall x, x < m + n -> A) -> list A.
Proof.
  destruct (range_suppl n m) as [|h t] eqn: E.
  - refine ( fun _ => []).
  - destruct n as [|n'].
    + simpl in E. discriminate E.
    + refine (fun f => (f h _) :: (map_range_with_proof A n' (1 + m) (fun x H => f x _))).
      * simpl in E. inversion E. lia.
      * lia.
Defined.

Fact length_map_with_proof: forall (A B: Type) (l: list A) (f: (forall x, In x l -> B)),
  length (map_with_proof l f) = length l.
Proof.
  intros.
  induction l as [|h t].
  - reflexivity.
  - simpl.
    f_equal.
    apply IHt.
Qed.

Fact fun_eq_in_map_with_proof:
  forall (A B: Type) (l: list A) (f: forall x, In x l -> B) (x: A) (H1: In x l) (H2: In x l),
  f x H1 = f x H2.
Proof.
  intros.
  assert (H1 = H2) by apply proof_irrelevance.
  rewrite H.
  reflexivity.
Qed.

Fact fun_eq_in_map_range_with_proof:
  forall (A: Type) (x n: nat) (f: forall x, x < n -> A) (H1: x < n) (H2: x < n),
  f x H1 = f x H2.
Proof.
  intros.
  assert (H1 = H2) by apply proof_irrelevance.
  rewrite H.
  reflexivity.
Qed.

(* ============================================================================================== *)
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

Lemma eq_nth_safe: forall (A: Type) (n: nat) (l: list A) (H1 H2: n < length l),
  nth_safe l n H1 = nth_safe l n H2.
Proof.
  intros.
  assert (H1 = H2) by apply proof_irrelevance.
  rewrite H.
  reflexivity.
Qed.

Lemma map_nth_safe: forall
(A B: Type) (f: A -> B) (l: list A) (n nmap: nat) (H: n < length l) (Hmap: nmap < length (map f l)),
nmap = n -> nth_safe (map f l) nmap Hmap = f (nth_safe l n H).
Proof.
  intros A B f l.
  induction l as [|h t].
  - intros. simpl in H. lia.
  - intros.
    destruct n as [|n'].
    + subst nmap.
      reflexivity.
    + subst nmap.
      apply IHt.
      reflexivity.
Qed.

Lemma firstn_nth_safe: forall
  (A: Type) (l: list A) (n1 n2: nat)
  (H1: n2 < length (firstn n1 l)) (H2: n2 < length l),
  n1 >= n2 -> nth_safe (firstn n1 l) n2 H1 = nth_safe l n2 H2.
Proof.
  intros.
  revert H1 H2 H.
  revert l n2.
  induction n1 as [|n1'].
  - intros.
    simpl in H1.
    lia.
  - intros.
    destruct l as [|h t].
    + simpl in H2.
      lia.
    + simpl.
      destruct n2 as [|n2'].
      * reflexivity.
      * apply IHn1'.
        lia.
Qed.

Lemma skipn_nth_safe: forall
  (A: Type) (l: list A) (n1 n2: nat)
  (H1: n2 < length (skipn n1 l)) (H2: n1 + n2 < length l),
  nth_safe (skipn n1 l) n2 H1 = nth_safe l (n1 + n2) H2.
Proof.
  intros A l.
  induction l as [|h t].
  - intros.
    simpl in H2.
    lia.
  - intros.
    destruct n1 as [|n1'].
    + destruct n2 as [|n2'].
      * reflexivity.
      * intros.
        simpl.
        apply eq_nth_safe.
    + intros.
      simpl.
      apply IHt.
Qed.


(* ============================================================================================== *)
(* combine two lists using the given binary operator ============================================ *)

Fixpoint bop_lists {A: Type} (bop: A -> A -> A) (l1 l2: list A) (H: length l1 = length l2):
{l: list A | length l = length l1} :=
  match l1, l2 return length l1 = length l2 -> {l: list A | length l = length l1} with
  | [], [] => fun _ => exist _ [] eq_refl
  | (x1::xs1), (x2::xs2) => fun H =>
      let res := bop_lists bop xs1 xs2 (f_equal pred H) in
      exist _ ((bop x1 x2) :: proj1_sig res) (f_equal S (proj2_sig res))
  | _, _ => fun H => ltac:(discriminate H)
  end H.

Property bop_lists_correct: forall
  (A: Type)
  (bop: A -> A -> A)
  (l1 l2 lz: list A)
  (n1 n2 nz: nat)
  (H12: length l1 = length l2)
  (H1z: length lz = length l1)
  (H1n: n1 < length l1)
  (H2n: n2 < length l2)
  (Hzn: nz < length lz),
  lz = proj1_sig (bop_lists bop l1 l2 H12) ->
  n1 = n2 -> n1 = nz ->
  nth_safe lz nz Hzn = bop (nth_safe l1 n1 H1n) (nth_safe l2 n2 H2n).
Proof.
  intros A bop l1.
  induction l1 as [|h1 t1].
  - intros.
    simpl in H1n.
    lia.
  - destruct l2 as [|h2 t2].
    + discriminate H12.
    + intros lz n.
      destruct lz as [|hz tz].
      * intros.
        simpl in Hzn.
        lia.
      * destruct n as [|n'].
        { simpl.
          intros.
          subst n2 nz.
          injection H as Hh _.
          apply Hh. }
        { intros.
          simpl in H12, H1z.
          injection H12 as Ht12.
          injection H1z as Ht1z.
          subst n2 nz.
          specialize (IHt1 t2 tz n' n' n' Ht12).
          apply IHt1.
          - apply Ht1z.
          - injection H.
            simpl.
            intros.
            replace Ht12 with (f_equal pred H12).
            + apply H0.
            + apply proof_irrelevance.
          - reflexivity.
          - reflexivity. }
Qed.
(* ============================================================================================== *)