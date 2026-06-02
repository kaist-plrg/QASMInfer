From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Reals.
From Stdlib Require Export Psatz.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Open Scope nat_scope.
Bind Scope nat_scope with nat.

Section POSITIVEMAP_LEMMAS.
Lemma PositiveMap_xfoldi_xmapi {A B C} (f: positive -> B -> C -> C) (g: A -> B) :
  forall (m : PositiveMap.t A) (acc : C) (i : positive),
    PositiveMap.xfoldi f (PositiveMap.xmapi (fun _ v => g v) m i) acc i =
    PositiveMap.xfoldi (fun k v acc => f k (g v) acc) m acc i.
Proof.
  induction m as [| l IHl o r IHr]; intros acc i; simpl.
  - reflexivity.
  - destruct o as [x|]; simpl.
    + rewrite IHl. rewrite IHr. reflexivity.
    + rewrite IHl. rewrite IHr. reflexivity.
Qed.

Corollary PositiveMap_fold_map {A B C} (f: positive -> B -> C -> C) (g: A -> B) :
  forall (m : PositiveMap.t A) (acc : C),
    PositiveMap.fold f (PositiveMap.map g m) acc =
    PositiveMap.fold (fun k v acc => f k (g v) acc) m acc.
Proof.
  intros m acc.
  unfold PositiveMap.fold, PositiveMap.map.
  apply PositiveMap_xfoldi_xmapi.
Qed.

Lemma PositiveMap_find_map {A B} (f: A -> B) (i: positive) (m: PositiveMap.t A):
  PositiveMap.find i (PositiveMap.map f m) = option_map f (PositiveMap.find i m).
Proof.
  unfold PositiveMap.map.
  rewrite PositiveMap.gmapi.
  reflexivity.
Qed.

Lemma PositiveMap_add_remove {A} (k: positive) (old: A) (f: A -> R) (ps: PositiveMap.t A) (acc: R) :
  PositiveMap.find k ps = Some old ->
  (PositiveMap.fold (fun _ b acc => acc + f b) (PositiveMap.add k old (PositiveMap.remove k ps)) acc
  = PositiveMap.fold (fun _ b acc => acc + f b) ps acc)%R.
Proof.
  intros Hfind.
  apply PProperties.fold_Equal.
  - apply eq_equivalence.
  - unfold Proper. reflexivity.
  - unfold PProperties.transpose_neqkey.
    intros. lra.
  - intros x.
    destruct (PositiveMap.E.eq_dec x k) as [Hkeq | Hkneq].
    + rewrite Hkeq.
      rewrite PProperties.F.add_eq_o.
      * symmetry. assumption.
      * reflexivity.
    + rewrite PProperties.F.add_neq_o.
      rewrite PProperties.F.remove_neq_o.
      * reflexivity.
      * intro H. subst. contradiction.
      * intro H. subst. contradiction.
Qed.

Lemma PositiveMap_add_remove_equal {A} (k: positive) (new: A) (f: A -> R) (ps: PositiveMap.t A) (acc: R) :
  (PositiveMap.fold (fun _ b acc => acc + f b) (PositiveMap.add k new ps) acc =
  PositiveMap.fold (fun _ b acc => acc + f b) (PositiveMap.add k new (PositiveMap.remove k ps)) acc)%R.
Proof.
  apply PProperties.fold_Equal.
  - apply eq_equivalence.
  - unfold Proper. reflexivity.
  - unfold PProperties.transpose_neqkey.
    intros. lra.
  - intros x.
    destruct (PositiveMap.E.eq_dec x k) as [Hkeq | Hkneq].
    + rewrite Hkeq.
      rewrite PProperties.F.add_eq_o.
      rewrite PProperties.F.add_eq_o.
      all: reflexivity.
    + rewrite PProperties.F.add_neq_o.
      rewrite PProperties.F.add_neq_o.
      rewrite PProperties.F.remove_neq_o.
      all: try (intro H; subst; contradiction).
      reflexivity.
Qed.

End POSITIVEMAP_LEMMAS.