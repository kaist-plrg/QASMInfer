From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Reals.
Import List.ListNotations.

Definition total_map (V: Type) := nat -> V.

Definition tm_empty {V: Type} (v: V): total_map V := fun (_: nat) => v.

Definition tm_update {V: Type} (m: total_map V) (k: nat) (v: V): total_map V :=
  fun (x: nat) => if (x =? k) then v else m x.

Definition tmb_equal (m1 m2: total_map bool) (size: nat): bool.
Proof.
  induction size as [|size'].
  - exact (eqb (m1 0) (m2 0)).
  - exact (andb (eqb (m1 size') (m2 size')) IHsize').
Defined.

Definition option_bind {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition option_map {A B : Type} (o: option A) (f: A -> B): option B :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Notation "x >>= f" := (option_bind x f) (at level 50, left associativity).
Notation "x >>| f" := (option_map x f) (at level 50, left associativity).
Notation "x |> f" := ((fun x' => f x') x) (at level 50, left associativity).

Definition list_init {A: Type} (n: nat) (f: nat -> A): list A :=
  map f (seq 0 n).

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A): list B :=
  combine (seq 0 (length l)) l |> (map (fun p => f (fst p) (snd p))).

Definition option_l_map {A B: Type} (f: A -> option B) (l: list A): option (list B) :=
  fold_left (fun acc a => f a >>= (fun b => acc >>| (fun acc' => b :: acc'))) l (Some []).

Definition option_l_concat_map {A B: Type} (f: A -> option (list B)) (l: list A) :=
  (option_l_map f l) >>| @concat B.



Definition list_map (K V: Type) := list (K * V).

Definition lm_empty {K V: Type} (v: V): list_map K V := [].

Definition lm_add {K V: Type} (k: K) (v: V) (m: list_map K V): list_map K V :=
  (k, v) :: m.

Definition lm_find {K V: Type}
  (equal: K -> K -> bool) (m: list_map K V) (k: K): option V :=
  find (fun p => equal (fst p) k) m >>| snd.
