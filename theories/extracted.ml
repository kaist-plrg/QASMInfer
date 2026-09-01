(*
 * GENERATED — DO NOT EDIT
 *
 * Source commit: 1f7abf61b9e2212edce46540d7c9b2178e7f5b8b
 * Rocq version: 9.1.0
 * Dune Rocq language version: 0.13
 * Extraction command: rocq repl -q -Q ../.. QASMInfer -batch -l ../../extract/Extract
 *)

(* Lines auto-prepended immediately after extraction. *)
[@@@warning "-27-33-39"] (* relax unused-variable/open warnings on generated code *)

(* Ensure record labels from Stdlib.Complex are in scope for extracted code. *)
open Complex

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> ( * ) n (pow n m0))
      m
 end

module Pos =
 struct
  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> Big_int_Z.mult_int_big_int 2 (succ p))
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p)
      (fun _ -> Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
      x

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p q0))
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q0))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add p q0))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (succ q0))
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        q0)
        (fun _ -> Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
        y)
      x

  (** val add_carry :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add_carry p q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p q0))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p q0))
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q0))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (succ q0))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        Big_int_Z.unit_big_int)
        y)
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 p))
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (pred_double p))
      (fun _ -> Big_int_Z.unit_big_int)
      x

  type mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> add y (Big_int_Z.mult_int_big_int 2 (mul p y)))
      (fun p -> Big_int_Z.mult_int_big_int 2 (mul p y))
      (fun _ -> y)
      x

  (** val compare_cont :
      comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> compare_cont r p q0)
        (fun q0 -> compare_cont Gt p q0)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> compare_cont Lt p q0)
        (fun q0 -> compare_cont r p q0)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb p q0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : Big_int_Z.big_int -> int **)

  let to_nat x =
    iter_op (+) x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> Big_int_Z.big_int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Coq_Pos =
 struct
  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec succ = Big_int_Z.succ_big_int

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add = Big_int_Z.add_big_int

  (** val add_carry :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add_carry p q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p q0))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p q0))
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q0))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (succ q0))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        Big_int_Z.unit_big_int)
        y)
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 p))
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (pred_double p))
      (fun _ -> Big_int_Z.unit_big_int)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Big_int_Z.unit_big_int
  | IsPos p ->
    IsPos ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Big_int_Z.mult_int_big_int 2 p)
  | x0 -> x0

  (** val double_pred_mask : Big_int_Z.big_int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> IsPos (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 p)))
      (fun p -> IsPos (Big_int_Z.mult_int_big_int 2
      (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : Big_int_Z.big_int -> Big_int_Z.big_int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> double_mask (sub_mask p q0))
        (fun q0 -> succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos (Big_int_Z.mult_int_big_int 2 p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> double_mask (sub_mask_carry p q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = (fun n m -> Big_int_Z.max_big_int
  Big_int_Z.unit_big_int (Big_int_Z.sub_big_int n m))

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec mul = Big_int_Z.mult_big_int

  (** val iter : ('a1 -> 'a1) -> 'a1 -> Big_int_Z.big_int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val compare_cont :
      comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let rec compare_cont = (fun c x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then c else if s < 0 then Lt else Gt)

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb p q0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : Big_int_Z.big_int -> int **)

  let to_nat x =
    iter_op (+) x (Stdlib.Int.succ 0)

  (** val pow :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pow x =
    iter (mul x) Big_int_Z.unit_big_int

  (** val size_nat : Big_int_Z.big_int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun _ -> Stdlib.Int.succ 0)
      p

  (** val ggcdn :
      int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (Big_int_Z.unit_big_int, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (Big_int_Z.unit_big_int, Big_int_Z.unit_big_int))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in
            (g, (aa, (add aa (Big_int_Z.mult_int_big_int 2 ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in
            (g, ((add bb (Big_int_Z.mult_int_big_int 2 ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, (Big_int_Z.mult_int_big_int 2 bb))))
          (fun _ -> (Big_int_Z.unit_big_int, (a, Big_int_Z.unit_big_int)))
          b)
        (fun a1 ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun _ ->
          let (g, p) = ggcdn n0 a1 b in
          let (aa, bb) = p in (g, ((Big_int_Z.mult_int_big_int 2 aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a1 b0 in ((Big_int_Z.mult_int_big_int 2 g), p))
          (fun _ -> (Big_int_Z.unit_big_int, (a, Big_int_Z.unit_big_int)))
          b)
        (fun _ -> (Big_int_Z.unit_big_int, (Big_int_Z.unit_big_int, b)))
        a)
      n

  (** val ggcd :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int) **)

  let ggcd a b =
    ggcdn ((+) (size_nat a) (size_nat b)) a b

  (** val of_nat : int -> Big_int_Z.big_int **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Big_int_Z.unit_big_int)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)



(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n0 l0)
    n

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a1 =
  match l with
  | [] -> a1
  | b :: l0 -> fold_left f l0 (f a1 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a1 = function
| [] -> a1
| b :: l0 -> f b (fold_right f a1 l0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

module Z =
 struct
  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      (fun p -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2 p))
      x

  (** val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p ->
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p))
      (fun p -> Big_int_Z.minus_big_int (Pos.pred_double p))
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      (fun p -> (Pos.pred_double p))
      (fun p -> Big_int_Z.minus_big_int
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      x

  (** val pos_sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> (Big_int_Z.mult_int_big_int 2 p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2
        q0))
        (fun q0 -> Big_int_Z.minus_big_int (Pos.pred_double q0))
        (fun _ -> Big_int_Z.zero_big_int)
        y)
      x

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add = Big_int_Z.add_big_int

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp = Big_int_Z.minus_big_int

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = Big_int_Z.sub_big_int

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul = Big_int_Z.mult_big_int

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eqb = Big_int_Z.eq_big_int

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let max = Big_int_Z.max_big_int

  (** val min :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let min = Big_int_Z.min_big_int

  (** val to_nat : Big_int_Z.big_int -> int **)

  let to_nat z0 =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> Big_int_Z.big_int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n0 -> (Pos.of_succ_nat n0))
      n

  (** val to_pos : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_pos z0 =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> p)
      (fun _ -> Big_int_Z.unit_big_int)
      z0

  (** val pos_div_eucl :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * Big_int_Z.big_int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' =
        add (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) r)
          Big_int_Z.unit_big_int
      in
      if ltb r' b
      then ((mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0),
             r')
      else ((add
              (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0)
              Big_int_Z.unit_big_int),
             (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) r in
      if ltb r' b
      then ((mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0),
             r')
      else ((add
              (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0)
              Big_int_Z.unit_big_int),
             (sub r' b)))
      (fun _ ->
      if leb (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) b
      then (Big_int_Z.zero_big_int, Big_int_Z.unit_big_int)
      else (Big_int_Z.unit_big_int, Big_int_Z.zero_big_int))
      a

  (** val div_eucl :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * Big_int_Z.big_int **)

  let div_eucl = Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> (zero_big_int, x)
  | 1 -> quomod_big_int x y
  | _ -> let (q, r) = quomod_big_int (add_int_big_int (-1) x) y in
          (add_int_big_int (-1) q, add_big_int (add_int_big_int 1 y) r))

  (** val div :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div = Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> zero_big_int
  | 1 -> div_big_int x y
  | _ -> add_int_big_int (-1) (div_big_int (add_int_big_int (-1) x) y))

  (** val even : Big_int_Z.big_int -> bool **)

  let even z0 =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      z0

  (** val sgn : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sgn z0 =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      z0

  (** val abs : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let abs = Big_int_Z.abs_big_int

  (** val ggcd :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int) **)

  let ggcd a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> ((abs b), (Big_int_Z.zero_big_int, (sgn b))))
      (fun a1 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> ((abs a), ((sgn a), Big_int_Z.zero_big_int)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a1 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a1 b0 in
        let (aa, bb) = p in (g, (aa, (Big_int_Z.minus_big_int bb))))
        b)
      (fun a1 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> ((abs a), ((sgn a), Big_int_Z.zero_big_int)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a1 b0 in
        let (aa, bb) = p in (g, ((Big_int_Z.minus_big_int aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a1 b0 in
        let (aa, bb) = p in
        (g, ((Big_int_Z.minus_big_int aa), (Big_int_Z.minus_big_int bb))))
        b)
      a

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec = Big_int_Z.eq_big_int
 end

type q = { qnum : Big_int_Z.big_int; qden : Big_int_Z.big_int }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)); qden =
    (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let (r1, r2) = snd (Z.ggcd q1 q2) in { qnum = r1; qden = (Z.to_pos r2) }

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : float -> coq_R

  val coq_Rrepr : coq_R -> float

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : float -> float **)

  let coq_Rabst = fun x -> x

  (** val coq_Rrepr : float -> float **)

  let coq_Rrepr = fun x -> x

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = Stdlib.(+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = Stdlib.( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = Stdlib.(~-.)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun x -> 1.0 /. x

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val rdiv :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv = Stdlib.(/.)

(** val q2R : q -> RbaseSymbolsImpl.coq_R **)

let q2R x =
  RbaseSymbolsImpl.coq_Rmult (Big_int_Z.float_of_big_int x.qnum)
    (RinvImpl.coq_Rinv (Big_int_Z.float_of_big_int x.qden))

(** val rgt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rgt_dec = (fun x y -> x > y)

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Nat_as_OT =
 struct
  type t = int

  (** val compare : int -> int -> int compare0 **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    (=)
 end

(** val append :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec append i j =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun ii ->
    (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
    (append ii j))
    (fun ii -> Big_int_Z.mult_int_big_int 2 (append ii j))
    (fun _ -> j)
    i

module PositiveMap =
 struct
  type key = Big_int_Z.big_int

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find i = function
  | Leaf -> None
  | Node (l, o, r) ->
    ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
       (fun ii -> find ii r)
       (fun ii -> find ii l)
       (fun _ -> o)
       i)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add i v = function
  | Leaf ->
    ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
       (fun ii -> Node (Leaf, None, (add ii v Leaf)))
       (fun ii -> Node ((add ii v Leaf), None, Leaf))
       (fun _ -> Node (Leaf, (Some v), Leaf))
       i)
  | Node (l, o, r) ->
    ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
       (fun ii -> Node (l, o, (add ii v r)))
       (fun ii -> Node ((add ii v l), o, r))
       (fun _ -> Node (l, (Some v), r))
       i)

  (** val xelements : 'a1 t -> key -> (key * 'a1) list **)

  let rec xelements m i =
    match m with
    | Leaf -> []
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         app
           (xelements l
             (append i (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
           ((i,
           x) :: (xelements r
                   (append i
                     ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                     Big_int_Z.unit_big_int))))
       | None ->
         app
           (xelements l
             (append i (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
           (xelements r
             (append i
               ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
               Big_int_Z.unit_big_int))))

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    xelements m Big_int_Z.unit_big_int

  (** val xmapi : (key -> 'a1 -> 'a2) -> 'a1 t -> key -> 'a2 t **)

  let rec xmapi f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node
        ((xmapi f l
           (append i (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))),
        (option_map (f i) o),
        (xmapi f r
          (append i
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            Big_int_Z.unit_big_int))))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    xmapi f m Big_int_Z.unit_big_int

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    mapi (fun _ -> f) m

  (** val xfoldi :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> key -> 'a2 **)

  let rec xfoldi f m v i =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         xfoldi f r
           (f i x
             (xfoldi f l v
               (append i (Big_int_Z.mult_int_big_int 2
                 Big_int_Z.unit_big_int))))
           (append i
             ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
             Big_int_Z.unit_big_int))
       | None ->
         xfoldi f r
           (xfoldi f l v
             (append i (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
           (append i
             ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
             Big_int_Z.unit_big_int)))

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    xfoldi f m i Big_int_Z.unit_big_int
 end

(** val rTC : RbaseSymbolsImpl.coq_R -> Complex.t **)

let rTC = fun x -> {re=x; im=0.0}

(** val rTIm : RbaseSymbolsImpl.coq_R -> Complex.t **)

let rTIm = fun y -> {re=0.0; im=y}

(** val nTC : int -> Complex.t **)

let nTC = fun n -> {re=float_of_int n; im=0.0}

(** val com_div : Complex.t -> Complex.t -> Complex.t **)

let com_div x y =
  Complex.mul x (Complex.inv y)

(** val com_iexp : RbaseSymbolsImpl.coq_R -> Complex.t **)

let com_iexp theta =
  Complex.add (rTC (Stdlib.cos theta)) (rTIm (Stdlib.sin theta))



type matrix =
| Bas_mat of Complex.t
| Rec_mat of int * matrix * matrix * matrix * matrix

(** val mat_case0 : (Complex.t -> 'a1) -> matrix -> 'a1 **)

let mat_case0 h = function
| Bas_mat a1 -> h a1
| Rec_mat (x, x0, x1, x2, x3) -> Obj.magic __ x x0 x1 x2 x3

(** val mat_caseS_ :
    int -> matrix -> (matrix -> matrix -> matrix -> matrix -> 'a1) -> 'a1 **)

let mat_caseS_ _ a h =
  match a with
  | Bas_mat x -> Obj.magic __ x __ h
  | Rec_mat (_, a1, a2, a3, a4) -> h a1 a2 a3 a4

(** val mat_rect2 :
    (Complex.t -> Complex.t -> 'a1) -> (int -> matrix -> matrix -> matrix ->
    matrix -> matrix -> matrix -> matrix -> matrix -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1) -> int -> matrix -> matrix -> 'a1 **)

let rec mat_rect2 bas rect _ a b =
  match a with
  | Bas_mat a1 -> mat_case0 (bas a1) b
  | Rec_mat (n0, a1, a2, a3, a4) ->
    mat_caseS_ n0 b (fun b1 b2 b3 b4 ->
      rect n0 a1 a2 a3 a4 b1 b2 b3 b4 (mat_rect2 bas rect n0 a1 b1)
        (mat_rect2 bas rect n0 a2 b2) (mat_rect2 bas rect n0 a3 b3)
        (mat_rect2 bas rect n0 a4 b4))

(** val mat_rect2_gen :
    (Complex.t -> Complex.t -> 'a1) -> (int -> matrix -> matrix -> matrix ->
    matrix -> matrix -> matrix -> matrix -> matrix -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1) -> int -> matrix -> matrix -> 'a1 **)

let rec mat_rect2_gen bas rect _ a b =
  match a with
  | Bas_mat a1 -> mat_case0 (bas a1) b
  | Rec_mat (n0, a1, a2, a3, a4) ->
    mat_caseS_ n0 b (fun b1 b2 b3 b4 ->
      rect n0 a1 a2 a3 a4 b1 b2 b3 b4 (mat_rect2_gen bas rect n0 a1 b1)
        (mat_rect2_gen bas rect n0 a1 b2) (mat_rect2_gen bas rect n0 a1 b3)
        (mat_rect2_gen bas rect n0 a1 b4) (mat_rect2_gen bas rect n0 a2 b1)
        (mat_rect2_gen bas rect n0 a2 b2) (mat_rect2_gen bas rect n0 a2 b3)
        (mat_rect2_gen bas rect n0 a2 b4) (mat_rect2_gen bas rect n0 a3 b1)
        (mat_rect2_gen bas rect n0 a3 b2) (mat_rect2_gen bas rect n0 a3 b3)
        (mat_rect2_gen bas rect n0 a3 b4) (mat_rect2_gen bas rect n0 a4 b1)
        (mat_rect2_gen bas rect n0 a4 b2) (mat_rect2_gen bas rect n0 a4 b3)
        (mat_rect2_gen bas rect n0 a4 b4))

(** val mat_0 : int -> matrix **)

let rec mat_0 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Bas_mat (nTC 0))
    (fun n0 -> Rec_mat (n0, (mat_0 n0), (mat_0 n0), (mat_0 n0), (mat_0 n0)))
    n

(** val mat_eye : int -> matrix **)

let rec mat_eye n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Bas_mat (nTC (Stdlib.Int.succ 0)))
    (fun n0 -> Rec_mat (n0, (mat_eye n0), (mat_0 n0), (mat_0 n0),
    (mat_eye n0)))
    n

(** val mat_map : (Complex.t -> Complex.t) -> int -> matrix -> matrix **)

let rec mat_map f _ = function
| Bas_mat a1 -> Bas_mat (f a1)
| Rec_mat (n0, a1, a2, a3, a4) ->
  Rec_mat (n0, (mat_map f n0 a1), (mat_map f n0 a2), (mat_map f n0 a3),
    (mat_map f n0 a4))

(** val mat_map2 :
    (Complex.t -> Complex.t -> Complex.t) -> int -> matrix -> matrix -> matrix **)

let mat_map2 g =
  mat_rect2 (fun a b -> Bas_mat (g a b))
    (fun n _ _ _ _ _ _ _ _ iH1 iH2 iH3 iH4 -> Rec_mat (n, iH1, iH2, iH3, iH4))

(** val mat_scale : int -> Complex.t -> matrix -> matrix **)

let mat_scale n a =
  mat_map (fun b -> Complex.mul a b) n

(** val mat_conjtrans : int -> matrix -> matrix **)

let rec mat_conjtrans _ = function
| Bas_mat c -> Bas_mat (Complex.conj c)
| Rec_mat (n, m0, m1, m2, m3) ->
  Rec_mat (n, (mat_conjtrans n m0), (mat_conjtrans n m2),
    (mat_conjtrans n m1), (mat_conjtrans n m3))

(** val mat_trace : int -> matrix -> Complex.t **)

let rec mat_trace _ = function
| Bas_mat c -> c
| Rec_mat (n, m0, _, _, m1) -> Complex.add (mat_trace n m0) (mat_trace n m1)

(** val mat_add : int -> matrix -> matrix -> matrix **)

let mat_add n =
  mat_map2 Complex.add n

(** val mat_mul : int -> matrix -> matrix -> matrix **)

let mat_mul =
  mat_rect2_gen (fun a b -> Bas_mat (Complex.mul a b))
    (fun n _ _ _ _ _ _ _ _ h11 h12 _ _ _ _ h23 h24 h31 h32 _ _ _ _ h43 h44 ->
    Rec_mat (n, (mat_add n h11 h23), (mat_add n h12 h24),
    (mat_add n h31 h43), (mat_add n h32 h44)))

(** val tensor_product : int -> int -> matrix -> matrix -> matrix **)

let rec tensor_product _ n a b =
  match a with
  | Bas_mat c -> mat_scale n c b
  | Rec_mat (n0, m, m0, m1, m2) ->
    Rec_mat (((+) n0 n), (tensor_product n0 n m b),
      (tensor_product n0 n m0 b), (tensor_product n0 n m1 b),
      (tensor_product n0 n m2 b))

(** val mat_rot_y : RbaseSymbolsImpl.coq_R -> matrix **)

let mat_rot_y _UU03b8_ =
  Rec_mat (0, (Bas_mat
    (rTC
      (Stdlib.cos
        (rdiv _UU03b8_
          (Big_int_Z.float_of_big_int (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))))),
    (Bas_mat
    (Complex.neg
      (rTC
        (Stdlib.sin
          (rdiv _UU03b8_
            (Big_int_Z.float_of_big_int (Big_int_Z.mult_int_big_int 2
              Big_int_Z.unit_big_int))))))),
    (Bas_mat
    (rTC
      (Stdlib.sin
        (rdiv _UU03b8_
          (Big_int_Z.float_of_big_int (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))))),
    (Bas_mat
    (rTC
      (Stdlib.cos
        (rdiv _UU03b8_
          (Big_int_Z.float_of_big_int (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))))))

(** val mat_rot_z : RbaseSymbolsImpl.coq_R -> matrix **)

let mat_rot_z _UU03b8_ =
  Rec_mat (0, (Bas_mat
    (com_iexp
      (rdiv (RbaseSymbolsImpl.coq_Ropp _UU03b8_)
        (Big_int_Z.float_of_big_int (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int))))),
    (Bas_mat (rTC (Big_int_Z.float_of_big_int Big_int_Z.zero_big_int))),
    (Bas_mat (rTC (Big_int_Z.float_of_big_int Big_int_Z.zero_big_int))),
    (Bas_mat
    (com_iexp
      (rdiv _UU03b8_
        (Big_int_Z.float_of_big_int (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int))))))

(** val mat_rot :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
    RbaseSymbolsImpl.coq_R -> matrix **)

let mat_rot _UU03b8_ _UU03c6_ l =
  mat_mul (Stdlib.Int.succ 0)
    (mat_mul (Stdlib.Int.succ 0) (mat_rot_z _UU03c6_) (mat_rot_y _UU03b8_))
    (mat_rot_z l)

(** val mat_single : int -> int -> matrix -> matrix **)

let rec mat_single n t0 u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat_eye 0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      tensor_product (Stdlib.Int.succ 0) n' u (mat_eye n'))
      (fun t' ->
      tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
        (mat_single n' t' u))
      t0)
    n

(** val mat_proj0_base : matrix **)

let mat_proj0_base =
  Rec_mat (0, (Bas_mat (nTC (Stdlib.Int.succ 0))), (Bas_mat (nTC 0)),
    (Bas_mat (nTC 0)), (Bas_mat (nTC 0)))

(** val mat_proj1_base : matrix **)

let mat_proj1_base =
  Rec_mat (0, (Bas_mat (nTC 0)), (Bas_mat (nTC 0)), (Bas_mat (nTC 0)),
    (Bas_mat (nTC (Stdlib.Int.succ 0))))

(** val mat_proj0 : int -> int -> matrix **)

let rec mat_proj0 n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Bas_mat (nTC (Stdlib.Int.succ 0)))
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      tensor_product (Stdlib.Int.succ 0) n' mat_proj0_base (mat_eye n'))
      (fun p' ->
      tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
        (mat_proj0 n' p'))
      p)
    n

(** val mat_proj1 : int -> int -> matrix **)

let rec mat_proj1 n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Bas_mat (nTC 0))
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      tensor_product (Stdlib.Int.succ 0) n' mat_proj1_base (mat_eye n'))
      (fun p' ->
      tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
        (mat_proj1 n' p'))
      p)
    n

(** val mat_swap2 : matrix **)

let mat_swap2 =
  Rec_mat ((Stdlib.Int.succ 0), (Rec_mat (0, (Bas_mat
    (nTC (Stdlib.Int.succ 0))), (Bas_mat (nTC 0)), (Bas_mat (nTC 0)),
    (Bas_mat (nTC 0)))), (Rec_mat (0, (Bas_mat (nTC 0)), (Bas_mat (nTC 0)),
    (Bas_mat (nTC (Stdlib.Int.succ 0))), (Bas_mat (nTC 0)))), (Rec_mat (0,
    (Bas_mat (nTC 0)), (Bas_mat (nTC (Stdlib.Int.succ 0))), (Bas_mat
    (nTC 0)), (Bas_mat (nTC 0)))), (Rec_mat (0, (Bas_mat (nTC 0)), (Bas_mat
    (nTC 0)), (Bas_mat (nTC 0)), (Bas_mat (nTC (Stdlib.Int.succ 0))))))

(** val mat_swap_1n_suppl : int -> matrix **)

let rec mat_swap_1n_suppl n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat_swap2)
    (fun n0 ->
    mat_mul
      ((+) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (let rec add0 n1 m =
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> m)
             (fun p -> Stdlib.Int.succ (add0 p m))
             n1
         in add0 0 n0)))
      (mat_mul
        ((+) (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
          (let rec add0 n1 m =
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> m)
               (fun p -> Stdlib.Int.succ (add0 p m))
               n1
           in add0 0 n0)))
        (tensor_product (Stdlib.Int.succ (Stdlib.Int.succ 0))
          (Stdlib.Int.succ
          (let rec add0 n1 m =
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> m)
               (fun p -> Stdlib.Int.succ (add0 p m))
               n1
           in add0 0 n0))
          mat_swap2
          (mat_eye (Stdlib.Int.succ
            (let rec add0 n1 m =
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> m)
                 (fun p -> Stdlib.Int.succ (add0 p m))
                 n1
             in add0 0 n0))))
        (tensor_product (Stdlib.Int.succ 0)
          ((+) (Stdlib.Int.succ (Stdlib.Int.succ 0)) n0)
          (mat_eye (Stdlib.Int.succ 0)) (mat_swap_1n_suppl n0)))
      (tensor_product (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
        (let rec add0 n1 m =
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> m)
             (fun p -> Stdlib.Int.succ (add0 p m))
             n1
         in add0 0 n0))
        mat_swap2
        (mat_eye (Stdlib.Int.succ
          (let rec add0 n1 m =
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> m)
               (fun p -> Stdlib.Int.succ (add0 p m))
               n1
           in add0 0 n0)))))
    n

(** val mat_swap_1n : int -> matrix **)

let mat_swap_1n n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat_eye 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> mat_eye (Stdlib.Int.succ 0))
      (fun n1 -> mat_swap_1n_suppl n1)
      n0)
    n

(** val mat_swap : int -> int -> int -> matrix **)

let mat_swap n q1 q2 =
  let s = (<) q1 n in
  if s
  then let s0 = (<) q2 n in
       if s0
       then let s1 = lt_eq_lt_dec q1 q2 in
            (match s1 with
             | Some s2 ->
               if s2
               then tensor_product
                      ((+) q1 ((+) (sub q2 q1) (Stdlib.Int.succ 0)))
                      (sub (sub n q2) (Stdlib.Int.succ 0))
                      (tensor_product q1
                        ((+) (sub q2 q1) (Stdlib.Int.succ 0)) (mat_eye q1)
                        (mat_swap_1n ((+) (sub q2 q1) (Stdlib.Int.succ 0))))
                      (mat_eye (sub (sub n q2) (Stdlib.Int.succ 0)))
               else mat_eye n
             | None ->
               tensor_product ((+) q2 ((+) (sub q1 q2) (Stdlib.Int.succ 0)))
                 (sub (sub n q1) (Stdlib.Int.succ 0))
                 (tensor_product q2 ((+) (sub q1 q2) (Stdlib.Int.succ 0))
                   (mat_eye q2)
                   (mat_swap_1n ((+) (sub q1 q2) (Stdlib.Int.succ 0))))
                 (mat_eye (sub (sub n q1) (Stdlib.Int.succ 0))))
       else mat_eye n
  else mat_eye n

(** val swap_qbit : int -> int -> int -> int **)

let swap_qbit qbit1 qbit2 tq =
  if (=) tq qbit1 then qbit2 else if (=) tq qbit2 then qbit1 else tq

(** val mat_ctrl_single : int -> int -> int -> matrix -> matrix **)

let rec mat_ctrl_single n c t0 u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat_eye 0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> mat_eye (Stdlib.Int.succ n'))
        (fun t' ->
        mat_add ((+) (Stdlib.Int.succ 0) n')
          (tensor_product (Stdlib.Int.succ 0) n' mat_proj0_base (mat_eye n'))
          (tensor_product (Stdlib.Int.succ 0) n' mat_proj1_base
            (mat_single n' t' u)))
        t0)
      (fun c' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        mat_add ((+) (Stdlib.Int.succ 0) n')
          (tensor_product (Stdlib.Int.succ 0) n'
            (mat_eye (Stdlib.Int.succ 0)) (mat_proj0 n' c'))
          (tensor_product (Stdlib.Int.succ 0) n' u (mat_proj1 n' c')))
        (fun t' ->
        tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
          (mat_ctrl_single n' c' t' u))
        t0)
      c)
    n

(** val mat_not2 : matrix **)

let mat_not2 =
  Rec_mat (0, (Bas_mat (nTC 0)), (Bas_mat (nTC (Stdlib.Int.succ 0))),
    (Bas_mat (nTC (Stdlib.Int.succ 0))), (Bas_mat (nTC 0)))

(** val mat_cnot : int -> int -> int -> matrix **)

let mat_cnot n qc qt =
  mat_ctrl_single n qc qt mat_not2

(** val den_init : int -> matrix **)

let rec den_init n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat_eye 0)
    (fun n0 -> Rec_mat (n0, (den_init n0), (mat_0 n0), (mat_0 n0),
    (mat_0 n0)))
    n

(** val den_uop : int -> matrix -> matrix -> matrix **)

let den_uop n uop den =
  mat_mul n (mat_mul n uop den) (mat_conjtrans n uop)

(** val den_prob : int -> matrix -> matrix -> Complex.t **)

let den_prob n proj den =
  mat_trace n (mat_mul n den proj)

(** val den_prob_0 : int -> int -> matrix -> Complex.t **)

let den_prob_0 n t0 den =
  den_prob n (mat_proj0 n t0) den

(** val den_prob_1 : int -> int -> matrix -> Complex.t **)

let den_prob_1 n t0 den =
  den_prob n (mat_proj1 n t0) den

(** val den_measure : int -> matrix -> matrix -> matrix **)

let den_measure n proj den =
  mat_scale n (Complex.inv (den_prob n proj den))
    (mat_mul n (mat_mul n proj den) proj)

(** val den_measure_0 : int -> int -> matrix -> matrix **)

let den_measure_0 n t0 den =
  den_measure n (mat_proj0 n t0) den

(** val den_measure_1 : int -> int -> matrix -> matrix **)

let den_measure_1 n t0 den =
  den_measure n (mat_proj1 n t0) den

(** val den_reset : int -> int -> matrix -> matrix **)

let den_reset n t0 den =
  mat_add n (mat_mul n (mat_mul n (mat_proj0 n t0) den) (mat_proj0 n t0))
    (den_uop n
      (mat_single n t0
        (mat_rot (4. *. Stdlib.atan 1.)
          (Big_int_Z.float_of_big_int Big_int_Z.zero_big_int)
          (4. *. Stdlib.atan 1.)))
      (mat_mul n (mat_mul n (mat_proj1 n t0) den) (mat_proj1 n t0)))

type angle =
| PiAngle of q
| RealAngle of RbaseSymbolsImpl.coq_R

(** val angle_to_R : angle -> RbaseSymbolsImpl.coq_R **)

let angle_to_R = function
| PiAngle q0 -> RbaseSymbolsImpl.coq_Rmult (q2R q0) (4. *. Stdlib.atan 1.)
| RealAngle r -> r

(** val q_is_even_integer : q -> bool **)

let q_is_even_integer q0 =
  let q' = qred q0 in
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun _ -> false)
     (fun _ -> false)
     (fun _ -> Z.even q'.qnum)
     q'.qden)

(** val q_eqb_mod_2 : q -> q -> bool **)

let q_eqb_mod_2 x y =
  q_is_even_integer (qminus x y)

(** val q_eqb_exact : q -> q -> bool **)

let q_eqb_exact x y =
  (&&) (Z.eqb x.qnum y.qnum) (Coq_Pos.eqb x.qden y.qden)

(** val angle_eqb : angle -> angle -> bool **)

let angle_eqb x y =
  match x with
  | PiAngle qx ->
    (match y with
     | PiAngle qy -> q_eqb_exact qx qy
     | RealAngle _ -> false)
  | RealAngle _ -> false

(** val angle_eqb_mod_2 : angle -> angle -> bool **)

let angle_eqb_mod_2 x y =
  match x with
  | PiAngle qx ->
    (match y with
     | PiAngle qy -> q_eqb_mod_2 qx qy
     | RealAngle _ -> false)
  | RealAngle _ -> false

(** val a0 : angle **)

let a0 =
  PiAngle { qnum = Big_int_Z.zero_big_int; qden = Big_int_Z.unit_big_int }

(** val aPI : angle **)

let aPI =
  PiAngle { qnum = Big_int_Z.unit_big_int; qden = Big_int_Z.unit_big_int }

(** val aPI2 : angle **)

let aPI2 =
  PiAngle { qnum = Big_int_Z.unit_big_int; qden =
    (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) }

(** val aNPI2 : angle **)

let aNPI2 =
  PiAngle { qnum = (Big_int_Z.minus_big_int Big_int_Z.unit_big_int); qden =
    (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) }

(** val aPI4 : angle **)

let aPI4 =
  PiAngle { qnum = Big_int_Z.unit_big_int; qden =
    (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
    Big_int_Z.unit_big_int)) }

(** val aNPI4 : angle **)

let aNPI4 =
  PiAngle { qnum = (Big_int_Z.minus_big_int Big_int_Z.unit_big_int); qden =
    (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
    Big_int_Z.unit_big_int)) }

type instruction =
| NopInstr
| RotateInstr of angle * angle * angle * int
| CnotInstr of int * int
| SwapInstr of int * int
| MeasureInstr of int * int
| SeqInstr of instruction list
| IfInstr of int * bool * instruction
| ResetInstr of int

type cState = Big_int_Z.big_int

(** val cState_init_suppl : int -> Big_int_Z.big_int **)

let rec cState_init_suppl n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Big_int_Z.unit_big_int)
    (fun n' -> Big_int_Z.mult_int_big_int 2 (cState_init_suppl n'))
    n

(** val cState_init : int -> cState **)

let cState_init =
  cState_init_suppl

(** val cState_read : int -> cState -> bool **)

let rec cState_read idx cstate =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun _ -> true)
      (fun _ -> false)
      (fun _ -> false)
      cstate)
    (fun idx' ->
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun c -> cState_read idx' c)
      (fun c -> cState_read idx' c)
      (fun _ -> false)
      cstate)
    idx

(** val cState_branch : int -> cState -> cState * cState **)

let rec cState_branch idx cstate =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun c -> ((Big_int_Z.mult_int_big_int 2 c),
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      c)))
      (fun c -> ((Big_int_Z.mult_int_big_int 2 c),
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      c)))
      (fun _ -> ((Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int),
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))
      cstate)
    (fun idx' ->
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun c ->
      let (c0, c1) = cState_branch idx' c in
      (((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      c0),
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) c1)))
      (fun c ->
      let (c0, c1) = cState_branch idx' c in
      ((Big_int_Z.mult_int_big_int 2 c0), (Big_int_Z.mult_int_big_int 2 c1)))
      (fun _ ->
      let (c0, c1) = cState_branch idx' Big_int_Z.unit_big_int in
      ((Big_int_Z.mult_int_big_int 2 c0), (Big_int_Z.mult_int_big_int 2 c1)))
      cstate)
    idx

type branch = { b_qstate : matrix; b_prob : RbaseSymbolsImpl.coq_R }

(** val branch_init : int -> branch **)

let branch_init nq =
  { b_qstate = (den_init nq); b_prob =
    (Big_int_Z.float_of_big_int Big_int_Z.unit_big_int) }

(** val branch_merge : int -> branch -> branch -> branch **)

let branch_merge nq b0 b1 =
  { b_qstate =
    (mat_add nq
      (mat_scale nq
        (com_div (rTC b0.b_prob)
          (Complex.add (rTC b0.b_prob) (rTC b1.b_prob)))
        b0.b_qstate)
      (mat_scale nq
        (com_div (rTC b1.b_prob)
          (Complex.add (rTC b0.b_prob) (rTC b1.b_prob)))
        b1.b_qstate));
    b_prob = (RbaseSymbolsImpl.coq_Rplus b0.b_prob b1.b_prob) }

type programState = branch PositiveMap.t

(** val programState_init : int -> int -> programState **)

let programState_init nq nc =
  PositiveMap.add (cState_init nc) (branch_init nq) PositiveMap.empty

(** val merge_step :
    int -> Big_int_Z.big_int -> branch -> branch PositiveMap.t -> branch
    PositiveMap.t **)

let merge_step nq cstate branch0 acc =
  match PositiveMap.find cstate acc with
  | Some branch' ->
    PositiveMap.add cstate (branch_merge nq branch0 branch') acc
  | None -> PositiveMap.add cstate branch0 acc

(** val programState_merge :
    int -> programState -> programState -> programState **)

let programState_merge nq ps0 ps1 =
  PositiveMap.fold (merge_step nq) ps0 ps1

(** val fold_step :
    int -> (PositiveMap.key -> branch -> programState) -> PositiveMap.key ->
    branch -> programState -> programState **)

let fold_step nq f k b acc =
  programState_merge nq acc (f k b)

(** val execute_rotate_instr_branch :
    int -> angle -> angle -> angle -> int -> branch -> branch **)

let execute_rotate_instr_branch nq theta phi lambda target branch0 =
  { b_qstate =
    (den_uop nq
      (mat_single nq target
        (mat_rot (angle_to_R theta) (angle_to_R phi) (angle_to_R lambda)))
      branch0.b_qstate);
    b_prob = branch0.b_prob }

(** val execute_rotate_instr :
    int -> angle -> angle -> angle -> int -> programState -> programState **)

let execute_rotate_instr nq theta phi lambda target ps =
  PositiveMap.map (execute_rotate_instr_branch nq theta phi lambda target) ps

(** val execute_cnot_instr_branch : int -> int -> int -> branch -> branch **)

let execute_cnot_instr_branch nq control target branch0 =
  { b_qstate = (den_uop nq (mat_cnot nq control target) branch0.b_qstate);
    b_prob = branch0.b_prob }

(** val execute_cnot_instr :
    int -> int -> int -> programState -> programState **)

let execute_cnot_instr nq control target ps =
  PositiveMap.map (execute_cnot_instr_branch nq control target) ps

(** val execute_swap_instr_branch : int -> int -> int -> branch -> branch **)

let execute_swap_instr_branch nq q1 q2 branch0 =
  { b_qstate = (den_uop nq (mat_swap nq q1 q2) branch0.b_qstate); b_prob =
    branch0.b_prob }

(** val execute_swap_instr :
    int -> int -> int -> programState -> programState **)

let execute_swap_instr nq q1 q2 ps =
  PositiveMap.map (execute_swap_instr_branch nq q1 q2) ps

(** val execute_measure_instr_branch :
    int -> int -> int -> cState -> branch -> programState **)

let execute_measure_instr_branch nq qbit cbit cstate branch0 =
  let prob0 = (fun x -> x.re) (den_prob_0 nq qbit branch0.b_qstate) in
  let prob1 = (fun x -> x.re) (den_prob_1 nq qbit branch0.b_qstate) in
  let (cstate0, cstate1) = cState_branch cbit cstate in
  if rgt_dec prob0 (Big_int_Z.float_of_big_int Big_int_Z.zero_big_int)
  then if rgt_dec prob1 (Big_int_Z.float_of_big_int Big_int_Z.zero_big_int)
       then PositiveMap.add cstate0 { b_qstate =
              (den_measure_0 nq qbit branch0.b_qstate); b_prob =
              (RbaseSymbolsImpl.coq_Rmult branch0.b_prob prob0) }
              (PositiveMap.add cstate1 { b_qstate =
                (den_measure_1 nq qbit branch0.b_qstate); b_prob =
                (RbaseSymbolsImpl.coq_Rmult branch0.b_prob prob1) }
                PositiveMap.empty)
       else PositiveMap.add cstate0 { b_qstate =
              (den_measure_0 nq qbit branch0.b_qstate); b_prob =
              (RbaseSymbolsImpl.coq_Rmult branch0.b_prob prob0) }
              PositiveMap.empty
  else if rgt_dec prob1 (Big_int_Z.float_of_big_int Big_int_Z.zero_big_int)
       then PositiveMap.add cstate1 { b_qstate =
              (den_measure_1 nq qbit branch0.b_qstate); b_prob =
              (RbaseSymbolsImpl.coq_Rmult branch0.b_prob prob1) }
              PositiveMap.empty
       else PositiveMap.empty

(** val execute_measure_instr :
    int -> int -> int -> programState -> programState **)

let execute_measure_instr nq qbit cbit ps =
  PositiveMap.fold (fold_step nq (execute_measure_instr_branch nq qbit cbit))
    ps PositiveMap.empty

(** val execute_reset_instr_branch : int -> int -> branch -> branch **)

let execute_reset_instr_branch nq target branch0 =
  { b_qstate = (den_reset nq target branch0.b_qstate); b_prob =
    branch0.b_prob }

(** val execute_reset_instr : int -> int -> programState -> programState **)

let execute_reset_instr nq target ps =
  PositiveMap.map (execute_reset_instr_branch nq target) ps

(** val execute_suppl : int -> instruction -> programState -> programState **)

let rec execute_suppl nq instr ps =
  match instr with
  | NopInstr -> ps
  | RotateInstr (theta, phi, lambda, target) ->
    execute_rotate_instr nq theta phi lambda target ps
  | CnotInstr (control, target) -> execute_cnot_instr nq control target ps
  | SwapInstr (q1, q2) -> execute_swap_instr nq q1 q2 ps
  | MeasureInstr (qbit, cbit) -> execute_measure_instr nq qbit cbit ps
  | SeqInstr il ->
    fold_left (fun ps' instr0 -> execute_suppl nq instr0 ps') il ps
  | IfInstr (cbit, cond, subinstr) ->
    PositiveMap.fold
      (fold_step nq (fun k b ->
        let ps_single = PositiveMap.add k b PositiveMap.empty in
        if eqb (cState_read cbit k) cond
        then execute_suppl nq subinstr ps_single
        else ps_single))
      ps PositiveMap.empty
  | ResetInstr target -> execute_reset_instr nq target ps

(** val execute : int -> int -> instruction -> programState **)

let execute nq nc instr =
  execute_suppl nq instr (programState_init nq nc)

(** val execute_and_calculate_prob :
    int -> int -> instruction -> (PositiveMap.key * RbaseSymbolsImpl.coq_R)
    list **)

let execute_and_calculate_prob nq nc instr =
  PositiveMap.elements
    (PositiveMap.map (fun b -> b.b_prob) (execute nq nc instr))

(** val qasm_seq : instruction -> instruction -> instruction **)

let qasm_seq i j =
  match i with
  | SeqInstr is ->
    (match j with
     | SeqInstr js -> SeqInstr (app is js)
     | _ -> SeqInstr (app is (j :: [])))
  | _ ->
    (match j with
     | SeqInstr js -> SeqInstr (i :: js)
     | _ -> SeqInstr (i :: (j :: [])))

(** val change_qbit_instr : (int -> int) -> instruction -> instruction **)

let rec change_qbit_instr chan_fn = function
| NopInstr -> NopInstr
| RotateInstr (phi, theta, lambda, qbit) ->
  RotateInstr (phi, theta, lambda, (chan_fn qbit))
| CnotInstr (qbit1, qbit2) -> CnotInstr ((chan_fn qbit1), (chan_fn qbit2))
| SwapInstr (qbit1, qbit2) -> SwapInstr ((chan_fn qbit1), (chan_fn qbit2))
| MeasureInstr (qbit, cbit) -> MeasureInstr ((chan_fn qbit), cbit)
| SeqInstr lst -> SeqInstr (map (change_qbit_instr chan_fn) lst)
| IfInstr (cbit, cond, instr0) ->
  IfInstr (cbit, cond, (change_qbit_instr chan_fn instr0))
| ResetInstr qbit -> ResetInstr (chan_fn qbit)

(** val swap_qbit_instr : int -> int -> instruction -> instruction **)

let swap_qbit_instr qbit1 qbit2 =
  change_qbit_instr (swap_qbit qbit1 qbit2)

(** val flatten_core : instruction -> instruction **)

let rec flatten_core instr = match instr with
| SeqInstr instrs ->
  fold_right (fun instr0 acc -> qasm_seq (flatten_core instr0) acc) (SeqInstr
    []) instrs
| IfInstr (c, b, body) -> IfInstr (c, b, (flatten_core body))
| _ -> instr

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> Big_int_Z.big_int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = Big_int_Z.big_int

  (** val _0 : Big_int_Z.big_int **)

  let _0 =
    Big_int_Z.zero_big_int

  (** val _1 : Big_int_Z.big_int **)

  let _1 =
    Big_int_Z.unit_big_int

  (** val _2 : Big_int_Z.big_int **)

  let _2 =
    (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)

  (** val _3 : Big_int_Z.big_int **)

  let _3 =
    ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add =
    Z.add

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp =
    Z.opp

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub =
    Z.sub

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul =
    Z.mul

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let max =
    Z.max

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> Big_int_Z.big_int **)

  let i2z n =
    n
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> Stdlib.Int.succ ((+) (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) -> (x, e0) :: (app (elements t0) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    Raw.add

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove =
    Raw.remove

  (** val mem : key -> 'a1 t -> bool **)

  let mem =
    Raw.mem

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find =
    Raw.find

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    Raw.map

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi =
    Raw.mapi

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 =
    Raw.map2

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements =
    Raw.elements

  (** val cardinal : 'a1 t -> int **)

  let cardinal =
    Raw.cardinal

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold =
    Raw.fold

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal =
    Raw.equal
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module NatMap = Make(Nat_as_OT)

(** val instruction_eqb : instruction -> instruction -> bool **)

let rec instruction_eqb instr1 instr2 =
  match instr1 with
  | NopInstr -> (match instr2 with
                 | NopInstr -> true
                 | _ -> false)
  | RotateInstr (theta1, phi1, lambda1, qbit1) ->
    (match instr2 with
     | RotateInstr (theta2, phi2, lambda2, qbit2) ->
       (&&)
         ((&&) ((&&) (angle_eqb theta1 theta2) (angle_eqb phi1 phi2))
           (angle_eqb lambda1 lambda2))
         ((=) qbit1 qbit2)
     | _ -> false)
  | CnotInstr (control1, target1) ->
    (match instr2 with
     | CnotInstr (control2, target2) ->
       (&&) ((=) control1 control2) ((=) target1 target2)
     | _ -> false)
  | SwapInstr (qbit1, qbit2) ->
    (match instr2 with
     | SwapInstr (qbit1', qbit2') ->
       (&&) ((=) qbit1 qbit1') ((=) qbit2 qbit2')
     | _ -> false)
  | MeasureInstr (qbit1, cbit1) ->
    (match instr2 with
     | MeasureInstr (qbit2, cbit2) -> (&&) ((=) qbit1 qbit2) ((=) cbit1 cbit2)
     | _ -> false)
  | SeqInstr instrs1 ->
    (match instr2 with
     | SeqInstr instrs2 ->
       let rec list_eqb instrs3 instrs4 =
         match instrs3 with
         | [] -> (match instrs4 with
                  | [] -> true
                  | _ :: _ -> false)
         | instr3 :: rest1 ->
           (match instrs4 with
            | [] -> false
            | instr4 :: rest2 ->
              (&&) (instruction_eqb instr3 instr4) (list_eqb rest1 rest2))
       in list_eqb instrs1 instrs2
     | _ -> false)
  | IfInstr (cbit1, expected1, body1) ->
    (match instr2 with
     | IfInstr (cbit2, expected2, body2) ->
       (&&) ((&&) ((=) cbit1 cbit2) (eqb expected1 expected2))
         (instruction_eqb body1 body2)
     | _ -> false)
  | ResetInstr qbit1 ->
    (match instr2 with
     | ResetInstr qbit2 -> (=) qbit1 qbit2
     | _ -> false)

type patternMap = { pattern_qbit_map : int NatMap.t;
                    pattern_cbit_map : int NatMap.t;
                    pattern_instr_map : instruction NatMap.t }

(** val patternMap_empty : patternMap **)

let patternMap_empty =
  { pattern_qbit_map = NatMap.empty; pattern_cbit_map = NatMap.empty;
    pattern_instr_map = NatMap.empty }

(** val natMap_value_existsb : int -> int NatMap.t -> bool **)

let natMap_value_existsb value map0 =
  NatMap.fold (fun _ found_value acc -> (||) ((=) found_value value) acc)
    map0 false

(** val natMap_bind_distinct :
    int -> int -> int NatMap.t -> int NatMap.t option **)

let natMap_bind_distinct variable value map0 =
  match NatMap.find variable map0 with
  | Some old_value -> if (=) old_value value then Some map0 else None
  | None ->
    if natMap_value_existsb value map0
    then None
    else Some (NatMap.add variable value map0)

(** val patternMap_bind_qbit :
    int -> int -> patternMap -> patternMap option **)

let patternMap_bind_qbit variable value map0 =
  match natMap_bind_distinct variable value map0.pattern_qbit_map with
  | Some qbit_map ->
    Some { pattern_qbit_map = qbit_map; pattern_cbit_map =
      map0.pattern_cbit_map; pattern_instr_map = map0.pattern_instr_map }
  | None -> None

(** val patternMap_bind_cbit :
    int -> int -> patternMap -> patternMap option **)

let patternMap_bind_cbit variable value map0 =
  match natMap_bind_distinct variable value map0.pattern_cbit_map with
  | Some cbit_map ->
    Some { pattern_qbit_map = map0.pattern_qbit_map; pattern_cbit_map =
      cbit_map; pattern_instr_map = map0.pattern_instr_map }
  | None -> None

(** val patternMap_bind_instr :
    int -> instruction -> patternMap -> patternMap option **)

let patternMap_bind_instr variable instr map0 =
  match NatMap.find variable map0.pattern_instr_map with
  | Some old_instr ->
    if instruction_eqb old_instr instr then Some map0 else None
  | None ->
    Some { pattern_qbit_map = map0.pattern_qbit_map; pattern_cbit_map =
      map0.pattern_cbit_map; pattern_instr_map =
      (NatMap.add variable instr map0.pattern_instr_map) }

type natPattern =
| NatExact of int
| NatVar of int

(** val qbitPattern_match :
    natPattern -> int -> patternMap -> patternMap option **)

let qbitPattern_match pattern value map0 =
  match pattern with
  | NatExact expected -> if (=) expected value then Some map0 else None
  | NatVar variable -> patternMap_bind_qbit variable value map0

(** val cbitPattern_match :
    natPattern -> int -> patternMap -> patternMap option **)

let cbitPattern_match pattern value map0 =
  match pattern with
  | NatExact expected -> if (=) expected value then Some map0 else None
  | NatVar variable -> patternMap_bind_cbit variable value map0

(** val qbitPattern_inst : natPattern -> patternMap -> int option **)

let qbitPattern_inst pattern subst =
  match pattern with
  | NatExact value -> Some value
  | NatVar variable -> NatMap.find variable subst.pattern_qbit_map

(** val cbitPattern_inst : natPattern -> patternMap -> int option **)

let cbitPattern_inst pattern subst =
  match pattern with
  | NatExact value -> Some value
  | NatVar variable -> NatMap.find variable subst.pattern_cbit_map

(** val instruction_list_simp : instruction list -> instruction **)

let instruction_list_simp instrs = match instrs with
| [] -> NopInstr
| instr :: l -> (match l with
                 | [] -> instr
                 | _ :: _ -> SeqInstr instrs)

(** val instructionPattern_body_view : instruction -> instruction list **)

let instructionPattern_body_view instr = match instr with
| NopInstr -> []
| SeqInstr instrs -> instrs
| _ -> instr :: []

(** val instructionPattern_canonicalize : instruction -> instruction **)

let rec instructionPattern_canonicalize instr = match instr with
| SeqInstr instrs ->
  SeqInstr
    (fold_right (fun instr0 acc ->
      (instructionPattern_canonicalize instr0) :: acc) [] instrs)
| IfInstr (cbit, expected, body) ->
  (match body with
   | NopInstr -> IfInstr (cbit, expected, NopInstr)
   | SeqInstr instrs ->
     IfInstr (cbit, expected,
       (instruction_list_simp
         (fold_right (fun instr0 acc ->
           (instructionPattern_canonicalize instr0) :: acc) [] instrs)))
   | _ -> IfInstr (cbit, expected, (instructionPattern_canonicalize body)))
| _ -> instr

type instructionPattern =
| PNop
| PRotate of angle * angle * angle * natPattern
| PCnot of natPattern * natPattern
| PSwap of natPattern * natPattern
| PMeasure of natPattern * natPattern
| PReset of natPattern
| PIf of natPattern * bool * instructionPattern list
| PInstrVar of int
| PInstrExact of instruction

(** val instructionPattern_match :
    instructionPattern -> instruction -> patternMap -> patternMap option **)

let rec instructionPattern_match pattern instr map0 =
  match pattern with
  | PNop -> (match instr with
             | NopInstr -> Some map0
             | _ -> None)
  | PRotate (theta', phi', lambda', qbit_pattern) ->
    (match instr with
     | RotateInstr (theta, phi, lambda, qbit) ->
       if (&&) ((&&) (angle_eqb theta theta') (angle_eqb phi phi'))
            (angle_eqb lambda lambda')
       then qbitPattern_match qbit_pattern qbit map0
       else None
     | _ -> None)
  | PCnot (control_pattern, target_pattern) ->
    (match instr with
     | CnotInstr (control, target) ->
       (match qbitPattern_match control_pattern control map0 with
        | Some map' -> qbitPattern_match target_pattern target map'
        | None -> None)
     | _ -> None)
  | PSwap (qbit1_pattern, qbit2_pattern) ->
    (match instr with
     | SwapInstr (qbit1, qbit2) ->
       (match qbitPattern_match qbit1_pattern qbit1 map0 with
        | Some map' -> qbitPattern_match qbit2_pattern qbit2 map'
        | None -> None)
     | _ -> None)
  | PMeasure (qbit_pattern, cbit_pattern) ->
    (match instr with
     | MeasureInstr (qbit, cbit) ->
       (match qbitPattern_match qbit_pattern qbit map0 with
        | Some map' -> cbitPattern_match cbit_pattern cbit map'
        | None -> None)
     | _ -> None)
  | PReset qbit_pattern ->
    (match instr with
     | ResetInstr qbit -> qbitPattern_match qbit_pattern qbit map0
     | _ -> None)
  | PIf (cbit_pattern, expected_pattern, body_patterns) ->
    (match instr with
     | IfInstr (cbit, expected, body) ->
       if eqb expected_pattern expected
       then (match cbitPattern_match cbit_pattern cbit map0 with
             | Some map' ->
               let rec match_exact_list patterns instrs map1 =
                 match patterns with
                 | [] -> (match instrs with
                          | [] -> Some map1
                          | _ :: _ -> None)
                 | pattern0 :: pattern_rest ->
                   (match instrs with
                    | [] -> None
                    | instr0 :: instr_rest ->
                      (match instructionPattern_match pattern0 instr0 map1 with
                       | Some map'0 ->
                         match_exact_list pattern_rest instr_rest map'0
                       | None -> None))
               in match_exact_list body_patterns
                    (instructionPattern_body_view body) map'
             | None -> None)
       else None
     | _ -> None)
  | PInstrVar variable ->
    patternMap_bind_instr variable (instructionPattern_canonicalize instr)
      map0
  | PInstrExact expected_instr ->
    if instruction_eqb expected_instr (instructionPattern_canonicalize instr)
    then Some map0
    else None

(** val instructionPattern_match_list :
    instructionPattern list -> instruction list -> patternMap -> patternMap
    option **)

let rec instructionPattern_match_list patterns instrs map0 =
  match patterns with
  | [] -> Some map0
  | pattern :: pattern_rest ->
    (match instrs with
     | [] -> None
     | instr :: instr_rest ->
       (match instructionPattern_match pattern instr map0 with
        | Some map' ->
          instructionPattern_match_list pattern_rest instr_rest map'
        | None -> None))

(** val instructionPattern_inst :
    instructionPattern -> patternMap -> instruction option **)

let rec instructionPattern_inst pattern map0 =
  match pattern with
  | PNop -> Some NopInstr
  | PRotate (theta, phi, lambda, qbit_pattern) ->
    (match qbitPattern_inst qbit_pattern map0 with
     | Some qbit -> Some (RotateInstr (theta, phi, lambda, qbit))
     | None -> None)
  | PCnot (control_pattern, target_pattern) ->
    (match qbitPattern_inst control_pattern map0 with
     | Some control ->
       (match qbitPattern_inst target_pattern map0 with
        | Some target -> Some (CnotInstr (control, target))
        | None -> None)
     | None -> None)
  | PSwap (qbit1_pattern, qbit2_pattern) ->
    (match qbitPattern_inst qbit1_pattern map0 with
     | Some qbit1 ->
       (match qbitPattern_inst qbit2_pattern map0 with
        | Some qbit2 -> Some (SwapInstr (qbit1, qbit2))
        | None -> None)
     | None -> None)
  | PMeasure (qbit_pattern, cbit_pattern) ->
    (match qbitPattern_inst qbit_pattern map0 with
     | Some qbit ->
       (match cbitPattern_inst cbit_pattern map0 with
        | Some cbit -> Some (MeasureInstr (qbit, cbit))
        | None -> None)
     | None -> None)
  | PReset qbit_pattern ->
    (match qbitPattern_inst qbit_pattern map0 with
     | Some qbit -> Some (ResetInstr qbit)
     | None -> None)
  | PIf (cbit_pattern, expected, body_patterns) ->
    (match cbitPattern_inst cbit_pattern map0 with
     | Some cbit ->
       (match fold_right (fun pattern0 instrs ->
                match instructionPattern_inst pattern0 map0 with
                | Some instr ->
                  (match instrs with
                   | Some instrs0 -> Some (instr :: instrs0)
                   | None -> None)
                | None -> None) (Some []) body_patterns with
        | Some body_instrs ->
          Some (IfInstr (cbit, expected, (instruction_list_simp body_instrs)))
        | None -> None)
     | None -> None)
  | PInstrVar variable -> NatMap.find variable map0.pattern_instr_map
  | PInstrExact instr -> Some instr

(** val instructionPattern_inst_list :
    instructionPattern list -> patternMap -> instruction list option **)

let rec instructionPattern_inst_list patterns map0 =
  match patterns with
  | [] -> Some []
  | pattern :: pattern_rest ->
    (match instructionPattern_inst pattern map0 with
     | Some instr ->
       (match instructionPattern_inst_list pattern_rest map0 with
        | Some instrs -> Some (instr :: instrs)
        | None -> None)
     | None -> None)

type rewriteRule = { rule_lhs : instructionPattern list;
                     rule_rhs : instructionPattern list }

(** val natPattern_vars : natPattern -> int list **)

let natPattern_vars = function
| NatExact _ -> []
| NatVar variable -> variable :: []

(** val instructionPattern_qbit_vars : instructionPattern -> int list **)

let rec instructionPattern_qbit_vars = function
| PRotate (_, _, _, qbit) -> natPattern_vars qbit
| PCnot (control, target) ->
  app (natPattern_vars control) (natPattern_vars target)
| PSwap (qbit1, qbit2) -> app (natPattern_vars qbit1) (natPattern_vars qbit2)
| PMeasure (qbit, _) -> natPattern_vars qbit
| PReset qbit -> natPattern_vars qbit
| PIf (_, _, body) -> concat (map instructionPattern_qbit_vars body)
| _ -> []

(** val instructionPattern_cbit_vars : instructionPattern -> int list **)

let rec instructionPattern_cbit_vars = function
| PMeasure (_, cbit) -> natPattern_vars cbit
| PIf (cbit, _, body) ->
  app (natPattern_vars cbit) (concat (map instructionPattern_cbit_vars body))
| _ -> []

(** val instructionPattern_instr_vars : instructionPattern -> int list **)

let rec instructionPattern_instr_vars = function
| PIf (_, _, body) -> concat (map instructionPattern_instr_vars body)
| PInstrVar variable -> variable :: []
| _ -> []

(** val instructionPattern_list_qbit_vars :
    instructionPattern list -> int list **)

let instructionPattern_list_qbit_vars patterns =
  concat (map instructionPattern_qbit_vars patterns)

(** val instructionPattern_list_cbit_vars :
    instructionPattern list -> int list **)

let instructionPattern_list_cbit_vars patterns =
  concat (map instructionPattern_cbit_vars patterns)

(** val instructionPattern_list_instr_vars :
    instructionPattern list -> int list **)

let instructionPattern_list_instr_vars patterns =
  concat (map instructionPattern_instr_vars patterns)

(** val nat_inb : int -> int list -> bool **)

let nat_inb needle haystack =
  existsb ((=) needle) haystack

(** val list_subsetb : int list -> int list -> bool **)

let list_subsetb xs ys =
  forallb (fun x -> nat_inb x ys) xs

(** val rewriteRule_safeb : rewriteRule -> bool **)

let rewriteRule_safeb rule =
  (&&)
    ((&&)
      (list_subsetb (instructionPattern_list_qbit_vars rule.rule_rhs)
        (instructionPattern_list_qbit_vars rule.rule_lhs))
      (list_subsetb (instructionPattern_list_cbit_vars rule.rule_rhs)
        (instructionPattern_list_cbit_vars rule.rule_lhs)))
    (list_subsetb (instructionPattern_list_instr_vars rule.rule_rhs)
      (instructionPattern_list_instr_vars rule.rule_lhs))

type rewriteResult = { rewriteResult_consumed : int;
                       rewriteResult_replacement : instruction list }

(** val rewriteRule_apply :
    rewriteRule -> instruction list -> rewriteResult option **)

let rewriteRule_apply rule instrs =
  if rewriteRule_safeb rule
  then (match instructionPattern_match_list rule.rule_lhs instrs
                patternMap_empty with
        | Some subst ->
          (match instructionPattern_inst_list rule.rule_rhs subst with
           | Some replacement ->
             Some { rewriteResult_consumed = (length rule.rule_lhs);
               rewriteResult_replacement = replacement }
           | None -> None)
        | None -> None)
  else None

(** val rewriteRule_match_at : rewriteRule -> instruction list -> int **)

let rewriteRule_match_at rule instrs =
  match rewriteRule_apply rule instrs with
  | Some _ -> Stdlib.Int.succ 0
  | None -> 0

(** val rewriteRule_match_count_top_list :
    rewriteRule -> instruction list -> int **)

let rec rewriteRule_match_count_top_list rule instrs = match instrs with
| [] -> 0
| _ :: rest ->
  (+) (rewriteRule_match_at rule instrs)
    (rewriteRule_match_count_top_list rule rest)

(** val rewriteRule_match_count_top : rewriteRule -> instruction -> int **)

let rewriteRule_match_count_top rule instr = match instr with
| SeqInstr instrs -> rewriteRule_match_count_top_list rule instrs
| _ -> rewriteRule_match_at rule (instr :: [])

(** val rewriteRule_match_count : rewriteRule -> instruction -> int **)

let rec rewriteRule_match_count rule instr = match instr with
| SeqInstr instrs ->
  let rec count_list xs = match xs with
  | [] -> 0
  | head :: rest ->
    (+)
      ((+) (rewriteRule_match_at rule xs)
        (match head with
         | SeqInstr _ -> rewriteRule_match_count rule head
         | IfInstr (_, _, body) -> rewriteRule_match_count rule body
         | _ -> 0))
      (count_list rest)
  in count_list instrs
| IfInstr (_, _, body) ->
  (+) (rewriteRule_match_at rule (instr :: []))
    (rewriteRule_match_count rule body)
| _ -> rewriteRule_match_at rule (instr :: [])

type rewriteStatus =
| RewriteDone
| RewriteContinue of int

(** val rewriteRule_apply_top_level_list_result :
    rewriteRule -> (instruction -> instruction) -> instruction list -> int ->
    instruction list * rewriteStatus **)

let rec rewriteRule_apply_top_level_list_result rule postprocesses remaining remaining_occurrence =
  match remaining with
  | [] -> ([], (RewriteContinue remaining_occurrence))
  | current :: rest ->
    (match rewriteRule_apply rule remaining with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((app result.rewriteResult_replacement
             (map postprocesses
               (skipn result.rewriteResult_consumed remaining))),
          RewriteDone))
          (fun occurrence' ->
          let (rest', status) =
            rewriteRule_apply_top_level_list_result rule postprocesses rest
              occurrence'
          in
          ((current :: rest'), status))
          remaining_occurrence)
     | None ->
       let (rest', status) =
         rewriteRule_apply_top_level_list_result rule postprocesses rest
           remaining_occurrence
       in
       ((current :: rest'), status))

(** val rewriteRule_apply_top_level_result :
    rewriteRule -> (instruction -> instruction) -> instruction -> int ->
    instruction * rewriteStatus **)

let rewriteRule_apply_top_level_result rule postprocesses instr occurrence =
  match instr with
  | NopInstr ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))
  | RotateInstr (_, _, _, _) ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))
  | CnotInstr (_, _) ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))
  | SwapInstr (_, _) ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))
  | MeasureInstr (_, _) ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))
  | SeqInstr instrs ->
    let (instrs', status) =
      rewriteRule_apply_top_level_list_result rule postprocesses instrs
        occurrence
    in
    ((SeqInstr instrs'), status)
  | IfInstr (_, _, _) ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))
  | ResetInstr _ ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (map postprocesses
                 (skipn result.rewriteResult_consumed (instr :: []))))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))

(** val rewriteRule_apply_deep_list_result :
    rewriteRule -> (instruction -> int -> instruction * rewriteStatus) ->
    instruction list -> int -> instruction list * rewriteStatus **)

let rec rewriteRule_apply_deep_list_result rule rewrite_instr remaining remaining_occurrence =
  match remaining with
  | [] -> ([], (RewriteContinue remaining_occurrence))
  | current :: rest ->
    (match rewriteRule_apply rule remaining with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((app result.rewriteResult_replacement
             (skipn result.rewriteResult_consumed remaining)),
          RewriteDone))
          (fun occurrence' ->
          match current with
          | SeqInstr _ ->
            let (current', current_status) = rewrite_instr current occurrence'
            in
            (match current_status with
             | RewriteDone -> ((current' :: rest), RewriteDone)
             | RewriteContinue occurrence'' ->
               let (rest', rest_status) =
                 rewriteRule_apply_deep_list_result rule rewrite_instr rest
                   occurrence''
               in
               ((current' :: rest'), rest_status))
          | IfInstr (cbit, expected, body) ->
            let (current', current_status) =
              rewrite_instr (IfInstr (cbit, expected, body)) (Stdlib.Int.succ
                occurrence')
            in
            (match current_status with
             | RewriteDone -> ((current' :: rest), RewriteDone)
             | RewriteContinue occurrence'' ->
               let (rest', rest_status) =
                 rewriteRule_apply_deep_list_result rule rewrite_instr rest
                   occurrence''
               in
               ((current' :: rest'), rest_status))
          | _ ->
            let (rest', status) =
              rewriteRule_apply_deep_list_result rule rewrite_instr rest
                occurrence'
            in
            ((current :: rest'), status))
          remaining_occurrence)
     | None ->
       let (current', current_status) =
         rewrite_instr current remaining_occurrence
       in
       (match current_status with
        | RewriteDone -> ((current' :: rest), RewriteDone)
        | RewriteContinue occurrence' ->
          let (rest', rest_status) =
            rewriteRule_apply_deep_list_result rule rewrite_instr rest
              occurrence'
          in
          ((current' :: rest'), rest_status)))

(** val rewriteRule_apply_deep_result :
    rewriteRule -> instruction -> int -> instruction * rewriteStatus **)

let rec rewriteRule_apply_deep_result rule instr occurrence =
  match instr with
  | SeqInstr instrs ->
    let (instrs', status) =
      rewriteRule_apply_deep_list_result rule
        (rewriteRule_apply_deep_result rule) instrs occurrence
    in
    ((SeqInstr instrs'), status)
  | IfInstr (cbit, expected, body) ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (skipn result.rewriteResult_consumed (instr :: [])))),
          RewriteDone))
          (fun occurrence' ->
          let (body', status) =
            rewriteRule_apply_deep_result rule body occurrence'
          in
          ((IfInstr (cbit, expected, body')), status))
          occurrence)
     | None ->
       let (body', status) =
         rewriteRule_apply_deep_result rule body occurrence
       in
       ((IfInstr (cbit, expected, body')), status))
  | _ ->
    (match rewriteRule_apply rule (instr :: []) with
     | Some result ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          ((instruction_list_simp
             (app result.rewriteResult_replacement
               (skipn result.rewriteResult_consumed (instr :: [])))),
          RewriteDone))
          (fun occurrence' -> (instr, (RewriteContinue
          occurrence')))
          occurrence)
     | None -> (instr, (RewriteContinue occurrence)))

(** val instruction_qbits_validb : int -> instruction -> bool **)

let rec instruction_qbits_validb nq = function
| NopInstr -> true
| RotateInstr (_, _, _, qbit) -> Nat.ltb qbit nq
| CnotInstr (control, target) -> (&&) (Nat.ltb control nq) (Nat.ltb target nq)
| SwapInstr (qbit1, qbit2) -> (&&) (Nat.ltb qbit1 nq) (Nat.ltb qbit2 nq)
| MeasureInstr (qbit, _) -> Nat.ltb qbit nq
| SeqInstr instrs ->
  let rec list_validb = function
  | [] -> true
  | instr0 :: rest ->
    (&&) (instruction_qbits_validb nq instr0) (list_validb rest)
  in list_validb instrs
| IfInstr (_, _, body) -> instruction_qbits_validb nq body
| ResetInstr qbit -> Nat.ltb qbit nq

type transformParameter =
| Param_None
| Param_qbit1 of int
| Param_qbit2 of int * int
| Param_cbit_instr of int * instruction

type transformParamKind =
| ParamKind_None
| ParamKind_qbit1
| ParamKind_qbit2
| ParamKind_cbit_instr

type transformStrategy =
| TransformTopLevel
| TransformDeep

type transformSpec = { transform_name : string;
                       transform_rule : (transformParameter -> rewriteRule
                                        option);
                       transform_postprocess : (transformParameter ->
                                               instruction -> instruction);
                       transform_strategy : transformStrategy;
                       transform_param_kind : transformParamKind }

(** val transformSpec_count :
    transformSpec -> transformParameter -> instruction -> int **)

let transformSpec_count spec param instr =
  match spec.transform_rule param with
  | Some rule ->
    (match spec.transform_strategy with
     | TransformTopLevel -> rewriteRule_match_count_top rule instr
     | TransformDeep -> rewriteRule_match_count rule instr)
  | None -> 0

(** val transformSpec_apply :
    transformSpec -> transformParameter -> instruction -> int -> instruction
    option **)

let transformSpec_apply spec param instr occurrence =
  match spec.transform_rule param with
  | Some rule ->
    let (instr', status) =
      match spec.transform_strategy with
      | TransformTopLevel ->
        rewriteRule_apply_top_level_result rule
          (spec.transform_postprocess param) instr occurrence
      | TransformDeep -> rewriteRule_apply_deep_result rule instr occurrence
    in
    (match status with
     | RewriteDone -> Some instr'
     | RewriteContinue _ -> None)
  | None -> None

(** val pat_I : natPattern -> instructionPattern **)

let pat_I qbit_pattern =
  PRotate (a0, a0, a0, qbit_pattern)

(** val rule_Insert_I : int -> rewriteRule **)

let rule_Insert_I qbit =
  { rule_lhs = []; rule_rhs = ((pat_I (NatExact qbit)) :: []) }

(** val rule_Insert_Swap : int -> int -> rewriteRule **)

let rule_Insert_Swap qbit1 qbit2 =
  { rule_lhs = []; rule_rhs = ((PSwap ((NatExact qbit1), (NatExact
    qbit2))) :: []) }

(** val rule_Insert_Cnot_Cnot : int -> int -> rewriteRule **)

let rule_Insert_Cnot_Cnot qbit1 qbit2 =
  { rule_lhs = []; rule_rhs = ((PCnot ((NatExact qbit1), (NatExact
    qbit2))) :: ((PCnot ((NatExact qbit1), (NatExact qbit2))) :: [])) }

(** val rule_Double_If : bool -> rewriteRule **)

let rule_Double_If cond =
  { rule_lhs = ((PIf ((NatVar 0), cond, ((PInstrVar 0) :: []))) :: []);
    rule_rhs = ((PIf ((NatVar 0), cond, ((PIf ((NatVar 0), cond, ((PInstrVar
    0) :: []))) :: []))) :: []) }

(** val rule_Double_If_True : rewriteRule **)

let rule_Double_If_True =
  rule_Double_If true

(** val rule_Double_If_False : rewriteRule **)

let rule_Double_If_False =
  rule_Double_If false

(** val rule_Insert_Contradictory_If :
    bool -> int -> instruction -> rewriteRule **)

let rule_Insert_Contradictory_If outer_cond cbit instr =
  { rule_lhs = []; rule_rhs = ((PIf ((NatExact cbit), outer_cond, ((PIf
    ((NatExact cbit), (negb outer_cond), ((PInstrExact
    instr) :: []))) :: []))) :: []) }

(** val rule_Double_Reset : rewriteRule **)

let rule_Double_Reset =
  { rule_lhs = ((PReset (NatVar 0)) :: []); rule_rhs = ((PReset (NatVar
    0)) :: ((PReset (NatVar 0)) :: [])) }

(** val transform_simple_rule :
    rewriteRule -> transformParameter -> rewriteRule option **)

let transform_simple_rule rule = function
| Param_None -> Some rule
| _ -> None

(** val transformSpec_simple_rule : string -> rewriteRule -> transformSpec **)

let transformSpec_simple_rule name rule =
  { transform_name = name; transform_rule = (transform_simple_rule rule);
    transform_postprocess = (fun _ instr -> instr); transform_strategy =
    TransformDeep; transform_param_kind = ParamKind_None }

(** val transformSpec_Insert_I : int -> transformSpec **)

let transformSpec_Insert_I nq =
  { transform_name = "Insert_I"; transform_rule = (fun param ->
    match param with
    | Param_qbit1 qbit ->
      if Nat.ltb qbit nq then Some (rule_Insert_I qbit) else None
    | _ -> None); transform_postprocess = (fun _ instr -> instr);
    transform_strategy = TransformDeep; transform_param_kind =
    ParamKind_qbit1 }

(** val transformSpec_Insert_Swap : int -> transformSpec **)

let transformSpec_Insert_Swap nq =
  { transform_name = "Insert_Swap"; transform_rule = (fun param ->
    match param with
    | Param_qbit2 (qbit1, qbit2) ->
      if (&&) (Nat.ltb qbit1 nq) (Nat.ltb qbit2 nq)
      then Some (rule_Insert_Swap qbit1 qbit2)
      else None
    | _ -> None); transform_postprocess = (fun param instr ->
    match param with
    | Param_qbit2 (qbit1, qbit2) -> swap_qbit_instr qbit1 qbit2 instr
    | _ -> instr); transform_strategy = TransformTopLevel;
    transform_param_kind = ParamKind_qbit2 }

(** val transformSpec_Insert_Cnot_Cnot : int -> transformSpec **)

let transformSpec_Insert_Cnot_Cnot nq =
  { transform_name = "Insert_Cnot_Cnot"; transform_rule = (fun param ->
    match param with
    | Param_qbit2 (qbit1, qbit2) ->
      if (&&) (Nat.ltb qbit1 nq) (Nat.ltb qbit2 nq)
      then Some (rule_Insert_Cnot_Cnot qbit1 qbit2)
      else None
    | _ -> None); transform_postprocess = (fun _ instr -> instr);
    transform_strategy = TransformDeep; transform_param_kind =
    ParamKind_qbit2 }

(** val transformSpec_Insert_Contradictory_If :
    int -> string -> bool -> transformSpec **)

let transformSpec_Insert_Contradictory_If nq name outer_cond =
  { transform_name = name; transform_rule = (fun param ->
    match param with
    | Param_cbit_instr (cbit, instr) ->
      if instruction_qbits_validb nq instr
      then Some (rule_Insert_Contradictory_If outer_cond cbit instr)
      else None
    | _ -> None); transform_postprocess = (fun _ instr -> instr);
    transform_strategy = TransformDeep; transform_param_kind =
    ParamKind_cbit_instr }

(** val transformSpec_Insert_Contradictory_If_False : int -> transformSpec **)

let transformSpec_Insert_Contradictory_If_False nq =
  transformSpec_Insert_Contradictory_If nq "Insert_If_FT" false

(** val transformSpec_Insert_Contradictory_If_True : int -> transformSpec **)

let transformSpec_Insert_Contradictory_If_True nq =
  transformSpec_Insert_Contradictory_If nq "Insert_If_TF" true

(** val transform_spec_list : int -> transformSpec list **)

let transform_spec_list nq =
  (transformSpec_Insert_I nq) :: ((transformSpec_Insert_Swap nq) :: (
    (transformSpec_Insert_Cnot_Cnot nq) :: ((transformSpec_Insert_Contradictory_If_False
                                              nq) :: ((transformSpec_Insert_Contradictory_If_True
                                                        nq) :: ((transformSpec_simple_rule
                                                                  "Double_If_True"
                                                                  rule_Double_If_True) :: (
    (transformSpec_simple_rule "Double_If_False" rule_Double_If_False) :: (
    (transformSpec_simple_rule "Double_Reset" rule_Double_Reset) :: [])))))))

type dOmega = { domega_d0 : Big_int_Z.big_int; domega_d1 : Big_int_Z.big_int;
                domega_d2 : Big_int_Z.big_int; domega_d3 : Big_int_Z.big_int;
                domega_k : int }

(** val domega_make :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int -> int -> dOmega **)

let domega_make d0 d1 d2 d3 k =
  { domega_d0 = d0; domega_d1 = d1; domega_d2 = d2; domega_d3 = d3;
    domega_k = k }

(** val pow2 : int -> Big_int_Z.big_int **)

let rec pow2 k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Big_int_Z.unit_big_int)
    (fun k' ->
    Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) (pow2 k'))
    k

(** val domega_zero : dOmega **)

let domega_zero =
  domega_make Big_int_Z.zero_big_int Big_int_Z.zero_big_int
    Big_int_Z.zero_big_int Big_int_Z.zero_big_int 0

(** val domega_one : dOmega **)

let domega_one =
  domega_make Big_int_Z.unit_big_int Big_int_Z.zero_big_int
    Big_int_Z.zero_big_int Big_int_Z.zero_big_int 0

(** val domega_w : dOmega **)

let domega_w =
  domega_make Big_int_Z.zero_big_int Big_int_Z.unit_big_int
    Big_int_Z.zero_big_int Big_int_Z.zero_big_int 0

(** val domega_w2 : dOmega **)

let domega_w2 =
  domega_make Big_int_Z.zero_big_int Big_int_Z.zero_big_int
    Big_int_Z.unit_big_int Big_int_Z.zero_big_int 0

(** val domega_w3 : dOmega **)

let domega_w3 =
  domega_make Big_int_Z.zero_big_int Big_int_Z.zero_big_int
    Big_int_Z.zero_big_int Big_int_Z.unit_big_int 0

(** val domega_neg : dOmega -> dOmega **)

let domega_neg x =
  domega_make (Z.opp x.domega_d0) (Z.opp x.domega_d1) (Z.opp x.domega_d2)
    (Z.opp x.domega_d3) x.domega_k

(** val domega_minus_one : dOmega **)

let domega_minus_one =
  domega_neg domega_one

(** val domega_minus_i : dOmega **)

let domega_minus_i =
  domega_neg domega_w2

(** val domega_h_scalar : dOmega **)

let domega_h_scalar =
  domega_make Big_int_Z.zero_big_int Big_int_Z.unit_big_int
    Big_int_Z.zero_big_int (Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
    (Stdlib.Int.succ 0)

(** val domega_half_one_plus_i : dOmega **)

let domega_half_one_plus_i =
  domega_make Big_int_Z.unit_big_int Big_int_Z.zero_big_int
    Big_int_Z.unit_big_int Big_int_Z.zero_big_int (Stdlib.Int.succ 0)

(** val domega_half_one_minus_i : dOmega **)

let domega_half_one_minus_i =
  domega_make Big_int_Z.unit_big_int Big_int_Z.zero_big_int
    (Big_int_Z.minus_big_int Big_int_Z.unit_big_int) Big_int_Z.zero_big_int
    (Stdlib.Int.succ 0)

(** val domega_common_k : dOmega -> dOmega -> int **)

let domega_common_k x y =
  Nat.max x.domega_k y.domega_k

(** val domega_align :
    int -> dOmega -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let domega_align target_k x d =
  Z.mul d (pow2 (sub target_k x.domega_k))

(** val domega_add : dOmega -> dOmega -> dOmega **)

let domega_add x y =
  let k = domega_common_k x y in
  domega_make
    (Z.add (domega_align k x x.domega_d0) (domega_align k y y.domega_d0))
    (Z.add (domega_align k x x.domega_d1) (domega_align k y y.domega_d1))
    (Z.add (domega_align k x x.domega_d2) (domega_align k y y.domega_d2))
    (Z.add (domega_align k x x.domega_d3) (domega_align k y y.domega_d3)) k

(** val domega_mul : dOmega -> dOmega -> dOmega **)

let domega_mul x y =
  let a1 = x.domega_d0 in
  let a2 = x.domega_d1 in
  let a3 = x.domega_d2 in
  let a4 = x.domega_d3 in
  let b0 = y.domega_d0 in
  let b1 = y.domega_d1 in
  let b2 = y.domega_d2 in
  let b3 = y.domega_d3 in
  let p0 = Z.mul a1 b0 in
  let p1 = Z.add (Z.mul a1 b1) (Z.mul a2 b0) in
  let p2 = Z.add (Z.add (Z.mul a1 b2) (Z.mul a2 b1)) (Z.mul a3 b0) in
  let p3 =
    Z.add (Z.add (Z.add (Z.mul a1 b3) (Z.mul a2 b2)) (Z.mul a3 b1))
      (Z.mul a4 b0)
  in
  let p4 = Z.add (Z.add (Z.mul a2 b3) (Z.mul a3 b2)) (Z.mul a4 b1) in
  let p5 = Z.add (Z.mul a3 b3) (Z.mul a4 b2) in
  let p6 = Z.mul a4 b3 in
  domega_make (Z.sub p0 p4) (Z.sub p1 p5) (Z.sub p2 p6) p3
    ((+) x.domega_k y.domega_k)

(** val domega_eqb : dOmega -> dOmega -> bool **)

let domega_eqb x y =
  let k = domega_common_k x y in
  (&&)
    ((&&)
      ((&&)
        (Z.eqb (domega_align k x x.domega_d0) (domega_align k y y.domega_d0))
        (Z.eqb (domega_align k x x.domega_d1) (domega_align k y y.domega_d1)))
      (Z.eqb (domega_align k x x.domega_d2) (domega_align k y y.domega_d2)))
    (Z.eqb (domega_align k x x.domega_d3) (domega_align k y y.domega_d3))

(** val domega_pow8 : int -> dOmega **)

let rec domega_pow8 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> domega_one)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> domega_w)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> domega_w2)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> domega_w3)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> domega_neg domega_one)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> domega_neg domega_w)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> domega_neg domega_w2)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> domega_neg domega_w3)
                  (fun n' -> domega_pow8 n')
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    n

(** val domega_phase_list : dOmega list **)

let domega_phase_list =
  (domega_pow8 0) :: ((domega_pow8 (Stdlib.Int.succ 0)) :: ((domega_pow8
                                                              (Stdlib.Int.succ
                                                              (Stdlib.Int.succ
                                                              0))) :: (
    (domega_pow8 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))) :: (
    (domega_pow8 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))) :: ((domega_pow8 (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) :: (
    (domega_pow8 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))) :: (
    (domega_pow8 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))) :: [])))))))

type dOmegaMatrix =
| Domega_bas_mat of dOmega
| Domega_rec_mat of int * dOmegaMatrix * dOmegaMatrix * dOmegaMatrix
   * dOmegaMatrix

(** val domega_matrix_case0 : (dOmega -> 'a1) -> dOmegaMatrix -> 'a1 **)

let domega_matrix_case0 h = function
| Domega_bas_mat a1 -> h a1
| Domega_rec_mat (x, x0, x1, x2, x3) -> Obj.magic __ x x0 x1 x2 x3

(** val domega_matrix_caseS_ :
    int -> dOmegaMatrix -> (dOmegaMatrix -> dOmegaMatrix -> dOmegaMatrix ->
    dOmegaMatrix -> 'a1) -> 'a1 **)

let domega_matrix_caseS_ _ a h =
  match a with
  | Domega_bas_mat x -> Obj.magic __ x __ h
  | Domega_rec_mat (_, a00, a01, a10, a11) -> h a00 a01 a10 a11

(** val domega_matrix_zero : int -> dOmegaMatrix **)

let rec domega_matrix_zero n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Domega_bas_mat domega_zero)
    (fun n' -> Domega_rec_mat (n', (domega_matrix_zero n'),
    (domega_matrix_zero n'), (domega_matrix_zero n'),
    (domega_matrix_zero n')))
    n

(** val domega_matrix_eye : int -> dOmegaMatrix **)

let rec domega_matrix_eye n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Domega_bas_mat domega_one)
    (fun n' -> Domega_rec_mat (n', (domega_matrix_eye n'),
    (domega_matrix_zero n'), (domega_matrix_zero n'),
    (domega_matrix_eye n')))
    n

(** val domega_matrix_map :
    int -> (dOmega -> dOmega) -> dOmegaMatrix -> dOmegaMatrix **)

let rec domega_matrix_map _ f = function
| Domega_bas_mat a -> Domega_bas_mat (f a)
| Domega_rec_mat (n0, a, b, c, d) ->
  Domega_rec_mat (n0, (domega_matrix_map n0 f a), (domega_matrix_map n0 f b),
    (domega_matrix_map n0 f c), (domega_matrix_map n0 f d))

(** val domega_matrix_map2 :
    int -> (dOmega -> dOmega -> dOmega) -> dOmegaMatrix -> dOmegaMatrix ->
    dOmegaMatrix **)

let rec domega_matrix_map2 _ f x y =
  match x with
  | Domega_bas_mat a ->
    domega_matrix_case0 (fun b -> Domega_bas_mat (f a b)) y
  | Domega_rec_mat (n, a, b, c, d) ->
    domega_matrix_caseS_ n y (fun e f' g h -> Domega_rec_mat (n,
      (domega_matrix_map2 n f a e), (domega_matrix_map2 n f b f'),
      (domega_matrix_map2 n f c g), (domega_matrix_map2 n f d h)))

(** val domega_matrix_add :
    int -> dOmegaMatrix -> dOmegaMatrix -> dOmegaMatrix **)

let domega_matrix_add n x y =
  domega_matrix_map2 n domega_add x y

(** val domega_matrix_scale :
    int -> dOmega -> dOmegaMatrix -> dOmegaMatrix **)

let domega_matrix_scale n scalar x =
  domega_matrix_map n (domega_mul scalar) x

(** val domega_matrix_mul :
    int -> dOmegaMatrix -> dOmegaMatrix -> dOmegaMatrix **)

let rec domega_matrix_mul _ x y =
  match x with
  | Domega_bas_mat a ->
    domega_matrix_case0 (fun b -> Domega_bas_mat (domega_mul a b)) y
  | Domega_rec_mat (n, a, b, c, d) ->
    domega_matrix_caseS_ n y (fun e f g h -> Domega_rec_mat (n,
      (domega_matrix_add n (domega_matrix_mul n a e)
        (domega_matrix_mul n b g)),
      (domega_matrix_add n (domega_matrix_mul n a f)
        (domega_matrix_mul n b h)),
      (domega_matrix_add n (domega_matrix_mul n c e)
        (domega_matrix_mul n d g)),
      (domega_matrix_add n (domega_matrix_mul n c f)
        (domega_matrix_mul n d h))))

(** val domega_matrix_eqb : int -> dOmegaMatrix -> dOmegaMatrix -> bool **)

let rec domega_matrix_eqb _ x y =
  match x with
  | Domega_bas_mat a -> domega_matrix_case0 (fun b -> domega_eqb a b) y
  | Domega_rec_mat (n, a, b, c, d) ->
    domega_matrix_caseS_ n y (fun e f g h ->
      (&&)
        ((&&) ((&&) (domega_matrix_eqb n a e) (domega_matrix_eqb n b f))
          (domega_matrix_eqb n c g))
        (domega_matrix_eqb n d h))

(** val domega_matrix_tprod :
    int -> int -> dOmegaMatrix -> dOmegaMatrix -> dOmegaMatrix **)

let rec domega_matrix_tprod _ n x y =
  match x with
  | Domega_bas_mat a -> domega_matrix_scale n a y
  | Domega_rec_mat (n0, a, b, c, d) ->
    Domega_rec_mat (((+) n0 n), (domega_matrix_tprod n0 n a y),
      (domega_matrix_tprod n0 n b y), (domega_matrix_tprod n0 n c y),
      (domega_matrix_tprod n0 n d y))

(** val domega_mat_proj0_base : dOmegaMatrix **)

let domega_mat_proj0_base =
  Domega_rec_mat (0, (Domega_bas_mat domega_one), (Domega_bas_mat
    domega_zero), (Domega_bas_mat domega_zero), (Domega_bas_mat domega_zero))

(** val domega_mat_proj1_base : dOmegaMatrix **)

let domega_mat_proj1_base =
  Domega_rec_mat (0, (Domega_bas_mat domega_zero), (Domega_bas_mat
    domega_zero), (Domega_bas_mat domega_zero), (Domega_bas_mat domega_one))

(** val domega_mat_not2 : dOmegaMatrix **)

let domega_mat_not2 =
  Domega_rec_mat (0, (Domega_bas_mat domega_zero), (Domega_bas_mat
    domega_one), (Domega_bas_mat domega_one), (Domega_bas_mat domega_zero))

(** val domega_matrix_single : int -> int -> dOmegaMatrix -> dOmegaMatrix **)

let rec domega_matrix_single n t0 u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> domega_matrix_eye 0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      domega_matrix_tprod (Stdlib.Int.succ 0) n' u (domega_matrix_eye n'))
      (fun t' ->
      domega_matrix_tprod (Stdlib.Int.succ 0) n'
        (domega_matrix_eye (Stdlib.Int.succ 0)) (domega_matrix_single n' t' u))
      t0)
    n

(** val domega_matrix_proj0 : int -> int -> dOmegaMatrix **)

let domega_matrix_proj0 n t0 =
  domega_matrix_single n t0 domega_mat_proj0_base

(** val domega_matrix_proj1 : int -> int -> dOmegaMatrix **)

let domega_matrix_proj1 n t0 =
  domega_matrix_single n t0 domega_mat_proj1_base

(** val domega_matrix_ctrl_single :
    int -> int -> int -> dOmegaMatrix -> dOmegaMatrix **)

let domega_matrix_ctrl_single n c t0 u =
  if (&&) ((&&) (Nat.ltb c n) (Nat.ltb t0 n)) (negb ((=) c t0))
  then domega_matrix_add n (domega_matrix_proj0 n c)
         (domega_matrix_mul n (domega_matrix_proj1 n c)
           (domega_matrix_single n t0 u))
  else domega_matrix_eye n

(** val domega_matrix_cnot : int -> int -> int -> dOmegaMatrix **)

let domega_matrix_cnot n control target =
  domega_matrix_ctrl_single n control target domega_mat_not2

(** val domega_matrix_swap : int -> int -> int -> dOmegaMatrix **)

let domega_matrix_swap n qbit1 qbit2 =
  domega_matrix_mul n (domega_matrix_cnot n qbit1 qbit2)
    (domega_matrix_mul n (domega_matrix_cnot n qbit2 qbit1)
      (domega_matrix_cnot n qbit1 qbit2))

(** val domega_matrix_eq_up_to_phaseb :
    int -> dOmegaMatrix -> dOmegaMatrix -> bool **)

let domega_matrix_eq_up_to_phaseb n x y =
  existsb (fun phase ->
    domega_matrix_eqb n x (domega_matrix_scale n phase y)) domega_phase_list

type standardGate =
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
| Std_SXdg

type standardPatternGate =
| SPG_Std of standardGate * int
| SPG_Cnot of int * int
| SPG_Swap of int * int

(** val standard_gate_pattern :
    standardGate -> natPattern -> instructionPattern **)

let standard_gate_pattern gate qbit_pattern =
  match gate with
  | Std_I -> PRotate (a0, a0, a0, qbit_pattern)
  | Std_X -> PRotate (aPI, a0, aPI, qbit_pattern)
  | Std_Y -> PRotate (aPI, aPI2, aPI2, qbit_pattern)
  | Std_Z -> PRotate (a0, a0, aPI, qbit_pattern)
  | Std_H -> PRotate (aPI2, a0, aPI, qbit_pattern)
  | Std_S -> PRotate (a0, a0, aPI2, qbit_pattern)
  | Std_Sdg -> PRotate (a0, a0, aNPI2, qbit_pattern)
  | Std_T -> PRotate (a0, a0, aPI4, qbit_pattern)
  | Std_Tdg -> PRotate (a0, a0, aNPI4, qbit_pattern)
  | Std_SX -> PRotate (aPI2, aNPI2, aPI2, qbit_pattern)
  | Std_SXdg -> PRotate (aPI2, aPI2, aNPI2, qbit_pattern)

(** val standard_pattern_gate_to_instruction_pattern :
    standardPatternGate -> instructionPattern **)

let standard_pattern_gate_to_instruction_pattern = function
| SPG_Std (gate0, qbit) -> standard_gate_pattern gate0 (NatVar qbit)
| SPG_Cnot (control, target) -> PCnot ((NatVar control), (NatVar target))
| SPG_Swap (qbit1, qbit2) -> PSwap ((NatVar qbit1), (NatVar qbit2))

(** val standard_pattern_sequence_to_instruction_patterns :
    standardPatternGate list -> instructionPattern list **)

let standard_pattern_sequence_to_instruction_patterns gates =
  map standard_pattern_gate_to_instruction_pattern gates

(** val domega_matrix2 :
    dOmega -> dOmega -> dOmega -> dOmega -> dOmegaMatrix **)

let domega_matrix2 a b c d =
  Domega_rec_mat (0, (Domega_bas_mat a), (Domega_bas_mat b), (Domega_bas_mat
    c), (Domega_bas_mat d))

(** val standard_gate_domega_matrix : standardGate -> dOmegaMatrix **)

let standard_gate_domega_matrix = function
| Std_I -> domega_matrix_eye (Stdlib.Int.succ 0)
| Std_X -> domega_matrix2 domega_zero domega_one domega_one domega_zero
| Std_Y -> domega_matrix2 domega_zero domega_minus_i domega_w2 domega_zero
| Std_Z -> domega_matrix2 domega_one domega_zero domega_zero domega_minus_one
| Std_H ->
  domega_matrix2 domega_h_scalar domega_h_scalar domega_h_scalar
    (domega_neg domega_h_scalar)
| Std_S -> domega_matrix2 domega_one domega_zero domega_zero domega_w2
| Std_Sdg -> domega_matrix2 domega_one domega_zero domega_zero domega_minus_i
| Std_T -> domega_matrix2 domega_one domega_zero domega_zero domega_w
| Std_Tdg ->
  domega_matrix2 domega_one domega_zero domega_zero (domega_neg domega_w3)
| Std_SX ->
  domega_matrix2 domega_half_one_plus_i domega_half_one_minus_i
    domega_half_one_minus_i domega_half_one_plus_i
| Std_SXdg ->
  domega_matrix2 domega_half_one_minus_i domega_half_one_plus_i
    domega_half_one_plus_i domega_half_one_minus_i

(** val standard_pattern_gate_nqubits : standardPatternGate -> int **)

let standard_pattern_gate_nqubits = function
| SPG_Std (_, qbit) -> Stdlib.Int.succ qbit
| SPG_Cnot (control, target) -> Stdlib.Int.succ (Nat.max control target)
| SPG_Swap (qbit1, qbit2) -> Stdlib.Int.succ (Nat.max qbit1 qbit2)

(** val standard_pattern_sequence_nqubits :
    standardPatternGate list -> int **)

let rec standard_pattern_sequence_nqubits = function
| [] -> 0
| gate :: rest ->
  Nat.max (standard_pattern_gate_nqubits gate)
    (standard_pattern_sequence_nqubits rest)

(** val standard_rule_nqubits :
    standardPatternGate list -> standardPatternGate list -> int **)

let standard_rule_nqubits lhs rhs =
  Nat.max (standard_pattern_sequence_nqubits lhs)
    (standard_pattern_sequence_nqubits rhs)

(** val qbit_in_bounds : int -> int -> bool **)

let qbit_in_bounds n qbit =
  Nat.ltb qbit n

(** val qbit_pair_in_bounds : int -> int -> int -> bool **)

let qbit_pair_in_bounds n qbit1 qbit2 =
  (&&) (qbit_in_bounds n qbit1) (qbit_in_bounds n qbit2)

(** val standard_pattern_gate_matrix :
    int -> standardPatternGate -> dOmegaMatrix option **)

let standard_pattern_gate_matrix n = function
| SPG_Std (gate0, qbit) ->
  if qbit_in_bounds n qbit
  then Some (domega_matrix_single n qbit (standard_gate_domega_matrix gate0))
  else None
| SPG_Cnot (control, target) ->
  if (||) ((=) control target) (negb (qbit_pair_in_bounds n control target))
  then None
  else Some (domega_matrix_cnot n control target)
| SPG_Swap (qbit1, qbit2) ->
  if (||) ((=) qbit1 qbit2) (negb (qbit_pair_in_bounds n qbit1 qbit2))
  then None
  else Some (domega_matrix_swap n qbit1 qbit2)

(** val standard_pattern_sequence_matrix :
    int -> standardPatternGate list -> dOmegaMatrix option **)

let rec standard_pattern_sequence_matrix n = function
| [] -> Some (domega_matrix_eye n)
| gate :: rest ->
  (match standard_pattern_gate_matrix n gate with
   | Some gate_matrix ->
     (match standard_pattern_sequence_matrix n rest with
      | Some rest_matrix -> Some (domega_matrix_mul n rest_matrix gate_matrix)
      | None -> None)
   | None -> None)

(** val standard_transform_validb :
    standardPatternGate list -> standardPatternGate list -> bool **)

let standard_transform_validb lhs rhs =
  let n = standard_rule_nqubits lhs rhs in
  (match standard_pattern_sequence_matrix n lhs with
   | Some lhs_matrix ->
     (match standard_pattern_sequence_matrix n rhs with
      | Some rhs_matrix ->
        domega_matrix_eq_up_to_phaseb n lhs_matrix rhs_matrix
      | None -> false)
   | None -> false)

(** val standard_rule_validb :
    int -> standardPatternGate list -> standardPatternGate list -> bool **)

let standard_rule_validb nq lhs rhs =
  (&&) ((<=) (standard_rule_nqubits lhs rhs) nq)
    (standard_transform_validb lhs rhs)

(** val standard_rewrite_rule :
    standardPatternGate list -> standardPatternGate list -> rewriteRule **)

let standard_rewrite_rule lhs rhs =
  { rule_lhs = (standard_pattern_sequence_to_instruction_patterns lhs);
    rule_rhs = (standard_pattern_sequence_to_instruction_patterns rhs) }

(** val standard_rule_of_sequences :
    int -> string -> standardPatternGate list -> standardPatternGate list ->
    transformSpec option **)

let standard_rule_of_sequences nq name lhs rhs =
  if standard_rule_validb nq lhs rhs
  then Some (transformSpec_simple_rule name (standard_rewrite_rule lhs rhs))
  else None
