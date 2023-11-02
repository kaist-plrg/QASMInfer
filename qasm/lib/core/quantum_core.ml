open Complex

let memoize2 f =
  let b = 8 in
  let memo_table = Hashtbl.create (Int.shift_left 1 (b + b)) in
  fun x y ->
    let xy = Int.shift_left x b + y in
    try Hashtbl.find memo_table xy
    with Not_found ->
      let result = f x y in
      Hashtbl.add memo_table xy result;
      result

type __ = Obj.t

let __ =
  let rec f _ = Obj.repr f in
  Obj.repr f

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m = match l with [] -> m | a :: l1 -> a :: app l1 m

type comparison = Eq | Lt | Gt

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub n m = Stdlib.max 0 (n - m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 = if b1 then b2 else if b2 then false else true

module Nat = struct
  (** val ltb : int -> int -> bool **)

  let ltb n m = Stdlib.Int.succ n <= m

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> n * pow n m0)
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q0 u =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> (q0, u))
      (fun x' ->
        (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
          (fun _ -> divmod x' y (Stdlib.Int.succ q0) y)
          (fun u' -> divmod x' y q0 u')
          u)
      x
end

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec n m = if n > m then None else Some (n < m)

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec = ( <= )

(** val le_dec : int -> int -> bool **)

let le_dec = le_gt_dec

(** val ge_dec : int -> int -> bool **)

let ge_dec n m = le_dec m n

module Pos = struct
  type mask = IsNul | IsPos of int | IsNeg
end

module Coq_Pos = struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.succ

  (** val add : int -> int -> int **)

  let rec add = ( + )

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> (fun p -> 1 + (2 * p)) (add_carry p q0))
          (fun q0 -> (fun p -> 2 * p) (add_carry p q0))
          (fun _ -> (fun p -> 1 + (2 * p)) (succ p))
          y)
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> (fun p -> 2 * p) (add_carry p q0))
          (fun q0 -> (fun p -> 1 + (2 * p)) (add p q0))
          (fun _ -> (fun p -> 2 * p) (succ p))
          y)
      (fun _ ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> (fun p -> 1 + (2 * p)) (succ q0))
          (fun q0 -> (fun p -> 2 * p) (succ q0))
          (fun _ -> (fun p -> 1 + (2 * p)) 1)
          y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p -> (fun p -> 1 + (2 * p)) ((fun p -> 2 * p) p))
      (fun p -> (fun p -> 1 + (2 * p)) (pred_double p))
      (fun _ -> 1)
      x

  type mask = Pos.mask = IsNul | IsPos of int | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
    | IsNul -> IsPos 1
    | IsPos p -> IsPos ((fun p -> 1 + (2 * p)) p)
    | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function IsPos p -> IsPos ((fun p -> 2 * p) p) | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p -> IsPos ((fun p -> 2 * p) ((fun p -> 2 * p) p)))
      (fun p -> IsPos ((fun p -> 2 * p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> double_mask (sub_mask p q0))
          (fun q0 -> succ_double_mask (sub_mask p q0))
          (fun _ -> IsPos ((fun p -> 2 * p) p))
          y)
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> succ_double_mask (sub_mask_carry p q0))
          (fun q0 -> double_mask (sub_mask p q0))
          (fun _ -> IsPos (pred_double p))
          y)
      (fun _ ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun _ -> IsNeg)
          (fun _ -> IsNeg)
          (fun _ -> IsNul)
          y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> succ_double_mask (sub_mask_carry p q0))
          (fun q0 -> double_mask (sub_mask p q0))
          (fun _ -> IsPos (pred_double p))
          y)
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> double_mask (sub_mask_carry p q0))
          (fun q0 -> succ_double_mask (sub_mask_carry p q0))
          (fun _ -> double_pred_mask p)
          y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub n m = Stdlib.max 1 (n - m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x = iter (mul x) 1

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun _ -> Stdlib.Int.succ 0)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont c x y = if x = y then c else if x < y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare x y = if x = y then Eq else if x < y then Lt else Gt

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun a' ->
            (fun f2p1 f2p f1 p ->
              if p <= 1 then f1 ()
              else if p mod 2 = 0 then f2p (p / 2)
              else f2p1 (p / 2))
              (fun b' ->
                match compare a' b' with
                | Eq -> (a, (1, 1))
                | Lt ->
                    let g, p = ggcdn n0 (sub b' a') a in
                    let ba, aa = p in
                    (g, (aa, add aa ((fun p -> 2 * p) ba)))
                | Gt ->
                    let g, p = ggcdn n0 (sub a' b') b in
                    let ab, bb = p in
                    (g, (add bb ((fun p -> 2 * p) ab), bb)))
              (fun b0 ->
                let g, p = ggcdn n0 a b0 in
                let aa, bb = p in
                (g, (aa, (fun p -> 2 * p) bb)))
              (fun _ -> (1, (a, 1)))
              b)
          (fun a0 ->
            (fun f2p1 f2p f1 p ->
              if p <= 1 then f1 ()
              else if p mod 2 = 0 then f2p (p / 2)
              else f2p1 (p / 2))
              (fun _ ->
                let g, p = ggcdn n0 a0 b in
                let aa, bb = p in
                (g, ((fun p -> 2 * p) aa, bb)))
              (fun b0 ->
                let g, p = ggcdn n0 a0 b0 in
                ((fun p -> 2 * p) g, p))
              (fun _ -> (1, (a, 1)))
              b)
          (fun _ -> (1, (1, b)))
          a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b = ggcdn (size_nat a + size_nat b) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x = iter_op ( + ) x (Stdlib.Int.succ 0)

  (** val of_nat : int -> int **)

  let rec of_nat n =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 1)
      (fun x ->
        (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
          (fun _ -> 1)
          (fun _ -> succ (of_nat x))
          x)
      n

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
end

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function [] -> [] | x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function [] -> [] | a :: t -> f a :: map f t

module Z = struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> (fun p -> 2 * p) p)
      (fun p -> ( ~- ) ((fun p -> 2 * p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> (fun p -> 1 + (2 * p)) p)
      (fun p -> ( ~- ) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> ( ~- ) 1)
      (fun p -> Coq_Pos.pred_double p)
      (fun p -> ( ~- ) ((fun p -> 1 + (2 * p)) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> double (pos_sub p q0))
          (fun q0 -> succ_double (pos_sub p q0))
          (fun _ -> (fun p -> 2 * p) p)
          y)
      (fun p ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> pred_double (pos_sub p q0))
          (fun q0 -> double (pos_sub p q0))
          (fun _ -> Coq_Pos.pred_double p)
          y)
      (fun _ ->
        (fun f2p1 f2p f1 p ->
          if p <= 1 then f1 ()
          else if p mod 2 = 0 then f2p (p / 2)
          else f2p1 (p / 2))
          (fun q0 -> ( ~- ) ((fun p -> 2 * p) q0))
          (fun q0 -> ( ~- ) (Coq_Pos.pred_double q0))
          (fun _ -> 0)
          y)
      x

  (** val add : int -> int -> int **)

  let add = ( + )

  (** val opp : int -> int **)

  let opp = ( ~- )

  (** val sub : int -> int -> int **)

  let sub = ( - )

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare x y = if x = y then Eq else if x < y then Lt else Gt

  (** val sgn : int -> int **)

  let sgn z0 =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun _ -> 1)
      (fun _ -> ( ~- ) 1)
      z0

  (** val leb : int -> int -> bool **)

  let leb x y = match compare x y with Gt -> false | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y = match compare x y with Lt -> true | _ -> false

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min

  (** val abs : int -> int **)

  let abs = Stdlib.Int.abs

  (** val to_nat : int -> int **)

  let to_nat z0 =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 0)
      (fun n0 -> Coq_Pos.of_succ_nat n0)
      n

  (** val to_pos : int -> int **)

  let to_pos z0 =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> p)
      (fun _ -> 1)
      z0

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
      if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))
      (fun a' ->
        let q0, r = pos_div_eucl a' b in
        let r' = add (mul ((fun p -> 2 * p) 1) r) 1 in
        if ltb r' b then (mul ((fun p -> 2 * p) 1) q0, r')
        else (add (mul ((fun p -> 2 * p) 1) q0) 1, sub r' b))
      (fun a' ->
        let q0, r = pos_div_eucl a' b in
        let r' = mul ((fun p -> 2 * p) 1) r in
        if ltb r' b then (mul ((fun p -> 2 * p) 1) q0, r')
        else (add (mul ((fun p -> 2 * p) 1) q0) 1, sub r' b))
      (fun _ -> if leb ((fun p -> 2 * p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
        (fun f0 fp fn z ->
          if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
          (fun _ -> (0, a))
          (fun _ -> pos_div_eucl a' b)
          (fun b' ->
            let q0, r = pos_div_eucl a' b' in
            (fun f0 fp fn z ->
              if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
              (fun _ -> (opp q0, 0))
              (fun _ -> (opp (add q0 1), add b r))
              (fun _ -> (opp (add q0 1), add b r))
              r)
          b)
      (fun a' ->
        (fun f0 fp fn z ->
          if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
          (fun _ -> (0, a))
          (fun _ ->
            let q0, r = pos_div_eucl a' b in
            (fun f0 fp fn z ->
              if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
              (fun _ -> (opp q0, 0))
              (fun _ -> (opp (add q0 1), sub b r))
              (fun _ -> (opp (add q0 1), sub b r))
              r)
          (fun b' ->
            let q0, r = pos_div_eucl a' b' in
            (q0, opp r))
          b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let q0, _ = div_eucl a b in
    q0

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    (fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
      (fun _ -> (abs b, (0, sgn b)))
      (fun a0 ->
        (fun f0 fp fn z ->
          if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
          (fun _ -> (abs a, (sgn a, 0)))
          (fun b0 ->
            let g, p = Coq_Pos.ggcd a0 b0 in
            let aa, bb = p in
            (g, (aa, bb)))
          (fun b0 ->
            let g, p = Coq_Pos.ggcd a0 b0 in
            let aa, bb = p in
            (g, (aa, ( ~- ) bb)))
          b)
      (fun a0 ->
        (fun f0 fp fn z ->
          if z = 0 then f0 () else if z > 0 then fp z else fn (-z))
          (fun _ -> (abs a, (sgn a, 0)))
          (fun b0 ->
            let g, p = Coq_Pos.ggcd a0 b0 in
            let aa, bb = p in
            (g, (( ~- ) aa, bb)))
          (fun b0 ->
            let g, p = Coq_Pos.ggcd a0 b0 in
            let aa, bb = p in
            (g, (( ~- ) aa, ( ~- ) bb)))
          b)
      a
end

type q = { qnum : int; qden : int }

module type RbaseSymbolsSig = sig
  type coq_R

  val coq_Rabst : float -> coq_R
  val coq_Rrepr : coq_R -> float
  val coq_R0 : coq_R
  val coq_R1 : coq_R
  val coq_Rplus : coq_R -> coq_R -> coq_R
  val coq_Rmult : coq_R -> coq_R -> coq_R
  val coq_Ropp : coq_R -> coq_R
end

module RbaseSymbolsImpl = struct
  type coq_R = float

  (** val coq_Rabst : float -> float **)

  let coq_Rabst x = x

  (** val coq_Rrepr : float -> float **)

  let coq_Rrepr x = x

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 = __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 = __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = Stdlib.( +. )

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = Stdlib.( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = Stdlib.( ~-. )

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def = __

  (** val coq_R1_def : __ **)

  let coq_R1_def = __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def = __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def = __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def = __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def = __
end

module type RinvSig = sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
end

module RinvImpl = struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv x = 1.0 /. x

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def = __
end

(** val rdiv :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv = Stdlib.( /. )

(** val rgt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rgt_dec x y = x > y

type 'v total_map = int -> 'v

(** val tm_empty : 'a1 -> 'a1 total_map **)

let tm_empty v _ = v

(** val tm_update : 'a1 total_map -> int -> 'a1 -> 'a1 total_map **)

let tm_update m k v x = if x = k then v else m x

(** val rTC : RbaseSymbolsImpl.coq_R -> Complex.t **)

let rTC x = { re = x; im = 0.0 }

(** val nTC : int -> Complex.t **)

let nTC n = { re = float_of_int n; im = 0.0 }

(** val func_sum_suppl : (int -> Complex.t) -> int -> int -> Complex.t **)

let rec func_sum_suppl f m n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> nTC 0)
    (fun n' -> Complex.add (f (m + n')) (func_sum_suppl f m n'))
    n

(** val func_sum2 : (int -> Complex.t) -> int -> int -> Complex.t **)

let func_sum2 f m n = func_sum_suppl f m (sub n m)

(** val func_sum : (int -> Complex.t) -> int -> Complex.t **)

let func_sum f n = func_sum2 f 0 n

type matrix = { mbits : int; minner : int -> int -> Complex.t }

(** val msize : matrix -> int **)

let msize m = (fun n -> Int.shift_left 1 n) m.mbits

type rowVec = { rVbits : int; rVinner : int -> Complex.t }
type colVec = { cVbits : int; cVinner : int -> Complex.t }

(** val extract_row_unsafe : matrix -> int -> rowVec **)

let extract_row_unsafe m i =
  { rVbits = m.mbits; rVinner = (fun j -> m.minner i j) }

(** val extract_col_unsafe : matrix -> int -> colVec **)

let extract_col_unsafe m j =
  { cVbits = m.mbits; cVinner = (fun i -> m.minner i j) }

(** val dot_product_suppl :
    (int -> Complex.t) -> (int -> Complex.t) -> int -> Complex.t **)

let dot_product_suppl r c idx = func_sum (fun i -> Complex.mul (r i) (c i)) idx

(** val muop : (Complex.t -> Complex.t) -> matrix -> matrix **)

let muop uop m =
  { mbits = m.mbits; minner = memoize2 (fun i j -> uop (m.minner i j)) }

(** val msmul : Complex.t -> matrix -> matrix **)

let msmul s m = muop (Complex.mul s) m

(** val mbop_unsafe :
    (Complex.t -> Complex.t -> Complex.t) -> matrix -> matrix -> matrix **)

let mbop_unsafe bop m1 m2 =
  {
    mbits = m1.mbits;
    minner = memoize2 (fun i j -> bop (m1.minner i j) (m2.minner i j));
  }

(** val mplus : matrix -> matrix -> matrix **)

let mplus m1 m2 = mbop_unsafe Complex.add m1 m2

(** val mmult_inner : matrix -> matrix -> int -> int -> Complex.t **)

let mmult_inner m1 m2 i j =
  dot_product_suppl (extract_row_unsafe m1 i).rVinner
    (extract_col_unsafe m2 j).cVinner (msize m1)

(** val mmult_unsafe : matrix -> matrix -> matrix **)

let mmult_unsafe m1 m2 =
  { mbits = m1.mbits; minner = memoize2 (fun i j -> mmult_inner m1 m2 i j) }

(** val mmult : matrix -> matrix -> matrix **)

let mmult = mmult_unsafe

(** val mconjtrans : matrix -> matrix **)

let mconjtrans m =
  {
    mbits = m.mbits;
    minner = memoize2 (fun i j -> Complex.conj (m.minner j i));
  }

(** val mtrace : matrix -> Complex.t **)

let mtrace m = func_sum (fun i -> m.minner i i) (msize m)

(** val eye : int -> matrix **)

let eye bits =
  {
    mbits = bits;
    minner =
      memoize2 (fun i j ->
          if i = j then
            if Nat.ltb i ((fun n -> Int.shift_left 1 n) bits) then
              nTC (Stdlib.Int.succ 0)
            else nTC 0
          else nTC 0);
  }

(** val tMproduct : matrix -> matrix -> matrix **)

let tMproduct m1 m2 =
  {
    mbits = m1.mbits + m2.mbits;
    minner =
      memoize2 (fun i j ->
          Complex.mul
            (m1.minner (i / msize m2) (j / msize m2))
            (m2.minner (i mod msize m2) (j mod msize m2)));
  }

(** val qop_ry : RbaseSymbolsImpl.coq_R -> matrix **)

let qop_ry theta =
  {
    mbits = Stdlib.Int.succ 0;
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ ->
                  rTC
                    (Stdlib.cos
                       (rdiv theta (float_of_int ((fun p -> 2 * p) 1)))))
                (fun n ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ ->
                      rTC
                        (RbaseSymbolsImpl.coq_Ropp
                           (Stdlib.sin
                              (rdiv theta (float_of_int ((fun p -> 2 * p) 1))))))
                    (fun _ -> rTC (float_of_int 0))
                    n)
                j)
            (fun n ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ ->
                      rTC
                        (Stdlib.sin
                           (rdiv theta (float_of_int ((fun p -> 2 * p) 1)))))
                    (fun n0 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ ->
                          rTC
                            (Stdlib.cos
                               (rdiv theta (float_of_int ((fun p -> 2 * p) 1)))))
                        (fun _ -> rTC (float_of_int 0))
                        n0)
                    j)
                (fun _ -> rTC (float_of_int 0))
                n)
            i);
  }

(** val qop_rz : RbaseSymbolsImpl.coq_R -> matrix **)

let qop_rz theta =
  {
    mbits = Stdlib.Int.succ 0;
    minner =
      memoize2 (fun i j ->
          if i = 0 then
            if j = 0 then
              Complex.exp
                ((fun re im -> { re; im })
                   (float_of_int 0)
                   (rdiv
                      (RbaseSymbolsImpl.coq_Ropp theta)
                      (float_of_int ((fun p -> 2 * p) 1))))
            else rTC (float_of_int 0)
          else if j = 0 then rTC (float_of_int 0)
          else
            Complex.exp
              ((fun re im -> { re; im })
                 (float_of_int 0)
                 (rdiv theta (float_of_int ((fun p -> 2 * p) 1)))));
  }

(** val qop_rot :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
    RbaseSymbolsImpl.coq_R -> matrix **)

let qop_rot theta phi lambda =
  mmult (mmult (qop_rz phi) (qop_ry theta)) (qop_rz lambda)

(** val qop_sq : int -> int -> matrix -> matrix **)

let qop_sq n t op =
  tMproduct (tMproduct (eye t) op) (eye (sub (sub n t) (Stdlib.Int.succ 0)))

(** val qproj0 : matrix **)

let qproj0 =
  {
    mbits = Stdlib.Int.succ 0;
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> nTC (Stdlib.Int.succ 0))
                (fun _ -> nTC 0)
                j)
            (fun _ -> nTC 0)
            i);
  }

(** val qproj1 : matrix **)

let qproj1 =
  {
    mbits = Stdlib.Int.succ 0;
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ -> nTC 0)
            (fun n ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ -> nTC 0)
                    (fun n0 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC (Stdlib.Int.succ 0))
                        (fun _ -> nTC 0)
                        n0)
                    j)
                (fun _ -> nTC 0)
                n)
            i);
  }

(** val qproj0_n_t : int -> int -> matrix **)

let qproj0_n_t n t = qop_sq n t qproj0

(** val qproj1_n_t : int -> int -> matrix **)

let qproj1_n_t n t = qop_sq n t qproj1

(** val qop_swap2 : matrix **)

let qop_swap2 =
  {
    mbits = Stdlib.Int.succ (Stdlib.Int.succ 0);
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> nTC (Stdlib.Int.succ 0))
                (fun _ -> nTC 0)
                j)
            (fun n ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ -> nTC 0)
                    (fun n0 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC 0)
                        (fun n1 ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC (Stdlib.Int.succ 0))
                            (fun _ -> nTC 0)
                            n1)
                        n0)
                    j)
                (fun n0 ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC 0)
                        (fun n1 ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC (Stdlib.Int.succ 0))
                            (fun _ -> nTC 0)
                            n1)
                        j)
                    (fun n1 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC 0)
                            (fun n2 ->
                              (fun fO fS n ->
                                if n = 0 then fO () else fS (n - 1))
                                (fun _ -> nTC 0)
                                (fun n3 ->
                                  (fun fO fS n ->
                                    if n = 0 then fO () else fS (n - 1))
                                    (fun _ -> nTC 0)
                                    (fun n4 ->
                                      (fun fO fS n ->
                                        if n = 0 then fO () else fS (n - 1))
                                        (fun _ -> nTC (Stdlib.Int.succ 0))
                                        (fun _ -> nTC 0)
                                        n4)
                                    n3)
                                n2)
                            j)
                        (fun _ -> nTC 0)
                        n1)
                    n0)
                n)
            i);
  }

(** val qop_swap1n_suppl : int -> matrix **)

let rec qop_swap1n_suppl n'' =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> qop_swap2)
    (fun n''' ->
      mmult_unsafe
        (mmult_unsafe
           (tMproduct qop_swap2 (eye n''))
           (tMproduct (eye (Stdlib.Int.succ 0)) (qop_swap1n_suppl n''')))
        (tMproduct qop_swap2 (eye n'')))
    n''

(** val qop_swap1n : int -> matrix **)

let qop_swap1n n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> eye 0)
    (fun n0 ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> eye (Stdlib.Int.succ 0))
        (fun n1 -> qop_swap1n_suppl n1)
        n0)
    n

(** val qop_swap : int -> int -> int -> matrix **)

let qop_swap n q1 q2 =
  let s = lt_eq_lt_dec q1 q2 in
  match s with
  | Some s0 ->
      if s0 then
        tMproduct
          (tMproduct (eye q1) (qop_swap1n (sub q2 q1 + Stdlib.Int.succ 0)))
          (eye (sub (sub n q2) (Stdlib.Int.succ 0)))
      else eye n
  | None ->
      tMproduct
        (tMproduct (eye q2) (qop_swap1n (sub q1 q2 + Stdlib.Int.succ 0)))
        (eye (sub (sub n q1) (Stdlib.Int.succ 0)))

(** val qop_swap_op : int -> int -> int -> matrix -> matrix **)

let qop_swap_op n q1 q2 op =
  mmult (mmult (qop_swap n q1 q2) op) (qop_swap n q1 q2)

(** val qop_cnot_ct : matrix **)

let qop_cnot_ct =
  {
    mbits = Stdlib.Int.succ (Stdlib.Int.succ 0);
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> nTC (Stdlib.Int.succ 0))
                (fun _ -> nTC 0)
                j)
            (fun n ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ -> nTC 0)
                    (fun n0 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC (Stdlib.Int.succ 0))
                        (fun _ -> nTC 0)
                        n0)
                    j)
                (fun n0 ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC 0)
                        (fun n1 ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC 0)
                            (fun n2 ->
                              (fun fO fS n ->
                                if n = 0 then fO () else fS (n - 1))
                                (fun _ -> nTC 0)
                                (fun n3 ->
                                  (fun fO fS n ->
                                    if n = 0 then fO () else fS (n - 1))
                                    (fun _ -> nTC (Stdlib.Int.succ 0))
                                    (fun _ -> nTC 0)
                                    n3)
                                n2)
                            n1)
                        j)
                    (fun n1 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC 0)
                            (fun n2 ->
                              (fun fO fS n ->
                                if n = 0 then fO () else fS (n - 1))
                                (fun _ -> nTC 0)
                                (fun n3 ->
                                  (fun fO fS n ->
                                    if n = 0 then fO () else fS (n - 1))
                                    (fun _ -> nTC (Stdlib.Int.succ 0))
                                    (fun _ -> nTC 0)
                                    n3)
                                n2)
                            j)
                        (fun _ -> nTC 0)
                        n1)
                    n0)
                n)
            i);
  }

(** val qop_cnot_tc : matrix **)

let qop_cnot_tc =
  {
    mbits = Stdlib.Int.succ (Stdlib.Int.succ 0);
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> nTC (Stdlib.Int.succ 0))
                (fun _ -> nTC 0)
                j)
            (fun n ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ -> nTC 0)
                    (fun n0 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC 0)
                        (fun n1 ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC 0)
                            (fun n2 ->
                              (fun fO fS n ->
                                if n = 0 then fO () else fS (n - 1))
                                (fun _ -> nTC (Stdlib.Int.succ 0))
                                (fun _ -> nTC 0)
                                n2)
                            n1)
                        n0)
                    j)
                (fun n0 ->
                  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                    (fun _ ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ -> nTC 0)
                        (fun n1 ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC 0)
                            (fun n2 ->
                              (fun fO fS n ->
                                if n = 0 then fO () else fS (n - 1))
                                (fun _ -> nTC (Stdlib.Int.succ 0))
                                (fun _ -> nTC 0)
                                n2)
                            n1)
                        j)
                    (fun n1 ->
                      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                        (fun _ ->
                          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                            (fun _ -> nTC 0)
                            (fun n2 ->
                              (fun fO fS n ->
                                if n = 0 then fO () else fS (n - 1))
                                (fun _ -> nTC (Stdlib.Int.succ 0))
                                (fun _ -> nTC 0)
                                n2)
                            j)
                        (fun _ -> nTC 0)
                        n1)
                    n0)
                n)
            i);
  }

(** val qop_cnot_ct_n : int -> matrix **)

let qop_cnot_ct_n n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> eye 0)
    (fun n0 ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> eye (Stdlib.Int.succ 0))
        (fun n1 -> tMproduct qop_cnot_ct (eye n1))
        n0)
    n

(** val qop_cnot_tc_n : int -> matrix **)

let qop_cnot_tc_n n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> eye 0)
    (fun n0 ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> eye (Stdlib.Int.succ 0))
        (fun n1 -> tMproduct qop_cnot_tc (eye n1))
        n0)
    n

(** val qop_cnot : int -> int -> int -> matrix **)

let qop_cnot n qc qt =
  let s = qc = 0 in
  if s then
    let s0 = qt = Stdlib.Int.succ 0 in
    if s0 then qop_cnot_ct_n n
    else qop_swap_op n (Stdlib.Int.succ 0) qt (qop_cnot_ct_n n)
  else
    let s0 = qc = Stdlib.Int.succ 0 in
    if s0 then
      let s1 = qt = 0 in
      if s1 then qop_cnot_tc_n n else qop_swap_op n 0 qt (qop_cnot_tc_n n)
    else
      let s1 = qt = 0 in
      if s1 then qop_swap_op n (Stdlib.Int.succ 0) qc (qop_cnot_tc_n n)
      else
        let s2 = qt = Stdlib.Int.succ 0 in
        if s2 then qop_swap_op n 0 qc (qop_cnot_ct_n n)
        else
          qop_swap_op n (Stdlib.Int.succ 0) qt
            (qop_swap_op n 0 qc (qop_cnot_ct_n n))

(** val den_0 : matrix **)

let den_0 =
  {
    mbits = Stdlib.Int.succ 0;
    minner =
      memoize2 (fun i j ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> nTC (Stdlib.Int.succ 0))
                (fun _ -> nTC 0)
                j)
            (fun _ -> nTC 0)
            i);
  }

(** val den_unitary : matrix -> matrix -> matrix **)

let den_unitary den uop = mmult (mmult uop den) (mconjtrans uop)

(** val den_reset : matrix -> int -> matrix **)

let den_reset den t =
  mplus
    (mmult (mmult (qproj0_n_t den.mbits t) den) (qproj0_n_t den.mbits t))
    (den_unitary
       (mmult (mmult (qproj1_n_t den.mbits t) den) (qproj1_n_t den.mbits t))
       (qop_sq den.mbits t
          (qop_rot
             (4. *. Stdlib.atan 1.)
             (float_of_int 0)
             (4. *. Stdlib.atan 1.))))

(** val den_prob : matrix -> matrix -> Complex.t **)

let den_prob den proj = mtrace (mmult den proj)

(** val den_prob_0 : matrix -> int -> int -> Complex.t **)

let den_prob_0 den n t = den_prob den (qproj0_n_t n t)

(** val den_prob_1 : matrix -> int -> int -> Complex.t **)

let den_prob_1 den n t = den_prob den (qproj1_n_t n t)

(** val den_measure : matrix -> matrix -> matrix **)

let den_measure den proj =
  msmul (Complex.inv (den_prob den proj)) (mmult (mmult proj den) proj)

(** val den_measure_0 : matrix -> int -> int -> matrix **)

let den_measure_0 den n t = den_measure den (qproj0_n_t n t)

(** val den_measure_1 : matrix -> int -> int -> matrix **)

let den_measure_1 den n t = den_measure den (qproj1_n_t n t)

(** val den_0_init : int -> matrix **)

let rec den_0_init n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> eye 0)
    (fun n' -> tMproduct den_0 (den_0_init n'))
    n

type instruction =
  | NopInstr
  | RotateInstr of
      RbaseSymbolsImpl.coq_R
      * RbaseSymbolsImpl.coq_R
      * RbaseSymbolsImpl.coq_R
      * int
  | CnotInstr of int * int
  | SwapInstr of int * int
  | MeasureInstr of int * int
  | SeqInstr of instruction * instruction
  | IfInstr of int * bool * instruction
  | ResetInstr of int

type inlinedProgram = {
  iP_num_qbits : int;
  iP_num_cbits : int;
  iP_num_subinstrs : int;
  iP_instrs : instruction;
}

type world = {
  w_qstate : matrix;
  w_cstate : bool total_map;
  w_prob : RbaseSymbolsImpl.coq_R;
  w_num_qubits : int;
}

type manyWorld = world list

(** val manyWorld_init : int -> int -> manyWorld **)

let manyWorld_init num_q _ =
  {
    w_qstate = den_0_init num_q;
    w_cstate = tm_empty false;
    w_prob = float_of_int 1;
    w_num_qubits = num_q;
  }
  :: []

(** val execute_rotate_instr :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
    RbaseSymbolsImpl.coq_R -> int -> manyWorld -> manyWorld **)

let rec execute_rotate_instr theta phi lambda target = function
  | [] -> []
  | w :: l ->
      let {
        w_qstate = w_qstate0;
        w_cstate = w_cstate0;
        w_prob = w_prob0;
        w_num_qubits = w_num_qubits0;
      } =
        w
      in
      let s = target < w_num_qubits0 in
      if s then
        {
          w_qstate =
            den_unitary w_qstate0
              (qop_sq w_num_qubits0 target (qop_rot theta phi lambda));
          w_cstate = w_cstate0;
          w_prob = w_prob0;
          w_num_qubits = w_num_qubits0;
        }
        :: execute_rotate_instr theta phi lambda target l
      else
        {
          w_qstate = w_qstate0;
          w_cstate = w_cstate0;
          w_prob = w_prob0;
          w_num_qubits = w_num_qubits0;
        }
        :: execute_rotate_instr theta phi lambda target l

(** val execute_cnot_instr : int -> int -> manyWorld -> manyWorld **)

let rec execute_cnot_instr control target = function
  | [] -> []
  | w :: l ->
      let {
        w_qstate = w_qstate0;
        w_cstate = w_cstate0;
        w_prob = w_prob0;
        w_num_qubits = w_num_qubits0;
      } =
        w
      in
      let s = ge_dec w_num_qubits0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) in
      if s then
        let s0 = control < w_num_qubits0 in
        if s0 then
          let s1 = target < w_num_qubits0 in
          if s1 then
            {
              w_qstate =
                den_unitary w_qstate0 (qop_cnot w_num_qubits0 control target);
              w_cstate = w_cstate0;
              w_prob = w_prob0;
              w_num_qubits = w_num_qubits0;
            }
            :: execute_cnot_instr control target l
          else
            {
              w_qstate = w_qstate0;
              w_cstate = w_cstate0;
              w_prob = w_prob0;
              w_num_qubits = w_num_qubits0;
            }
            :: execute_cnot_instr control target l
        else
          {
            w_qstate = w_qstate0;
            w_cstate = w_cstate0;
            w_prob = w_prob0;
            w_num_qubits = w_num_qubits0;
          }
          :: execute_cnot_instr control target l
      else
        {
          w_qstate = w_qstate0;
          w_cstate = w_cstate0;
          w_prob = w_prob0;
          w_num_qubits = w_num_qubits0;
        }
        :: execute_cnot_instr control target l

(** val execute_swap_instr : int -> int -> manyWorld -> manyWorld **)

let rec execute_swap_instr q1 q2 = function
  | [] -> []
  | w :: l ->
      let {
        w_qstate = w_qstate0;
        w_cstate = w_cstate0;
        w_prob = w_prob0;
        w_num_qubits = w_num_qubits0;
      } =
        w
      in
      let s = q1 < w_num_qubits0 in
      if s then
        let s0 = q2 < w_num_qubits0 in
        if s0 then
          {
            w_qstate = den_unitary w_qstate0 (qop_swap w_num_qubits0 q1 q2);
            w_cstate = w_cstate0;
            w_prob = w_prob0;
            w_num_qubits = w_num_qubits0;
          }
          :: execute_swap_instr q1 q2 l
        else
          {
            w_qstate = w_qstate0;
            w_cstate = w_cstate0;
            w_prob = w_prob0;
            w_num_qubits = w_num_qubits0;
          }
          :: execute_swap_instr q1 q2 l
      else
        {
          w_qstate = w_qstate0;
          w_cstate = w_cstate0;
          w_prob = w_prob0;
          w_num_qubits = w_num_qubits0;
        }
        :: execute_swap_instr q1 q2 l

(** val execute_measure_instr : int -> int -> manyWorld -> manyWorld **)

let rec execute_measure_instr qbit cbit = function
  | [] -> []
  | w :: l ->
      let {
        w_qstate = w_qstate0;
        w_cstate = w_cstate0;
        w_prob = w_prob0;
        w_num_qubits = w_num_qubits0;
      } =
        w
      in
      let s = qbit < w_num_qubits0 in
      if s then
        let prob0 = (fun x -> x.re) (den_prob_0 w_qstate0 w_num_qubits0 qbit) in
        let prob1 = (fun x -> x.re) (den_prob_1 w_qstate0 w_num_qubits0 qbit) in
        let s0 = rgt_dec prob0 (float_of_int 0) in
        if s0 then
          let s1 = rgt_dec prob1 (float_of_int 0) in
          if s1 then
            {
              w_qstate = den_measure_0 w_qstate0 w_num_qubits0 qbit;
              w_cstate = tm_update w_cstate0 cbit false;
              w_prob = RbaseSymbolsImpl.coq_Rmult w_prob0 prob0;
              w_num_qubits = w_num_qubits0;
            }
            :: {
                 w_qstate = den_measure_1 w_qstate0 w_num_qubits0 qbit;
                 w_cstate = tm_update w_cstate0 cbit true;
                 w_prob = RbaseSymbolsImpl.coq_Rmult w_prob0 prob1;
                 w_num_qubits = w_num_qubits0;
               }
            :: execute_measure_instr qbit cbit l
          else
            {
              w_qstate = den_measure_0 w_qstate0 w_num_qubits0 qbit;
              w_cstate = tm_update w_cstate0 cbit false;
              w_prob = RbaseSymbolsImpl.coq_Rmult w_prob0 prob0;
              w_num_qubits = w_num_qubits0;
            }
            :: execute_measure_instr qbit cbit l
        else
          let s1 = rgt_dec prob1 (float_of_int 0) in
          if s1 then
            {
              w_qstate = den_measure_1 w_qstate0 w_num_qubits0 qbit;
              w_cstate = tm_update w_cstate0 cbit true;
              w_prob = RbaseSymbolsImpl.coq_Rmult w_prob0 prob1;
              w_num_qubits = w_num_qubits0;
            }
            :: execute_measure_instr qbit cbit l
          else execute_measure_instr qbit cbit l
      else execute_measure_instr qbit cbit l

(** val execute_reset_instr : int -> manyWorld -> manyWorld **)

let rec execute_reset_instr target = function
  | [] -> []
  | w :: l ->
      let {
        w_qstate = w_qstate0;
        w_cstate = w_cstate0;
        w_prob = w_prob0;
        w_num_qubits = w_num_qubits0;
      } =
        w
      in
      let s = target < w_num_qubits0 in
      if s then
        {
          w_qstate = den_reset w_qstate0 target;
          w_cstate = w_cstate0;
          w_prob = w_prob0;
          w_num_qubits = w_num_qubits0;
        }
        :: execute_reset_instr target l
      else
        {
          w_qstate = w_qstate0;
          w_cstate = w_cstate0;
          w_prob = w_prob0;
          w_num_qubits = w_num_qubits0;
        }
        :: execute_reset_instr target l

(** val execute_suppl : int -> instruction -> manyWorld -> manyWorld **)

let rec execute_suppl ir instr worlds =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> worlds)
    (fun ir' ->
      match instr with
      | NopInstr -> worlds
      | RotateInstr (theta, phi, lambda, target) ->
          execute_rotate_instr theta phi lambda target worlds
      | CnotInstr (control, target) -> execute_cnot_instr control target worlds
      | SwapInstr (q1, q2) -> execute_swap_instr q1 q2 worlds
      | MeasureInstr (qbit, cbit) -> execute_measure_instr qbit cbit worlds
      | SeqInstr (i1, i2) -> execute_suppl ir' i2 (execute_suppl ir' i1 worlds)
      | IfInstr (cbit, cond, subinstr) ->
          concat
            (map
               (fun w ->
                 if eqb (w.w_cstate cbit) cond then
                   execute_suppl ir' subinstr (w :: [])
                 else w :: [])
               worlds)
      | ResetInstr target -> execute_reset_instr target worlds)
    ir

(** val execute : inlinedProgram -> manyWorld **)

let execute program =
  execute_suppl program.iP_num_subinstrs program.iP_instrs
    (manyWorld_init program.iP_num_qbits program.iP_num_cbits)

(** val cstate_to_binary_little_endian :
    int -> bool total_map -> int -> int **)

let rec cstate_to_binary_little_endian n cstate acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun n' ->
      let bit = if cstate n' then Stdlib.Int.succ 0 else 0 in
      cstate_to_binary_little_endian n' cstate
        (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) acc + bit))
    n

(** val cstate_to_binary : int -> bool total_map -> int **)

let cstate_to_binary num_cbits cstate =
  cstate_to_binary_little_endian num_cbits cstate 0

(** val calculate_prob :
    int -> manyWorld -> RbaseSymbolsImpl.coq_R total_map **)

let rec calculate_prob num_cbits = function
  | [] -> tm_empty RbaseSymbolsImpl.coq_R0
  | w :: t ->
      let prev = calculate_prob num_cbits t in
      let key = cstate_to_binary num_cbits w.w_cstate in
      tm_update prev key (RbaseSymbolsImpl.coq_Rplus (prev key) w.w_prob)

(** val execute_and_calculate_prob :
    inlinedProgram -> RbaseSymbolsImpl.coq_R total_map **)

let execute_and_calculate_prob program =
  calculate_prob program.iP_num_cbits (execute program)
