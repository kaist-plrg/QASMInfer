
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> ( * ) n (pow n m0))
      m
 end

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec =
  (<=)

(** val le_dec : int -> int -> bool **)

let le_dec =
  le_gt_dec

(** val ge_dec : int -> int -> bool **)

let ge_dec n m =
  le_dec m n

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (add_carry p q0))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (succ q0))
        (fun q0 -> (fun p->2*p) (succ q0))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun q0 -> succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask_carry p q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Stdlib.max 1 (n-m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x =
    iter (mul x) 1

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun _ -> Stdlib.Int.succ 0)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a, 1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in
          let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a, 1)))
          b)
        (fun _ -> (1, (1, b)))
        a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn ((+) (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op (+) x (Stdlib.Int.succ 0)

  (** val of_nat : int -> int **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 1)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
 end

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Coq_Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (~-) ((fun p->2*p) q0))
        (fun q0 -> (~-) (Coq_Pos.pred_double q0))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val sgn : int -> int **)

  let sgn z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun _ -> 1)
      (fun _ -> (~-) 1)
      z0

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min

  (** val abs : int -> int **)

  let abs = Stdlib.Int.abs

  (** val to_nat : int -> int **)

  let to_nat z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : int -> int **)

  let to_pos z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> p)
      (fun _ -> 1)
      z0

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q0), r')
      else ((add (mul ((fun p->2*p) 1) q0) 1), (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q0), r')
      else ((add (mul ((fun p->2*p) 1) q0) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q0, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q0), 0))
           (fun _ -> ((opp (add q0 1)), (add b r)))
           (fun _ -> ((opp (add q0 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ ->
        let (q0, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q0), 0))
           (fun _ -> ((opp (add q0 1)), (sub b r)))
           (fun _ -> ((opp (add q0 1)), (sub b r)))
           r))
        (fun b' -> let (q0, r) = pos_div_eucl a' b' in (q0, (opp r)))
        b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let (q0, _) = div_eucl a b in q0

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> ((abs b), (0, (sgn b))))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a), 0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, ((~-) bb))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a), 0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), ((~-) bb))))
        b)
      a
 end

type q = { qnum : int; qden : int }

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

(** val rgt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rgt_dec = (fun x y -> x > y)

type 'v total_map = int -> 'v

(** val tm_empty : 'a1 -> 'a1 total_map **)

let tm_empty v _ =
  v

(** val tm_update : 'a1 total_map -> int -> 'a1 -> 'a1 total_map **)

let tm_update m k v x =
  if (=) x k then v else m x

(** val tmb_equal : bool total_map -> bool total_map -> int -> bool **)

let rec tmb_equal m1 m2 size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> eqb (m1 0) (m2 0))
    (fun n -> (&&) (eqb (m1 n) (m2 n)) (tmb_equal m1 m2 n))
    size

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
| Bas_mat a0 -> h a0
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
  | Bas_mat a0 -> mat_case0 (bas a0) b
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
  | Bas_mat a0 -> mat_case0 (bas a0) b
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
| Bas_mat a0 -> Bas_mat (f a0)
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
    (rTC (Stdlib.cos (rdiv _UU03b8_ (float_of_int ((fun p->2*p) 1)))))),
    (Bas_mat
    (Complex.neg
      (rTC (Stdlib.sin (rdiv _UU03b8_ (float_of_int ((fun p->2*p) 1))))))),
    (Bas_mat
    (rTC (Stdlib.sin (rdiv _UU03b8_ (float_of_int ((fun p->2*p) 1)))))),
    (Bas_mat
    (rTC (Stdlib.cos (rdiv _UU03b8_ (float_of_int ((fun p->2*p) 1)))))))

(** val mat_rot_z : RbaseSymbolsImpl.coq_R -> matrix **)

let mat_rot_z _UU03b8_ =
  Rec_mat (0, (Bas_mat
    (com_iexp
      (rdiv (RbaseSymbolsImpl.coq_Ropp _UU03b8_)
        (float_of_int ((fun p->2*p) 1))))), (Bas_mat (rTC (float_of_int 0))),
    (Bas_mat (rTC (float_of_int 0))), (Bas_mat
    (com_iexp (rdiv _UU03b8_ (float_of_int ((fun p->2*p) 1))))))

(** val mat_rot :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
    RbaseSymbolsImpl.coq_R -> matrix **)

let mat_rot _UU03b8_ _UU03c6_ l =
  mat_mul (Stdlib.Int.succ 0)
    (mat_mul (Stdlib.Int.succ 0) (mat_rot_z _UU03c6_) (mat_rot_y _UU03b8_))
    (mat_rot_z l)

(** val mat_single : int -> int -> matrix -> matrix **)

let rec mat_single n t u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat_eye 0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      tensor_product (Stdlib.Int.succ 0) n' u (mat_eye n'))
      (fun t' ->
      tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
        (mat_single n' t' u))
      t)
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
    (fun _ -> Bas_mat (nTC 0))
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
    (fun _ -> Bas_mat (nTC (Stdlib.Int.succ 0)))
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      tensor_product (Stdlib.Int.succ 0) n' mat_proj1_base (mat_eye n'))
      (fun p' ->
      tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
        (mat_proj1 n' p'))
      p)
    n

(** val mat_ctrl_single : int -> int -> int -> matrix -> matrix **)

let rec mat_ctrl_single n c t u =
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
        t)
      (fun c' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        mat_add ((+) (Stdlib.Int.succ 0) n')
          (tensor_product (Stdlib.Int.succ 0) n' u (mat_proj0 n' c'))
          (tensor_product (Stdlib.Int.succ 0) n'
            (mat_eye (Stdlib.Int.succ 0)) (mat_proj1 n' c')))
        (fun t' ->
        tensor_product (Stdlib.Int.succ 0) n' (mat_eye (Stdlib.Int.succ 0))
          (mat_ctrl_single n' c' t' u))
        t)
      c)
    n

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

let den_prob_0 n t den =
  den_prob n (mat_proj0 n t) den

(** val den_prob_1 : int -> int -> matrix -> Complex.t **)

let den_prob_1 n t den =
  den_prob n (mat_proj1 n t) den

(** val den_measure : int -> matrix -> matrix -> matrix **)

let den_measure n proj den =
  mat_scale n (Complex.inv (den_prob n proj den))
    (mat_mul n (mat_mul n proj den) proj)

(** val den_measure_0 : int -> int -> matrix -> matrix **)

let den_measure_0 n t den =
  den_measure n (mat_proj0 n t) den

(** val den_measure_1 : int -> int -> matrix -> matrix **)

let den_measure_1 n t den =
  den_measure n (mat_proj1 n t) den

(** val den_reset : int -> int -> matrix -> matrix **)

let den_reset n t den =
  mat_add n (mat_mul n (mat_mul n (mat_proj0 n t) den) (mat_proj0 n t))
    (den_uop n
      (mat_single n t
        (mat_rot (4. *. Stdlib.atan 1.) (float_of_int 0)
          (4. *. Stdlib.atan 1.)))
      (mat_mul n (mat_mul n (mat_proj1 n t) den) (mat_proj1 n t)))

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
           in add0 0 n0)) mat_swap2
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
         in add0 0 n0)) mat_swap2
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

(** val mat_not2 : matrix **)

let mat_not2 =
  Rec_mat (0, (Bas_mat (nTC 0)), (Bas_mat (nTC (Stdlib.Int.succ 0))),
    (Bas_mat (nTC (Stdlib.Int.succ 0))), (Bas_mat (nTC 0)))

(** val mat_cnot : int -> int -> int -> matrix **)

let mat_cnot n qc qt =
  mat_ctrl_single n qc qt mat_not2

type instruction =
| NopInstr
| RotateInstr of RbaseSymbolsImpl.coq_R * RbaseSymbolsImpl.coq_R
   * RbaseSymbolsImpl.coq_R * int
| CnotInstr of int * int
| SwapInstr of int * int
| MeasureInstr of int * int
| SeqInstr of instruction * instruction
| IfInstr of int * bool * instruction
| ResetInstr of int

type inlinedProgram = { iP_num_cbits : int; iP_num_subinstrs : int;
                        iP_instrs : instruction }

type world = { w_num_clbits : int; w_qstate : matrix;
               w_cstate : bool total_map; w_prob : RbaseSymbolsImpl.coq_R }

type manyWorld = world list

(** val manyWorld_init : int -> int -> int -> manyWorld **)

let manyWorld_init nq _ num_c =
  { w_num_clbits = num_c; w_qstate = (den_init nq); w_cstate =
    (tm_empty false); w_prob = (float_of_int 1) } :: []

(** val merge_manyworld_suppl : int -> world -> manyWorld -> manyWorld **)

let rec merge_manyworld_suppl nq w = function
| [] -> w :: []
| y :: l ->
  let b = tmb_equal y.w_cstate w.w_cstate y.w_num_clbits in
  if b
  then let { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
         w_cstate0; w_prob = w_prob0 } = w
       in
       let { w_num_clbits = _; w_qstate = w_qstate1; w_cstate = _; w_prob =
         w_prob1 } = y
       in
       { w_num_clbits = w_num_clbits0; w_qstate =
       (mat_add nq
         (mat_scale nq
           (com_div (rTC w_prob0) (Complex.add (rTC w_prob0) (rTC w_prob1)))
           w_qstate0)
         (mat_scale nq
           (com_div (rTC w_prob1) (Complex.add (rTC w_prob0) (rTC w_prob1)))
           w_qstate1)); w_cstate = w_cstate0; w_prob =
       (RbaseSymbolsImpl.coq_Rplus w_prob0 w_prob1) } :: l
  else y :: (merge_manyworld_suppl nq w l)

(** val merge_manyworld : int -> manyWorld -> manyWorld **)

let merge_manyworld nq = function
| [] -> []
| w :: l ->
  (match l with
   | [] -> merge_manyworld_suppl nq w []
   | w0 :: l0 -> merge_manyworld_suppl nq w (merge_manyworld_suppl nq w0 l0))

(** val execute_rotate_instr :
    int -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
    RbaseSymbolsImpl.coq_R -> int -> manyWorld -> manyWorld **)

let rec execute_rotate_instr nq theta phi lambda target = function
| [] -> []
| w :: l ->
  let { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
    w_cstate0; w_prob = w_prob0 } = w
  in
  let s = (<) target nq in
  if s
  then { w_num_clbits = w_num_clbits0; w_qstate =
         (den_uop nq (mat_single nq target (mat_rot theta phi lambda))
           w_qstate0); w_cstate = w_cstate0; w_prob =
         w_prob0 } :: (execute_rotate_instr nq theta phi lambda target l)
  else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
         w_cstate0; w_prob =
         w_prob0 } :: (execute_rotate_instr nq theta phi lambda target l)

(** val execute_cnot_instr : int -> int -> int -> manyWorld -> manyWorld **)

let rec execute_cnot_instr nq control target = function
| [] -> []
| w :: l ->
  let { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
    w_cstate0; w_prob = w_prob0 } = w
  in
  let s = ge_dec nq (Stdlib.Int.succ (Stdlib.Int.succ 0)) in
  if s
  then let s0 = (<) control nq in
       if s0
       then let s1 = (<) target nq in
            if s1
            then { w_num_clbits = w_num_clbits0; w_qstate =
                   (den_uop nq (mat_cnot nq control target) w_qstate0);
                   w_cstate = w_cstate0; w_prob =
                   w_prob0 } :: (execute_cnot_instr nq control target l)
            else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0;
                   w_cstate = w_cstate0; w_prob =
                   w_prob0 } :: (execute_cnot_instr nq control target l)
       else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
              w_cstate0; w_prob =
              w_prob0 } :: (execute_cnot_instr nq control target l)
  else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
         w_cstate0; w_prob =
         w_prob0 } :: (execute_cnot_instr nq control target l)

(** val execute_swap_instr : int -> int -> int -> manyWorld -> manyWorld **)

let rec execute_swap_instr nq q1 q2 = function
| [] -> []
| w :: l ->
  let { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
    w_cstate0; w_prob = w_prob0 } = w
  in
  let s = (<) q1 nq in
  if s
  then let s0 = (<) q2 nq in
       if s0
       then { w_num_clbits = w_num_clbits0; w_qstate =
              (den_uop nq (mat_swap nq q1 q2) w_qstate0); w_cstate =
              w_cstate0; w_prob = w_prob0 } :: (execute_swap_instr nq q1 q2 l)
       else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
              w_cstate0; w_prob = w_prob0 } :: (execute_swap_instr nq q1 q2 l)
  else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
         w_cstate0; w_prob = w_prob0 } :: (execute_swap_instr nq q1 q2 l)

(** val execute_measure_instr :
    int -> int -> int -> manyWorld -> manyWorld **)

let rec execute_measure_instr nq qbit cbit = function
| [] -> []
| w :: l ->
  let { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
    w_cstate0; w_prob = w_prob0 } = w
  in
  let s = (<) qbit nq in
  if s
  then let prob0 = (fun x -> x.re) (den_prob_0 nq qbit w_qstate0) in
       let prob1 = (fun x -> x.re) (den_prob_1 nq qbit w_qstate0) in
       let s0 = rgt_dec prob0 (float_of_int 0) in
       if s0
       then let s1 = rgt_dec prob1 (float_of_int 0) in
            if s1
            then { w_num_clbits = w_num_clbits0; w_qstate =
                   (den_measure_0 nq qbit w_qstate0); w_cstate =
                   (tm_update w_cstate0 cbit false); w_prob =
                   (RbaseSymbolsImpl.coq_Rmult w_prob0 prob0) } :: ({ w_num_clbits =
                   w_num_clbits0; w_qstate =
                   (den_measure_1 nq qbit w_qstate0); w_cstate =
                   (tm_update w_cstate0 cbit true); w_prob =
                   (RbaseSymbolsImpl.coq_Rmult w_prob0 prob1) } :: (execute_measure_instr
                                                                    nq qbit
                                                                    cbit l))
            else { w_num_clbits = w_num_clbits0; w_qstate =
                   (den_measure_0 nq qbit w_qstate0); w_cstate =
                   (tm_update w_cstate0 cbit false); w_prob =
                   (RbaseSymbolsImpl.coq_Rmult w_prob0 prob0) } :: (execute_measure_instr
                                                                    nq qbit
                                                                    cbit l)
       else let s1 = rgt_dec prob1 (float_of_int 0) in
            if s1
            then { w_num_clbits = w_num_clbits0; w_qstate =
                   (den_measure_1 nq qbit w_qstate0); w_cstate =
                   (tm_update w_cstate0 cbit true); w_prob =
                   (RbaseSymbolsImpl.coq_Rmult w_prob0 prob1) } :: (execute_measure_instr
                                                                    nq qbit
                                                                    cbit l)
            else execute_measure_instr nq qbit cbit l
  else execute_measure_instr nq qbit cbit l

(** val execute_reset_instr : int -> int -> manyWorld -> manyWorld **)

let rec execute_reset_instr nq target = function
| [] -> []
| w :: l ->
  let { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
    w_cstate0; w_prob = w_prob0 } = w
  in
  let s = (<) target nq in
  if s
  then { w_num_clbits = w_num_clbits0; w_qstate =
         (den_reset nq target w_qstate0); w_cstate = w_cstate0; w_prob =
         w_prob0 } :: (execute_reset_instr nq target l)
  else { w_num_clbits = w_num_clbits0; w_qstate = w_qstate0; w_cstate =
         w_cstate0; w_prob = w_prob0 } :: (execute_reset_instr nq target l)

(** val execute_suppl :
    int -> int -> instruction -> manyWorld -> manyWorld **)

let rec execute_suppl nq ir instr worlds =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> worlds)
    (fun ir' ->
    match instr with
    | NopInstr -> worlds
    | RotateInstr (theta, phi, lambda, target) ->
      execute_rotate_instr nq theta phi lambda target worlds
    | CnotInstr (control, target) ->
      execute_cnot_instr nq control target worlds
    | SwapInstr (q1, q2) -> execute_swap_instr nq q1 q2 worlds
    | MeasureInstr (qbit, cbit) ->
      merge_manyworld nq (execute_measure_instr nq qbit cbit worlds)
    | SeqInstr (i1, i2) ->
      execute_suppl nq ir' i2 (execute_suppl nq ir' i1 worlds)
    | IfInstr (cbit, cond, subinstr) ->
      concat
        (map (fun w ->
          if eqb (w.w_cstate cbit) cond
          then execute_suppl nq ir' subinstr (w :: [])
          else w :: []) worlds)
    | ResetInstr target -> execute_reset_instr nq target worlds)
    ir

(** val execute : int -> inlinedProgram -> manyWorld **)

let execute nq program =
  execute_suppl nq program.iP_num_subinstrs program.iP_instrs
    (manyWorld_init nq nq program.iP_num_cbits)

(** val cstate_to_binary_little_endian :
    int -> bool total_map -> int -> int **)

let rec cstate_to_binary_little_endian n cstate acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' ->
    let bit = if cstate n' then Stdlib.Int.succ 0 else 0 in
    cstate_to_binary_little_endian n' cstate
      ((+) (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) acc) bit))
    n

(** val cstate_to_binary : int -> bool total_map -> int **)

let cstate_to_binary num_cbits cstate =
  cstate_to_binary_little_endian num_cbits cstate 0

(** val calculate_prob :
    int -> int -> manyWorld -> RbaseSymbolsImpl.coq_R total_map **)

let rec calculate_prob nq num_cbits = function
| [] -> tm_empty RbaseSymbolsImpl.coq_R0
| w :: t ->
  let prev = calculate_prob nq num_cbits t in
  let key = cstate_to_binary num_cbits w.w_cstate in
  tm_update prev key (RbaseSymbolsImpl.coq_Rplus (prev key) w.w_prob)

(** val execute_and_calculate_prob :
    int -> inlinedProgram -> RbaseSymbolsImpl.coq_R total_map **)

let execute_and_calculate_prob nq program =
  calculate_prob nq program.iP_num_cbits (execute nq program)
