
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q0 u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q0, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Stdlib.Int.succ q0) y)
        (fun u' -> divmod x' y q0 u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)

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
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

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
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

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

type cReal = { seq : (int -> q); scale : int }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

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

(** val rminus :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rminus r1 r2 =
  RbaseSymbolsImpl.coq_Rplus r1 (RbaseSymbolsImpl.coq_Ropp r2)

(** val iPR_2 : int -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p0 ->
    RbaseSymbolsImpl.coq_Rmult
      (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
        RbaseSymbolsImpl.coq_R1)
      (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)))
    (fun p0 ->
    RbaseSymbolsImpl.coq_Rmult
      (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
        RbaseSymbolsImpl.coq_R1) (iPR_2 p0))
    (fun _ ->
    RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    p

(** val iPR : int -> RbaseSymbolsImpl.coq_R **)

let iPR p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p0 ->
    RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
    (fun p0 -> iPR_2 p0)
    (fun _ -> RbaseSymbolsImpl.coq_R1)
    p

(** val iZR : int -> RbaseSymbolsImpl.coq_R **)

let iZR z0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> RbaseSymbolsImpl.coq_R0)
    (fun n -> iPR n)
    (fun n -> RbaseSymbolsImpl.coq_Ropp (iPR n))
    z0

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

let rdiv r1 r2 =
  RbaseSymbolsImpl.coq_Rmult r1 (RinvImpl.coq_Rinv r2)

(** val exp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let exp = Stdlib.exp

(** val cos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let cos = Stdlib.cos

(** val sin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let sin = Stdlib.sin

type c = RbaseSymbolsImpl.coq_R * RbaseSymbolsImpl.coq_R

(** val rTC : RbaseSymbolsImpl.coq_R -> c **)

let rTC = fun x -> (x, 0.0)

(** val nTC : int -> c **)

let nTC = fun n -> (float_of_int n, 0.0)

(** val cplus : c -> c -> c **)

let cplus x y =
  ((RbaseSymbolsImpl.coq_Rplus (fst x) (fst y)),
    (RbaseSymbolsImpl.coq_Rplus (snd x) (snd y)))

(** val copp : c -> c **)

let copp x =
  ((RbaseSymbolsImpl.coq_Ropp (fst x)), (RbaseSymbolsImpl.coq_Ropp (snd x)))

(** val cminus : c -> c -> c **)

let cminus x y =
  cplus x (copp y)

(** val cmult : c -> c -> c **)

let cmult x y =
  ((rminus (RbaseSymbolsImpl.coq_Rmult (fst x) (fst y))
     (RbaseSymbolsImpl.coq_Rmult (snd x) (snd y))),
    (RbaseSymbolsImpl.coq_Rplus (RbaseSymbolsImpl.coq_Rmult (fst x) (snd y))
      (RbaseSymbolsImpl.coq_Rmult (snd x) (fst y))))

(** val cexp : c -> c **)

let cexp x =
  let r = fst x in
  let theta = snd x in
  cmult (rTC (exp r))
    (cplus (rTC (cos theta)) (RbaseSymbolsImpl.coq_R0, (sin theta)))

(** val cconj : c -> c **)

let cconj x =
  ((fst x), (RbaseSymbolsImpl.coq_Ropp (snd x)))

(** val func_sum_suppl : (int -> c) -> int -> int -> c **)

let rec func_sum_suppl f m n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> nTC 0)
    (fun n' -> cplus (f (add m n')) (func_sum_suppl f m n'))
    n

(** val func_sum2 : (int -> c) -> int -> int -> c **)

let func_sum2 f m n =
  func_sum_suppl f m (sub n m)

(** val func_sum : (int -> c) -> int -> c **)

let func_sum f n =
  func_sum2 f 0 n

type matrix = { mbits : int; minner : (int -> int -> c) }

(** val msize : matrix -> int **)

let msize m =
  Nat.pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) m.mbits

type rowVec = { rVbits : int; rVinner : (int -> c) }

type colVec = { cVbits : int; cVinner : (int -> c) }

(** val extract_row_unsafe : matrix -> int -> rowVec **)

let extract_row_unsafe m i =
  { rVbits = m.mbits; rVinner = (fun j -> m.minner i j) }

(** val extract_col_unsafe : matrix -> int -> colVec **)

let extract_col_unsafe m j =
  { cVbits = m.mbits; cVinner = (fun i -> m.minner i j) }

(** val dot_product_suppl : (int -> c) -> (int -> c) -> int -> c **)

let dot_product_suppl r c0 idx =
  func_sum (fun i -> cmult (r i) (c0 i)) idx

(** val mbop_unsafe : (c -> c -> c) -> matrix -> matrix -> matrix **)

let mbop_unsafe bop m1 m2 =
  { mbits = m1.mbits; minner = (fun i j ->
    bop (m1.minner i j) (m2.minner i j)) }

(** val mplus : matrix -> matrix -> matrix **)

let mplus m1 m2 =
  mbop_unsafe cplus m1 m2

(** val mminus : matrix -> matrix -> matrix **)

let mminus m1 m2 =
  mbop_unsafe cminus m1 m2

(** val mmult_inner : matrix -> matrix -> int -> int -> c **)

let mmult_inner m1 m2 i j =
  dot_product_suppl (extract_row_unsafe m1 i).rVinner
    (extract_col_unsafe m2 j).cVinner (msize m1)

(** val mmult_unsafe : matrix -> matrix -> matrix **)

let mmult_unsafe m1 m2 =
  { mbits = m1.mbits; minner = (fun i j -> mmult_inner m1 m2 i j) }

(** val mmult : matrix -> matrix -> matrix **)

let mmult =
  mmult_unsafe

(** val mconjtrans : matrix -> matrix **)

let mconjtrans m =
  { mbits = m.mbits; minner = (fun i j -> cconj (m.minner j i)) }

(** val eye : int -> matrix **)

let eye bits =
  { mbits = bits; minner = (fun i j ->
    if (=) i j then nTC (Stdlib.Int.succ 0) else nTC 0) }

(** val tMproduct : matrix -> matrix -> matrix **)

let tMproduct m1 m2 =
  { mbits = (add m1.mbits m2.mbits); minner = (fun i j ->
    cmult (m1.minner (Nat.div i (msize m2)) (Nat.div j (msize m2)))
      (m2.minner (Nat.modulo i (msize m2)) (Nat.modulo j (msize m2)))) }

(** val qop_ry : RbaseSymbolsImpl.coq_R -> matrix **)

let qop_ry theta =
  { mbits = (Stdlib.Int.succ 0); minner = (fun i j ->
    if (=) i 0
    then if (=) j 0
         then rTC (cos (rdiv theta (iZR ((fun p->2*p) 1))))
         else rTC
                (RbaseSymbolsImpl.coq_Ropp
                  (sin (rdiv theta (iZR ((fun p->2*p) 1)))))
    else if (=) j 0
         then rTC (sin (rdiv theta (iZR ((fun p->2*p) 1))))
         else rTC (cos (rdiv theta (iZR ((fun p->2*p) 1))))) }

(** val qop_rz : RbaseSymbolsImpl.coq_R -> matrix **)

let qop_rz theta =
  { mbits = (Stdlib.Int.succ 0); minner = (fun i j ->
    if (=) i 0
    then if (=) j 0
         then cexp ((iZR 0),
                (rdiv (RbaseSymbolsImpl.coq_Ropp theta)
                  (iZR ((fun p->2*p) 1))))
         else rTC (iZR 0)
    else if (=) j 0
         then rTC (iZR 0)
         else cexp ((iZR 0), (rdiv theta (iZR ((fun p->2*p) 1))))) }

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
  { mbits = (Stdlib.Int.succ 0); minner = (fun i j ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> nTC (Stdlib.Int.succ 0))
        (fun _ -> nTC 0)
        j)
      (fun _ -> nTC 0)
      i) }

(** val qproj1 : matrix **)

let qproj1 =
  { mbits = (Stdlib.Int.succ 0); minner = (fun i j ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> nTC 0)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> nTC 0)
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> nTC (Stdlib.Int.succ 0))
            (fun _ -> nTC 0)
            n0)
          j)
        (fun _ -> nTC 0)
        n)
      i) }

(** val qproj0_n_t : int -> int -> matrix **)

let qproj0_n_t n t =
  qop_sq n t qproj0

(** val qproj1_n_t : int -> int -> matrix **)

let qproj1_n_t n t =
  qop_sq n t qproj1

(** val qop_swap2 : matrix **)

let qop_swap2 =
  { mbits = (Stdlib.Int.succ (Stdlib.Int.succ 0)); minner = (fun i j ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> nTC (Stdlib.Int.succ 0))
        (fun _ -> nTC 0)
        j)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> nTC 0)
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> nTC 0)
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC (Stdlib.Int.succ 0))
              (fun _ -> nTC 0)
              n1)
            n0)
          j)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> nTC 0)
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC (Stdlib.Int.succ 0))
              (fun _ -> nTC 0)
              n1)
            j)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC 0)
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> nTC 0)
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> nTC 0)
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
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
      i) }

(** val qop_swap1n_suppl : int -> matrix **)

let rec qop_swap1n_suppl n'' =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> qop_swap2)
    (fun n''' ->
    mmult_unsafe
      (mmult_unsafe (tMproduct qop_swap2 (eye n''))
        (tMproduct (eye (Stdlib.Int.succ 0)) (qop_swap1n_suppl n''')))
      (tMproduct qop_swap2 (eye n'')))
    n''

(** val qop_swap1n : int -> matrix **)

let qop_swap1n n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> eye 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> eye (Stdlib.Int.succ 0))
      (fun n1 -> qop_swap1n_suppl n1)
      n0)
    n

(** val qop_swap : int -> int -> int -> matrix **)

let qop_swap n q1 q2 =
  let s = lt_eq_lt_dec q1 q2 in
  (match s with
   | Some a ->
     if a
     then tMproduct
            (tMproduct (eye q1)
              (qop_swap1n (add (sub q2 q1) (Stdlib.Int.succ 0))))
            (eye (sub (sub n q2) (Stdlib.Int.succ 0)))
     else eye n
   | None ->
     tMproduct
       (tMproduct (eye q2) (qop_swap1n (add (sub q1 q2) (Stdlib.Int.succ 0))))
       (eye (sub (sub n q1) (Stdlib.Int.succ 0))))

(** val qop_swap_op : int -> int -> int -> matrix -> matrix **)

let qop_swap_op n q1 q2 op =
  mmult (mmult (qop_swap n q1 q2) op) (qop_swap n q1 q2)

(** val qop_cnot_ct : matrix **)

let qop_cnot_ct =
  { mbits = (Stdlib.Int.succ (Stdlib.Int.succ 0)); minner = (fun i j ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> nTC (Stdlib.Int.succ 0))
        (fun _ -> nTC 0)
        j)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> nTC 0)
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> nTC (Stdlib.Int.succ 0))
            (fun _ -> nTC 0)
            n0)
          j)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> nTC 0)
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC 0)
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> nTC 0)
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> nTC (Stdlib.Int.succ 0))
                  (fun _ -> nTC 0)
                  n3)
                n2)
              n1)
            j)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC 0)
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> nTC 0)
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> nTC (Stdlib.Int.succ 0))
                  (fun _ -> nTC 0)
                  n3)
                n2)
              j)
            (fun _ -> nTC 0)
            n1)
          n0)
        n)
      i) }

(** val qop_cnot_tc : matrix **)

let qop_cnot_tc =
  { mbits = (Stdlib.Int.succ (Stdlib.Int.succ 0)); minner = (fun i j ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> nTC 0)
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> nTC (Stdlib.Int.succ 0))
          (fun _ -> nTC 0)
          n)
        j)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> nTC (Stdlib.Int.succ 0))
          (fun _ -> nTC 0)
          j)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> nTC 0)
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC 0)
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> nTC (Stdlib.Int.succ 0))
                (fun _ -> nTC 0)
                n2)
              n1)
            j)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> nTC 0)
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> nTC 0)
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> nTC 0)
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
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
      i) }

(** val qop_cnot_ct_n : int -> matrix **)

let qop_cnot_ct_n n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> eye 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> eye (Stdlib.Int.succ 0))
      (fun n1 -> tMproduct qop_cnot_ct (eye n1))
      n0)
    n

(** val qop_cnot_tc_n : int -> matrix **)

let qop_cnot_tc_n n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> eye 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> eye (Stdlib.Int.succ 0))
      (fun n1 -> tMproduct qop_cnot_tc (eye n1))
      n0)
    n

(** val qop_cnot : int -> int -> int -> matrix **)

let qop_cnot n qc qt =
  let s = (=) qc 0 in
  if s
  then let s0 = (=) qt (Stdlib.Int.succ 0) in
       if s0
       then qop_cnot_ct_n n
       else qop_swap_op n (Stdlib.Int.succ 0) qt (qop_cnot_ct_n n)
  else let s0 = (=) qc (Stdlib.Int.succ 0) in
       if s0
       then let s1 = (=) qt 0 in
            if s1
            then qop_cnot_tc_n n
            else qop_swap_op n 0 qt (qop_cnot_tc_n n)
       else let s1 = (=) qt 0 in
            if s1
            then qop_swap_op n (Stdlib.Int.succ 0) qc (qop_cnot_tc_n n)
            else let s2 = (=) qt (Stdlib.Int.succ 0) in
                 if s2
                 then qop_swap_op n 0 qc (qop_cnot_ct_n n)
                 else qop_swap_op n (Stdlib.Int.succ 0) qt
                        (qop_swap_op n 0 qc (qop_cnot_ct_n n))

(** val den_0 : matrix **)

let den_0 =
  { mbits = (Stdlib.Int.succ 0); minner = (fun i j ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> nTC (Stdlib.Int.succ 0))
        (fun _ -> nTC 0)
        j)
      (fun _ -> nTC 0)
      i) }

(** val den_unitary : matrix -> matrix -> matrix **)

let den_unitary den uop =
  mmult (mmult uop den) (mconjtrans uop)

(** val den_measure : matrix -> int -> int -> matrix **)

let den_measure den n t =
  mplus (mmult (mmult (qproj0_n_t n t) den) (qproj0_n_t n t))
    (mmult (mmult (qproj1_n_t n t) den) (qproj1_n_t n t))

(** val den_proj_uop : matrix -> matrix -> matrix -> matrix **)

let den_proj_uop den proj uop =
  mplus (den_unitary (mmult (mmult proj den) proj) uop)
    (mmult (mmult (mminus (eye proj.mbits) proj) den)
      (mminus (eye proj.mbits) proj))

(** val den_0_init : int -> matrix **)

let rec den_0_init n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> eye 0)
    (fun n' -> tMproduct den_0 (den_0_init n'))
    n
