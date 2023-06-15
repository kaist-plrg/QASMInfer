
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val sub : int -> int -> int

module Nat :
 sig
  val pow : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int
 end

val lt_eq_lt_dec : int -> int -> bool option

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val sub : int -> int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val pow : int -> int -> int

  val size_nat : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val ggcdn : int -> int -> int -> int * (int * int)

  val ggcd : int -> int -> int * (int * int)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_nat : int -> int

  val of_succ_nat : int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val sgn : int -> int

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int

  val abs : int -> int

  val to_nat : int -> int

  val of_nat : int -> int

  val to_pos : int -> int

  val pos_div_eucl : int -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div : int -> int -> int

  val ggcd : int -> int -> int * (int * int)
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

module RbaseSymbolsImpl :
 RbaseSymbolsSig

module type RinvSig =
 sig
  val coq_Rinv : float -> float
 end

module RinvImpl :
 RinvSig



val rTC : float -> Complex.t

val rTIm : float -> Complex.t

val nTC : int -> Complex.t

val cexp : Complex.t -> Complex.t

val func_sum_suppl : (int -> Complex.t) -> int -> int -> Complex.t

val func_sum2 : (int -> Complex.t) -> int -> int -> Complex.t

val func_sum : (int -> Complex.t) -> int -> Complex.t

type matrix = { mbits : int; minner : (int -> int -> Complex.t) }

val msize : matrix -> int

type rowVec = { rVbits : int; rVinner : (int -> Complex.t) }

type colVec = { cVbits : int; cVinner : (int -> Complex.t) }

val extract_row_unsafe : matrix -> int -> rowVec

val extract_col_unsafe : matrix -> int -> colVec

val dot_product_suppl :
  (int -> Complex.t) -> (int -> Complex.t) -> int -> Complex.t

val mbop_unsafe :
  (Complex.t -> Complex.t -> Complex.t) -> matrix -> matrix -> matrix

val mplus : matrix -> matrix -> matrix

val mmult_inner : matrix -> matrix -> int -> int -> Complex.t

val mmult_unsafe : matrix -> matrix -> matrix

val mmult : matrix -> matrix -> matrix

val mconjtrans : matrix -> matrix

val mtrace : matrix -> Complex.t

val eye : int -> matrix

val tMproduct : matrix -> matrix -> matrix

val qop_ry : float -> matrix

val qop_rz : float -> matrix

val qop_rot : float -> float -> float -> matrix

val qop_sq : int -> int -> matrix -> matrix

val qproj0 : matrix

val qproj1 : matrix

val qproj0_n_t : int -> int -> matrix

val qproj1_n_t : int -> int -> matrix

val qop_swap2 : matrix

val qop_swap1n_suppl : int -> matrix

val qop_swap1n : int -> matrix

val qop_swap : int -> int -> int -> matrix

val qop_swap_op : int -> int -> int -> matrix -> matrix

val qop_cnot_ct : matrix

val qop_cnot_tc : matrix

val qop_cnot_ct_n : int -> matrix

val qop_cnot_tc_n : int -> matrix

val qop_cnot : int -> int -> int -> matrix

val den_0 : matrix

val den_unitary : matrix -> matrix -> matrix

val den_prob : matrix -> matrix -> float

val den_measure_2 : matrix -> int -> int -> (matrix * matrix)

val den_measure : matrix -> int -> int -> matrix

val den_0_init : int -> matrix
