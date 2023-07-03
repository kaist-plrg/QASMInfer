
type __ = Obj.t

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val mul : int -> int -> int

val sub : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val ltb : int -> int -> bool

  val pow : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int
 end

val lt_eq_lt_dec : int -> int -> bool option

val le_gt_dec : int -> int -> bool

val le_dec : int -> int -> bool

val ge_dec : int -> int -> bool

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

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

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
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val rgt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

type 'v total_map = int -> 'v

val tm_empty : 'a1 -> 'a1 total_map

val tm_update : 'a1 total_map -> int -> 'a1 -> 'a1 total_map

val rTC : RbaseSymbolsImpl.coq_R -> Complex.t

val nTC : int -> Complex.t

val func_sum : (int -> Complex.t) -> int -> Complex.t

type matrix = { mbits : int; minner : (int -> int -> Complex.t) }

val msize : matrix -> int

type rowVec = { rVbits : int; rVinner : (int -> Complex.t) }

type colVec = { cVbits : int; cVinner : (int -> Complex.t) }

val extract_row_unsafe : matrix -> int -> rowVec

val extract_col_unsafe : matrix -> int -> colVec

val dot_product_suppl : (int -> Complex.t) -> (int -> Complex.t) -> int -> Complex.t

val muop : (Complex.t -> Complex.t) -> matrix -> matrix

val msmul : Complex.t -> matrix -> matrix

val mmult_inner : matrix -> matrix -> int -> int -> Complex.t

val mmult_unsafe : matrix -> matrix -> matrix

val mmult : matrix -> matrix -> matrix

val mconjtrans : matrix -> matrix

val mtrace : matrix -> Complex.t

val eye : int -> matrix

val tMproduct : matrix -> matrix -> matrix

val qop_ry : RbaseSymbolsImpl.coq_R -> matrix

val qop_rz : RbaseSymbolsImpl.coq_R -> matrix

val qop_rot : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> matrix

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

val den_prob : matrix -> matrix -> Complex.t

val den_prob_0 : matrix -> int -> int -> Complex.t

val den_prob_1 : matrix -> int -> int -> Complex.t

val den_measure : matrix -> matrix -> matrix

val den_measure_0 : matrix -> int -> int -> matrix

val den_measure_1 : matrix -> int -> int -> matrix

val den_0_init : int -> matrix

type instruction =
| NopInstr
| RotateInstr of RbaseSymbolsImpl.coq_R * RbaseSymbolsImpl.coq_R * RbaseSymbolsImpl.coq_R * int
| CnotInstr of int * int
| SwapInstr of int * int
| MeasureInstr of int * int
| SeqInstr of instruction * instruction
| IfInstr of int * bool * instruction

type inlinedProgram = { iP_num_qbits : int; iP_num_cbits : int; iP_num_subinstrs : int;
                        iP_instrs : instruction }

type world = { w_qstate : matrix; w_cstate : bool total_map; w_prob : RbaseSymbolsImpl.coq_R;
               w_num_qubits : int }

type manyWorld = world list

val manyWorld_init : int -> int -> manyWorld

val execute_rotate_instr :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> int -> manyWorld
  -> manyWorld

val execute_cnot_instr : int -> int -> manyWorld -> manyWorld

val execute_swap_instr : int -> int -> manyWorld -> manyWorld

val execute_measure_instr : int -> int -> manyWorld -> manyWorld

val execute_suppl : int -> instruction -> manyWorld -> manyWorld

val execute : inlinedProgram -> manyWorld

val cstate_to_binary_suppl : int -> bool total_map -> int

val cstate_to_binary : int -> bool total_map -> int

val calculate_prob : int -> manyWorld -> RbaseSymbolsImpl.coq_R total_map

val execute_and_calculate_prob : inlinedProgram -> RbaseSymbolsImpl.coq_R total_map
