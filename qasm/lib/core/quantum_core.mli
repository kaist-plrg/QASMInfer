
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
  val pow : int -> int -> int
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

val rdiv :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val rgt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

type 'v total_map = int -> 'v

val tm_empty : 'a1 -> 'a1 total_map

val tm_update : 'a1 total_map -> int -> 'a1 -> 'a1 total_map

val tmb_equal : bool total_map -> bool total_map -> int -> bool

val rTC : RbaseSymbolsImpl.coq_R -> Complex.t

val rTIm : RbaseSymbolsImpl.coq_R -> Complex.t

val nTC : int -> Complex.t

val com_div : Complex.t -> Complex.t -> Complex.t

val com_iexp : RbaseSymbolsImpl.coq_R -> Complex.t



type matrix =
| Bas_mat of Complex.t
| Rec_mat of int * matrix * matrix * matrix * matrix

val mat_case0 : (Complex.t -> 'a1) -> matrix -> 'a1

val mat_caseS_ :
  int -> matrix -> (matrix -> matrix -> matrix -> matrix -> 'a1) -> 'a1

val mat_rect2 :
  (Complex.t -> Complex.t -> 'a1) -> (int -> matrix -> matrix -> matrix ->
  matrix -> matrix -> matrix -> matrix -> matrix -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1) -> int -> matrix -> matrix -> 'a1

val mat_rect2_gen :
  (Complex.t -> Complex.t -> 'a1) -> (int -> matrix -> matrix -> matrix ->
  matrix -> matrix -> matrix -> matrix -> matrix -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1) -> int -> matrix -> matrix -> 'a1

val mat_0 : int -> matrix

val mat_eye : int -> matrix

val mat_map : (Complex.t -> Complex.t) -> int -> matrix -> matrix

val mat_map2 :
  (Complex.t -> Complex.t -> Complex.t) -> int -> matrix -> matrix -> matrix

val mat_scale : int -> Complex.t -> matrix -> matrix

val mat_conjtrans : int -> matrix -> matrix

val mat_trace : int -> matrix -> Complex.t

val mat_add : int -> matrix -> matrix -> matrix

val mat_mul : int -> matrix -> matrix -> matrix

val tensor_product : int -> int -> matrix -> matrix -> matrix

val mat_rot_y : RbaseSymbolsImpl.coq_R -> matrix

val mat_rot_z : RbaseSymbolsImpl.coq_R -> matrix

val mat_rot :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
  -> matrix

val mat_single : int -> int -> matrix -> matrix

val mat_proj0_base : matrix

val mat_proj1_base : matrix

val mat_proj0 : int -> int -> matrix

val mat_proj1 : int -> int -> matrix

val mat_ctrl_single : int -> int -> int -> matrix -> matrix

val den_init : int -> matrix

val den_uop : int -> matrix -> matrix -> matrix

val den_prob : int -> matrix -> matrix -> Complex.t

val den_prob_0 : int -> int -> matrix -> Complex.t

val den_prob_1 : int -> int -> matrix -> Complex.t

val den_measure : int -> matrix -> matrix -> matrix

val den_measure_0 : int -> int -> matrix -> matrix

val den_measure_1 : int -> int -> matrix -> matrix

val den_reset : int -> int -> matrix -> matrix

val mat_swap2 : matrix

val mat_swap_1n_suppl : int -> matrix

val mat_swap_1n : int -> matrix

val mat_swap : int -> int -> int -> matrix

val mat_not2 : matrix

val mat_cnot : int -> int -> int -> matrix

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

val manyWorld_init : int -> int -> int -> manyWorld

val merge_manyworld_suppl : int -> world -> manyWorld -> manyWorld

val merge_manyworld : int -> manyWorld -> manyWorld

val execute_rotate_instr :
  int -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
  RbaseSymbolsImpl.coq_R -> int -> manyWorld -> manyWorld

val execute_cnot_instr : int -> int -> int -> manyWorld -> manyWorld

val execute_swap_instr : int -> int -> int -> manyWorld -> manyWorld

val execute_measure_instr : int -> int -> int -> manyWorld -> manyWorld

val execute_reset_instr : int -> int -> manyWorld -> manyWorld

val execute_suppl : int -> int -> instruction -> manyWorld -> manyWorld

val execute : int -> inlinedProgram -> manyWorld

val cstate_to_binary_little_endian : int -> bool total_map -> int -> int

val cstate_to_binary : int -> bool total_map -> int

val calculate_prob :
  int -> int -> manyWorld -> RbaseSymbolsImpl.coq_R total_map

val execute_and_calculate_prob :
  int -> inlinedProgram -> RbaseSymbolsImpl.coq_R total_map
