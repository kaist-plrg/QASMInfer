open Quantum_core
open OpenQASM2.OpenQASM
open OpenQASM2.AST

type intermediate =
| NopInter
| RotateInter of RbaseSymbolsImpl.coq_R * RbaseSymbolsImpl.coq_R
   * RbaseSymbolsImpl.coq_R * int
| CnotInter of int * int
| MeasureInter of int * int
| ResetInter of int * intermediate
| SeqInter of intermediate * intermediate
| IfInter of int * bool * intermediate

module QASMqubit =
  struct
    type t = string * int
    let compare (s1, i1) (s2, i2) =
      match compare s1 s2 with
        0 -> compare i1 i2
      | c -> c
    end


module RegSizeMap = Map.Make(struct
    type t = id
    let compare = compare
  end
)
module QubitMap = Map.Make(QASMqubit)

let rec extract_qreg_size (qasm_program: program): int RegSizeMap.t =
  match qasm_program with
  | [] -> RegSizeMap.empty
  | Decl QReg (reg_id, reg_size) :: tail -> RegSizeMap.add reg_id reg_size (extract_qreg_size tail)
  | _ :: tail -> extract_qreg_size tail

let rec extract_creg_size (qasm_program: program): int RegSizeMap.t =
  match qasm_program with
  | [] -> RegSizeMap.empty
  | Decl CReg (reg_id, reg_size) :: tail -> RegSizeMap.add reg_id reg_size (extract_creg_size tail)
  | _ :: tail -> extract_creg_size tail

let extract_qubit_map (qasm_program: program): int QubitMap.t = failwith "not implemented"
