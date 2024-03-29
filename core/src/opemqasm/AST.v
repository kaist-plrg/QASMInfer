Require Import Coq.Strings.String.
Require Import ZArith.
Require Import Reals.

Definition qasm_id : Set := string.

Inductive qasm_binaryop : Set :=
| QASM_Plus : qasm_binaryop
| QASM_Minus : qasm_binaryop
| QASM_Times : qasm_binaryop
| QASM_Div : qasm_binaryop
| QASM_Pow : qasm_binaryop.

Inductive qasm_unaryop : Set :=
| QASM_Sin : qasm_unaryop
| QASM_Cos : qasm_unaryop
| QASM_Tan : qasm_unaryop
| QASM_Exp : qasm_unaryop
| QASM_Ln : qasm_unaryop
| QASM_Sqrt : qasm_unaryop
| QASM_UMinus : qasm_unaryop.

Inductive qasm_exp : Set :=
| QASM_Real : R -> qasm_exp
| QASM_Nninteger : Z -> qasm_exp
| QASM_Pi : qasm_exp
| QASM_Id : qasm_id -> qasm_exp
| QASM_BinaryOp : qasm_binaryop -> qasm_exp -> qasm_exp -> qasm_exp
| QASM_UnaryOp : qasm_unaryop -> qasm_exp -> qasm_exp.

Definition qasm_argument : Set := qasm_id * option nat.

Inductive qasm_uop : Set :=
| QASM_CX : qasm_argument -> qasm_argument -> qasm_uop
| QASM_U : list qasm_exp -> qasm_argument -> qasm_uop
| QASM_Gate : qasm_id -> list qasm_exp -> list qasm_argument -> qasm_uop.

Inductive qasm_qop : Set :=
| QASM_Uop : qasm_uop -> qasm_qop
| QASM_Meas : qasm_argument -> qasm_argument -> qasm_qop
| QASM_Reset : qasm_argument -> qasm_qop.

Inductive qasm_gop : Set :=
| QASM_GUop : qasm_uop -> qasm_gop
| QASM_GBarrier : list qasm_id -> qasm_gop.

Definition qasm_gatedecl : Set := qasm_id * list qasm_id * list qasm_id.

Inductive qasm_decl : Set :=
| QASM_QReg : qasm_id -> nat -> qasm_decl
| QASM_CReg : qasm_id -> nat -> qasm_decl.

Inductive qasm_statement : Set :=
| QASM_Include : string -> qasm_statement
| QASM_Decl : qasm_decl -> qasm_statement
| QASM_GateDecl : qasm_gatedecl -> list qasm_gop -> qasm_statement
| QASM_OpaqueDecl : qasm_gatedecl -> qasm_statement
| QASM_Qop : qasm_qop -> qasm_statement
| QASM_If : qasm_id -> nat -> qasm_qop -> qasm_statement
| QASM_Barrier : list qasm_argument -> qasm_statement.

Definition qasm_program : Set := list qasm_statement.
