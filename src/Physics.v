Require Export Density.

Declare Scope Physics_scope.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope util_scope.
Open Scope C_scope.
Bind Scope C_scope with C.
Open Scope M_scope.
Open Scope T_scope.
Open Scope Qst_scope.
Open Scope Den_scope.


(*
  # Mixed States ( Mathematics of Quantum Computing (Wolfgang Scherer): 43 )
  In general a quantum mechanical system is described mathematically by an
  operator `rho` acting on a Hilbert space `H` with `rho` having the properties:
 *)

(* 1. `rho` is self-adjoint (i.e. Hermitian). *)
Theorem Mixed_States_Hermitian: forall num_qubits rho,
  DensityMatrix num_qubits rho -> Mconjtrans rho = rho.
Proof.
  apply DensityMatrix_Hermitian.
Qed.

(* 2. `rho` is positive. *)
Theorem Mixed_States_positive: forall num_qubits rho,
  DensityMatrix num_qubits rho -> forall qstate Hmc Hd,
  Cge_0 (dot_product (CVconjtrans qstate) (MVmult rho qstate Hmc) Hd).
Proof.
  apply DensityMatrix_positive.
Qed.

(* 3. `rho` has trace 1. *)
Theorem Mixed_States_trace_1: forall num_qubits rho,
  DensityMatrix num_qubits rho -> Mtrace rho = 1.
Proof.
  apply DensityMatrix_normalized.
Qed.

