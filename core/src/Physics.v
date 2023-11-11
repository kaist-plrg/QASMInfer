Require Import Program.

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
  operator \rho acting on a Hilbert space with \rho having the properties:
 *)

(* 1. \rho is self-adjoint (i.e. Hermitian). *)
(* Physical meaning: Eigenvalues are real, because any physical quantity should be real *)
Theorem all_states_Hermitian: forall program world,
  In world (Execute program) -> Qop_Hermitian (W_qstate world).
Proof.
  intro program.
  apply Forall_forall.
  apply Forall_impl with (P := (fun world => DensityMatrix program.(IP_num_qbits) (W_qstate world))).
  intros world H.
  apply DensityMatrix_Hermitian with (n := program.(IP_num_qbits)).
  apply H.
  apply Execute_quantum_state_density.
Qed.

(* 2. \rho is positive semidefinite. *)
(* Physical meaning: Eigenvalues are positive, because probability is positive *)
Theorem all_states_positive: forall program world,
  In world (Execute program) -> Qop_positive (W_qstate world).
Proof.
  intro program.
  apply Forall_forall.
  apply Forall_impl with (P := (fun world => DensityMatrix program.(IP_num_qbits) (W_qstate world))).
  intros world H.
  apply DensityMatrix_positive with (n := program.(IP_num_qbits)).
  apply H.
  apply Execute_quantum_state_density.
Qed.

(* 3. \rho has trace 1. *)
(* Physical meaning: sum of probabilites of every possible states is 1 *)
Theorem all_states_trace_1: forall program world,
  In world (Execute program) -> Mtrace (W_qstate world) = 1.
Proof.
  intro program.
  apply Forall_forall.
  apply Forall_impl with (P := (fun world => DensityMatrix program.(IP_num_qbits) (W_qstate world))).
  intros world H.
  apply DensityMatrix_normalized with (n := program.(IP_num_qbits)).
  apply H.
  apply Execute_quantum_state_density.
Qed.


(*
  # Observables and States ( Mathematics of Quantum Computing (Wolfgang Scherer): 45 )
  The quantum mechanical expectation value of an observable A in a mixed state
  \rho is given by

  < A >_\rho := tr ( \rho A ).
 *)
Theorem Observables_and_States: forall rho observable Hbits,
  Den_expect rho observable Hbits = Mtrace (Mmult rho observable Hbits).
Proof.
  reflexivity.
Qed.


(*
  # Measurement Probability ( Mathematics of Quantum Computing (Wolfgang Scherer): 45 )
  If the quanutm system is in a state \rho, \lambda is an eigenvalue of A and
  P_\lambda the projection onto the eigenspace of \lambda, then the probability
  P_\rho ( \lambda ) that a measurement of A yields the value \lambda is given by

  P_\rho ( \lambda ) = tr ( \rho P_\lambda ).
 *)
Theorem measurement_probability_postulate: forall rho projection Hbits,
  Den_prob rho projection Hbits = Mtrace (Mmult rho projection Hbits).
Proof.
  reflexivity.
Qed.


(*
  # Projection Postulate
  ( Mathematics of Quantum Computing (Wolfgang Scherer): 45 )
  If the quantum system is initially described by the state \rho, and then the
  measurement of the observable A yields the eigenvalue \lambda of A, then this
  measurement has effected the following change of state

  after measurement : \frac { P_\lambda \rho P_lambda } { tr ( \rho P_\lambda ) }.

  ( From Classical to Quantum Shannon Theory (mark M. Wilde): 159 )
  Using the born rule, the above can be interpreted as the state produced by
  performing the measurement but not recording which outcome occurred.

  after measurement : \sum_\lambda { P_\lambda rho P_lambda }.

  * In the quantum computing case, a measurement is done in the computational
  * basis: 0 or 1. Therefore, in a measurement of some target qubit, there are
  * two possible projection operators:
  * (Qproj0_n_t num_bits target_bit Ht) and (Qproj1_n_t num_bits target_bit Ht).

 *)
Theorem projection_postulate: forall rho proj Hbits Hp Hm1 Hm2,
  Den_measure rho proj Hbits =
    Msmul
      (Cinv (Den_prob rho proj Hp))
      ( Mmult (
          Mmult proj rho Hm1
        ) proj Hm2).
Proof.
  reflexivity.
Qed.

Theorem projection_postulate_density: forall num_bits rho proj Hbits,
  DensityMatrix num_bits rho ->
  Projection proj ->
  Den_prob rho proj Hbits <> 0 ->
  DensityMatrix num_bits (Den_measure rho proj Hbits).
Proof.
  apply DensityMatrix_measure.
Qed.

(*
  # Time Evolution ( Mathematics of Quantum Computing (Wolfgang Scherer): 45 )
  Any time evolution of a quantum system that is not caused by a measurement is
  described as an evolution of states given by a unitary time evolution operator
  acting on the density operator as

  \rho ( t ) = U \rho U^*.
 *)

Theorem time_evoluation_postulate: forall rho uop H1 H2,
  Den_unitary rho uop H1 H2 = (Mmult (Mmult uop rho H1) (Mconjtrans uop) H2).
Proof.
  reflexivity.
Qed.

Theorem time_evolution_postulate_density: forall num_bits rho uop Hbits1 Hbits2,
  DensityMatrix num_bits rho ->
  Qop_unitary uop ->
  DensityMatrix num_bits (Mmult (Mmult uop rho Hbits1) (Mconjtrans uop) Hbits2).
Proof.
  apply DensityMatrix_unitary.
Qed.
