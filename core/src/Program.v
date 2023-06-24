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
Import ListNotations.


(* inlined QASM2.0 instructions ================================================================= *)

Inductive Instruction: Type :=
| RotateInstr: R -> R -> R -> nat -> Instruction  (* U (theta phi lambda) qbit *)
| CnotInstr: nat -> nat -> Instruction  (* CnotInstr a b: flip b iff a *)
| MeasureInstr: nat -> nat -> Instruction  (* MeasureInstr q c: *)
| IfInstr: nat -> bool -> list Instruction -> Instruction.  (* if cbit == 0 (false) or cbit == 1 (true) *)

(* ============================================================================================== *)
(* inlined QASM2.0 program ====================================================================== *)

Record InlinedProgram: Type := {
  IP_num_qbits: nat;
  IP_num_cbits: nat;
  IP_num_subinstrs: nat;  (* numbers of all subinstructions, to prove decreasing argument of fix *)
  IP_instrs: list Instruction;
}.

(* ============================================================================================== *)
(* MWI for express program states =============================================================== *)

Record World: Type := {
  W_qstate: Matrix; (* density matrix *)
  W_cstate: total_map bool;  (* false for 0, true for 1 *)
  W_prob: R; (* probability of the world *)
  W_num_qubits: nat;
  W_qstate_valid: Mbits W_qstate = W_num_qubits
}.

Definition ManyWorld: Type := list World.

Definition ManyWorld_init (num_q num_c: nat): ManyWorld.
Proof.
  refine ([{|
    W_qstate := Den_0_init num_q;
    W_cstate := tm_empty false;
    W_prob := 1;
    W_num_qubits := num_q;
  |}]).
  apply Den_0_init_bits.
Defined.

(* ============================================================================================== *)
(* execution ==================================================================================== *)

Fixpoint Execute_rotate_instr (theta phi lambda: R) (target: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  - exact [].
  - destruct (lt_dec target nq).
      + refine ({|
          W_qstate := Den_unitary qstate (Qop_sq nq target (Qop_rot theta phi lambda) l _) _ _;
          W_cstate := cstate;
          W_prob := prob;
          W_num_qubits := nq;
        |} :: (Execute_rotate_instr theta phi lambda target t)).
        Unshelve.
        rewrite Den_unitary_bits.
        apply Hq.
        apply Qop_rot_bits.
        simpl_bits.
        rewrite Qop_sq_bits.
        lia.
        simpl_bits.
        reflexivity.
      + apply ({|
          W_qstate := qstate;
          W_cstate := cstate;
          W_prob := prob;
          W_num_qubits := nq;
          W_qstate_valid := Hq;
        |} :: (Execute_rotate_instr theta phi lambda target t)).  (* nop *)
Defined.

Fixpoint Execute_cnot_instr (control target: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  - exact [].
  - destruct (ge_dec nq 2), (lt_dec control nq), (lt_dec target nq).
    refine ({|
      W_qstate := Den_unitary qstate (Qop_cnot nq control target g l l0) _ _;
      W_cstate := cstate;
      W_prob := prob;
      W_num_qubits := nq;
      |} :: (Execute_cnot_instr control target t)).
    2-8: apply ({|
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_num_qubits := nq;
        W_qstate_valid := Hq;
      |} :: (Execute_cnot_instr control target t)).  (* nop *)
    Unshelve.
    rewrite Den_unitary_bits.
    apply Hq.
    simpl_bits.
    rewrite Qop_cnot_bits.
    lia.
    simpl_bits.
    reflexivity.
Defined.

Fixpoint Execute_measure_instr (qbit cbit: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  - exact [].
  - destruct (lt_dec qbit nq).
    + specialize (Creal (Den_prob_0 qstate nq qbit l Hq)) as prob0.
      specialize (Creal (Den_prob_1 qstate nq qbit l Hq)) as prob1.
      destruct (Rgt_dec prob0 0), (Rgt_dec prob1 0).
      * refine ({|
          W_qstate := Den_measure_0 qstate nq qbit l Hq;
          W_cstate := tm_update cstate cbit false;
          W_prob := prob * prob0;
          W_num_qubits := nq;
        |} :: {|
          W_qstate := Den_measure_1 qstate nq qbit l Hq;
          W_cstate := tm_update cstate cbit true;
          W_prob := prob * prob1;
          W_num_qubits := nq;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        apply Den_measure_0_bits.
        apply Den_measure_1_bits.
      * refine ({|
          W_qstate := Den_measure_0 qstate nq qbit l Hq;
          W_cstate := tm_update cstate cbit false;
          W_prob := prob * prob0;
          W_num_qubits := nq;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        apply Den_measure_0_bits.
      * refine ({|
          W_qstate := Den_measure_1 qstate nq qbit l Hq;
          W_cstate := tm_update cstate cbit true;
          W_prob := prob * prob1;
          W_num_qubits := nq;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        apply Den_measure_1_bits.
      * apply (Execute_measure_instr qbit cbit t).  (* nop *)
  + apply (Execute_measure_instr qbit cbit t).  (* nop *)
Defined.

(* Fixpoint Execute_if_instr (ir: nat) (cbit: nat) (cond: bool) (subinstrs: list Instruction) (worlds: ManyWorld): ManyWorld :=
  match ir with
  | O => worlds
  | S ir' => (
    match worlds with
    | [] => []
    | hw :: tw =>
      if (W_cstate hw cbit =? cond) then (Execute_suppl ir' subinstrs
Proof.
  induction worlds as [|hw tw].
  - exact [].
  - destruct (eqb (W_cstate hw cbit) cond) eqn: Heq.
    + apply (Execute_suppl). *)



Fixpoint Execute_suppl (ir: nat) (instrs: list Instruction) (worlds: ManyWorld): ManyWorld :=
  match ir with
  | O => worlds
  | S ir' => (
    match instrs with
    | []                                         => worlds
    | (RotateInstr theta phi lambda target) :: t => Execute_suppl ir' t (Execute_rotate_instr theta phi lambda target worlds)
    | (CnotInstr control target)            :: t => Execute_suppl ir' t (Execute_cnot_instr control target worlds)
    | (MeasureInstr qbit cbit)              :: t => Execute_suppl ir' t (Execute_measure_instr qbit cbit worlds)
    | (IfInstr cbit cond subinstrs)         :: t => Execute_suppl ir' t (
        concat (map (fun w =>
          if (eqb (W_cstate w cbit)  cond)
          then Execute_suppl ir' subinstrs [w]
          else [w]) worlds)
    )
    end
  )
  end.

Fixpoint Cstate_to_binary_suppl (n: nat) (cstate: total_map bool): nat := match n with
  | O => O
  | S n' => 2 * Cstate_to_binary_suppl n' cstate + if (cstate n') then 1 else 0
end.

Definition Cstate_to_binary (num_cbits: nat) (cstate: total_map bool) := Cstate_to_binary_suppl num_cbits cstate.

(*  0 -> true
    1 -> false     ===> 1011 (value of 0 is the leftmost bit in the result)
    2 -> true      ===>
    3 -> true *)

Fixpoint Calculate_prob (num_cbits: nat) (worlds: ManyWorld): total_map R :=
  match worlds with
  | [] => tm_empty R0
  | w :: t =>
    let prev := Calculate_prob num_cbits t in
    let key := Cstate_to_binary num_cbits (W_cstate w) in
    tm_update prev key (prev key + W_prob w)%R
  end.

Definition Execute (ip: InlinedProgram): total_map R :=
  let result := Execute_suppl (IP_num_subinstrs ip) (IP_instrs ip) (ManyWorld_init (IP_num_qbits ip) (IP_num_cbits ip)) in
  Calculate_prob (IP_num_cbits ip) result.