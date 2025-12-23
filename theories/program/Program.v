Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.

From Stdlib Require Import List.

Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope Matrix_scope.
Import List.ListNotations.

Section PROGRAM.

Variable nq : nat. (* number of qubits *)

(* desugared QASM instructions ================================================================== *)

Inductive Instruction: Type :=
| NopInstr: Instruction
| RotateInstr: R -> R -> R -> nat -> Instruction  (* U (theta phi lambda) qbit *)
| CnotInstr: nat -> nat -> Instruction  (* CnotInstr a b: flip b iff a *)
| SwapInstr: nat -> nat -> Instruction  (* SwapInstr a b: swap a b *)
| MeasureInstr: nat -> nat -> Instruction  (* MeasureInstr q c: *)
| SeqInstr: Instruction -> Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction  (* if cbit == 0 (false) or cbit == 1 (true) *)
| ResetInstr: nat -> Instruction.  (* reset qbit to 0 *)


(* ============================================================================================== *)
(* desugared QASM program ======================================================================= *)

Record InlinedProgram: Type := {
  IP_num_cbits: nat;
  IP_instrs: Instruction;
}.

(* ============================================================================================== *)
(* Branching for program states ================================================================= *)

Record Branch: Type := {
  B_num_clbits: nat;
  B_qstate: Matrix nq; (* density matrix *)
  B_cstate: total_map bool;  (* false for 0, true for 1 *)
  B_prob: R; (* probability of the branch *)
  B_prob_valid: (B_prob > 0)%R;
}.

Definition qstate_valid (b: Branch): Prop := den_valid (B_qstate b).

(* ============================================================================================== *)
(* Program state ================================================================================ *)

Definition ProgramState: Type := list Branch.

Definition ProgramState_init (num_q num_c: nat): ProgramState.
Proof.
  refine ([{|
    B_num_clbits := num_c;
    B_qstate := den_init nq;
    B_cstate := tm_empty false;
    B_prob := 1;
  |}]).
  lra.
Defined.

(* ============================================================================================== *)
(* merging two branches ========================================================================= *)

Definition Merge_branch (b0 b1: Branch): Branch.
Proof.
  destruct b0 eqn:ew0, b1.
  destruct
    (Nat.eq_dec B_num_clbits0 B_num_clbits1),
    (tmb_equal B_cstate0 B_cstate1 B_num_clbits0) eqn:ec.
  subst B_num_clbits1.
  refine ({|
    B_num_clbits := B_num_clbits0;
    B_qstate := B_prob0 .* B_qstate0 + B_prob1 .* B_qstate1;
    B_cstate := B_cstate0;
    B_prob := B_prob0 + B_prob1;
  |}).
  lra.
  all: exact b0.
Defined.

Definition Merge_program_state_suppl (b: Branch) (ps: ProgramState): ProgramState.
Proof.
  induction ps.
  - exact [b].
  - destruct
    (tmb_equal (B_cstate a) (B_cstate b) (B_num_clbits a)).
    destruct b as [nc qst cst p pv], a as [nc' qst' cst' p' pv']; simpl in *.
    refine ({|
      B_num_clbits := nc;
      B_qstate := (p / (p + p'))%com .* qst + (p' / (p + p'))%com .* qst';
      B_cstate := cst;
      B_prob := p + p';
    |} :: ps). (* merge *)
      lra.
    exact (a :: IHps). (* nop *)
Defined.

Definition Merge_program_state (ps: ProgramState): ProgramState.
Proof.
  destruct ps.
  - exact [].
  - destruct ps.
    + exact (Merge_program_state_suppl b []).
    + exact (Merge_program_state_suppl b (Merge_program_state_suppl b0 ps)).
Defined.

Lemma Merge_program_state_suppl_qstate_valid:
  forall (b: Branch) (ps: ProgramState),
  den_valid (B_qstate b) -> Forall qstate_valid ps -> Forall qstate_valid (Merge_program_state_suppl b ps).
Proof.
  induction ps.
  - intros; simpl.
    apply Forall_cons.
    apply H.
    apply Forall_nil.
  - intros; simpl.
    apply Forall_cons_iff in H0.
    destruct H0.
    destruct (tmb_equal (B_cstate a) (B_cstate b) (B_num_clbits a)).
    + destruct b as [nc qst cst p pv], a as [nc' qst' cst' p' pv']; simpl in *.
      apply Forall_cons.
      * apply den_valid_mix.
        all: assumption.
      * apply H1.
    + apply Forall_cons; auto; auto.
Qed.

Lemma Merge_program_state_qstate_valid:
  forall (branches: ProgramState),
  Forall qstate_valid branches -> Forall qstate_valid (Merge_program_state branches).
Proof.
  intros; simpl.
  induction branches as [|b0[|b1 t] ].
  - apply Forall_nil.
  - apply H.
  - apply Forall_cons_iff in H; destruct H.
    apply Forall_cons_iff in H0; destruct H0.
    apply Merge_program_state_suppl_qstate_valid.
    all: auto.
    apply Merge_program_state_suppl_qstate_valid.
    all: auto.
Qed.

(* ============================================================================================== *)
(* execution ==================================================================================== *)

Fixpoint Execute_rotate_instr (theta phi lambda: R) (target: nat) (branches: ProgramState): ProgramState.
Proof.
  destruct branches as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec target nq).
    + exact ({|
        B_num_clbits := nc;
        B_qstate := den_uop (mat_single nq target (mat_rot theta phi lambda)) qstate ;
        B_cstate := cstate;
        B_prob := prob;
        B_prob_valid := Hp;
      |} :: (Execute_rotate_instr theta phi lambda target t)).
    + exact ({|
        B_num_clbits := nc;
        B_qstate := qstate;
        B_cstate := cstate;
        B_prob := prob;
        B_prob_valid := Hp;
      |} :: (Execute_rotate_instr theta phi lambda target t)).  (* nop *)
Defined.

Fixpoint Execute_cnot_instr (control target: nat) (branches: ProgramState): ProgramState.
Proof.
  destruct branches as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (ge_dec nq 2), (lt_dec control nq), (lt_dec target nq).
    exact ({|
      B_num_clbits := nc;
      B_qstate := den_uop (mat_cnot control target) qstate;
      B_cstate := cstate;
      B_prob := prob;
      B_prob_valid := Hp;
      |} :: (Execute_cnot_instr control target t)).
    all: refine ({|
      B_num_clbits := nc;
      B_qstate := qstate;
      B_cstate := cstate;
      B_prob := prob;
      B_prob_valid := Hp;
    |} :: (Execute_cnot_instr control target t)).  (* nop *)
Defined.

Fixpoint Execute_swap_instr (q1 q2: nat) (branches: ProgramState): ProgramState.
Proof.
  destruct branches as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec q1 nq), (lt_dec q2 nq).
    exact ({|
      B_num_clbits := nc;
      B_qstate := den_uop (mat_swap q1 q2) qstate;
      B_cstate := cstate;
      B_prob := prob;
      B_prob_valid := Hp;
      |} :: (Execute_swap_instr q1 q2 t)).
    all: exact ({|
        B_num_clbits := nc;
        B_qstate := qstate;
        B_cstate := cstate;
        B_prob := prob;
        B_prob_valid := Hp;
      |} :: (Execute_swap_instr q1 q2 t)).  (* nop *)
Defined.

Fixpoint Execute_measure_instr (qbit cbit: nat) (branches: ProgramState): ProgramState.
Proof.
  destruct branches as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec qbit nq).
    + specialize (com_real (den_prob_0 qbit qstate)) as prob0.
      specialize (com_real (den_prob_1 qbit qstate)) as prob1.
      destruct (Rgt_dec prob0 0), (Rgt_dec prob1 0).
      * refine ({|
          B_num_clbits := nc;
          B_qstate := den_measure_0 qbit qstate;
          B_cstate := tm_update cstate cbit false;
          B_prob := prob * prob0;
        |} :: {|
          B_num_clbits := nc;
          B_qstate := den_measure_1 qbit qstate;
          B_cstate := tm_update cstate cbit true;
          B_prob := prob * prob1;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        all: try nra.
      * refine ({|
          B_num_clbits := nc;
          B_qstate := den_measure_0 qbit qstate;
          B_cstate := tm_update cstate cbit false;
          B_prob := prob * prob0;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        nra.
      * refine ({|
          B_num_clbits := nc;
          B_qstate := den_measure_1 qbit qstate;
          B_cstate := tm_update cstate cbit true;
          B_prob := prob * prob1;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        nra.
      * exact (Execute_measure_instr qbit cbit t).  (* nop *)
  + exact (Execute_measure_instr qbit cbit t).  (* nop *)
Defined.

Fixpoint Execute_reset_instr (target: nat) (branches: ProgramState): ProgramState.
Proof.
  destruct branches as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec target nq).
    + exact ({|
        B_num_clbits := nc;
        B_qstate := den_reset target qstate;
        B_cstate := cstate;
        B_prob := prob;
        B_prob_valid := Hp;
      |} :: (Execute_reset_instr target t)).
    + exact ({|
        B_num_clbits := nc;
        B_qstate := qstate;
        B_cstate := cstate;
        B_prob := prob;
        B_prob_valid := Hp;
      |} :: (Execute_reset_instr target t)).  (* nop *)
Defined.

Fixpoint Execute_suppl_old (ir: nat) (instr: Instruction) (branches: ProgramState): ProgramState :=
  match ir with
  | O => branches
  | S ir' => (
    match instr with
    | NopInstr                            => branches
    | RotateInstr theta phi lambda target => Execute_rotate_instr theta phi lambda target branches
    | CnotInstr control target            => Execute_cnot_instr control target branches
    | SwapInstr q1 q2                     => Execute_swap_instr q1 q2 branches
    | MeasureInstr qbit cbit              => Merge_program_state (Execute_measure_instr qbit cbit branches)
    | SeqInstr i1 i2                      => Execute_suppl_old ir' i2 (Execute_suppl_old ir' i1 branches)
    | IfInstr cbit cond subinstr          => (
        concat (map (fun b =>
          if (eqb (B_cstate b cbit) cond)
          then Execute_suppl_old ir' subinstr [b]
          else [b]) branches)
    )
    | ResetInstr target                   => Execute_reset_instr target branches
    end
  )
  end.

Fixpoint Execute_suppl (instr: Instruction) (branches: ProgramState): ProgramState :=
    match instr with
    | NopInstr                            => branches
    | RotateInstr theta phi lambda target => Execute_rotate_instr theta phi lambda target branches
    | CnotInstr control target            => Execute_cnot_instr control target branches
    | SwapInstr q1 q2                     => Execute_swap_instr q1 q2 branches
    | MeasureInstr qbit cbit              => Merge_program_state (Execute_measure_instr qbit cbit branches)
    | SeqInstr i1 i2                      => Execute_suppl i2 (Execute_suppl i1 branches)
    | IfInstr cbit cond subinstr          => (
        concat (map (fun b =>
          if (eqb (B_cstate b cbit) cond)
          then Execute_suppl subinstr [b]
          else [b]) branches)
    )
    | ResetInstr target                   => Execute_reset_instr target branches
    end.

Definition Execute (program: InlinedProgram): ProgramState :=
  Execute_suppl
    (IP_instrs program)
    (ProgramState_init nq (IP_num_cbits program)).

Fixpoint Cstate_to_binary_little_endian (n: nat) (cstate: total_map bool) (acc: nat): nat := match n with
  | O => acc
  | S n' => let bit := if (cstate n') then 1 else 0 in
            Cstate_to_binary_little_endian n' cstate (2 * acc + bit)
end.

Definition Cstate_to_binary (num_cbits: nat) (cstate: total_map bool) := Cstate_to_binary_little_endian num_cbits cstate O.

(*  0 -> true
    1 -> false     ===> 1011 (value of 0 is the leftmost bit in the result) (big endian)
    2 -> true      ===> In qasm, they use little endian so have to reverse it
    3 -> true *)


Fixpoint Calculate_prob (num_cbits: nat) (branches: ProgramState): total_map R :=
  match branches with
  | [] => tm_empty R0
  | b :: t =>
    let prev := Calculate_prob num_cbits t in
    let key := Cstate_to_binary num_cbits (B_cstate b) in
    tm_update prev key (prev key + B_prob b)%R
  end.

Definition Execute_and_calculate_prob (program: InlinedProgram): total_map R :=
  Calculate_prob (IP_num_cbits program) (Execute program).

(* ============================================================================================== *)
(* Proof about quantum states =================================================================== *)

Lemma Execute_rotate_instr_quantum_state_density:
  forall (theta phi lambda: R) (target: nat) (branches: ProgramState),
  Forall qstate_valid branches ->
  Forall qstate_valid (Execute_rotate_instr theta phi lambda target branches).
Proof.
  intros.
  induction branches.
  - apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec target nq).
    + apply Forall_cons; simpl.
      apply den_valid_uop.
      apply mat_single_unitary.
      apply mat_rot_unitary.
      assumption.
      apply IHbranches.
      apply Ht.
    + apply Forall_cons; simpl.
      apply H.
      apply IHbranches.
      apply Ht.
Qed.

Lemma Execute_cnot_instr_quantum_state_density:
  forall (control target: nat) (branches: ProgramState),
  Forall qstate_valid branches -> Forall qstate_valid (Execute_cnot_instr control target branches).
Proof.
  intros.
  induction branches.
  - apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (ge_dec nq 2), (lt_dec control nq), (lt_dec target nq).
    { apply Forall_cons.
      simpl.
      apply den_valid_uop.
      apply mat_cnot_unitary.
      assumption.
      apply IHbranches.
      apply Ht. }
      all: apply Forall_cons.
      all: simpl; try apply H.
      all: apply IHbranches.
      all: apply Ht.
Qed.

Lemma Execute_swap_instr_quantum_state_density:
  forall (q1 q2: nat) (branches: ProgramState),
  Forall qstate_valid branches -> Forall qstate_valid (Execute_swap_instr q1 q2 branches).
Proof.
  intros.
  induction branches.
  - apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec q1 nq), (lt_dec q2 nq).
    { apply Forall_cons.
      simpl.
      apply den_valid_uop.
      apply mat_swap_unitary.
      assumption.
      apply IHbranches.
      apply Ht. }
      all: apply Forall_cons.
      all: simpl; try apply H.
      all: apply IHbranches.
      all: apply Ht.
Qed.

Lemma Execute_measure_instr_quantum_state_density:
  forall (qbit cbit: nat) (branches: ProgramState),
  Forall qstate_valid branches -> Forall qstate_valid (Execute_measure_instr qbit cbit branches).
Proof.
  intros.
  induction branches.
  - apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec qbit nq).
    + destruct
      (Rgt_dec (com_real (den_prob_0 qbit B_qstate0)) 0),
      (Rgt_dec (com_real (den_prob_1 qbit B_qstate0)) 0).
      all: try repeat apply Forall_cons; simpl.
      all: unfold den_measure_0, den_measure_1 in *.
      all: try apply den_valid_measure.
      all: unfold den_prob_0, den_prob_1, den_prob in *.
      all: try apply H.
      all: try apply mat_proj0_projection; try apply mat_proj1_projection.
      all: unfold com_real in *.
      all: try apply com_proj_neq_fst.
      all: unfold NTC, INR; simpl; try lra.
      all: apply IHbranches.
      all: apply Ht.
    + apply IHbranches.
      apply Ht.
Qed.

Lemma Execute_reset_instr_quantum_state_density:
  forall (target: nat) (branches: ProgramState),
  Forall qstate_valid branches -> Forall qstate_valid (Execute_reset_instr target branches).
Proof.
  intros.
  induction branches.
  - simpl.
    apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec target nq).
    + apply Forall_cons.
      apply den_valid_reset.
      apply H.
      apply IHbranches.
      apply Ht.
    + apply Forall_cons.
      apply H.
      apply IHbranches.
      apply Ht.
Qed.

Lemma Execute_suppl_empty_branch: forall (instr: Instruction),
  Execute_suppl instr [] = [].
Proof.
  induction instr.
  all: try reflexivity.
  simpl.
  rewrite IHinstr1.
  rewrite IHinstr2.
  reflexivity.
Qed.

Lemma Execute_suppl_nop: forall (branches: ProgramState),
  Execute_suppl NopInstr branches = branches.
Proof.
  destruct branches.
  all: reflexivity.
Qed.

Arguments Execute_rotate_instr _ _ _ _ : simpl never.
Arguments Execute_cnot_instr _ _ _ : simpl never.
Arguments Execute_swap_instr _ _ _ : simpl never.
Arguments Execute_measure_instr _ _ _ : simpl never.

Lemma Execute_suppl_quantum_state_density:
  forall (instr: Instruction) (branches: ProgramState),
  Forall qstate_valid branches -> Forall qstate_valid (Execute_suppl instr branches).
Proof.
  induction instr.
  all: intros; simpl.
  - exact H.
  - apply Execute_rotate_instr_quantum_state_density; apply H.
  - apply Execute_cnot_instr_quantum_state_density; apply H.
  - apply Execute_swap_instr_quantum_state_density; apply H.
  - apply Merge_program_state_qstate_valid.
    apply Execute_measure_instr_quantum_state_density; apply H.
  - apply IHinstr2; apply IHinstr1; apply H.
  - apply Forall_concat.
    apply Forall_map.
    induction branches.
    + apply Forall_nil.
    + apply Forall_cons.
      * destruct (eqb (B_cstate a n) b).
        apply IHinstr.
        all: apply Forall_cons_iff in H.
        all: destruct H.
        all: apply Forall_cons.
        all: try apply H; try apply Forall_nil.
      * apply IHbranches.
        apply Forall_cons_iff in H.
        destruct H.
        apply H0.
  - simpl.
    apply Execute_reset_instr_quantum_state_density.
    apply H.
Qed.


Theorem Execute_quantum_state_density: forall (program: InlinedProgram),
  Forall qstate_valid (Execute program).
Proof.
  intros.
  unfold Execute.
  apply Execute_suppl_quantum_state_density.
  unfold ProgramState_init.
  apply Forall_cons.
  apply den_valid_init.
  apply Forall_nil.
Qed.

End PROGRAM.
