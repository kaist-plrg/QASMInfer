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

(* inlined QASM instructions ================================================================= *)

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
(* inlined QASM program ====================================================================== *)

Record InlinedProgram: Type := {
  IP_num_cbits: nat;
  IP_num_subinstrs: nat;  (* numbers of all subinstructions, to prove decreasing argument of fix *)
  IP_instrs: Instruction;
}.

(* ============================================================================================== *)
(* MWI for program states ======================================================================= *)

Record World: Type := {
  W_num_clbits: nat;
  W_qstate: Matrix nq; (* density matrix *)
  W_cstate: total_map bool;  (* false for 0, true for 1 *)
  W_prob: R; (* probability of the world *)
  W_prob_valid: (W_prob > 0)%R;
}.

Definition qstate_valid (w: World): Prop := den_valid (W_qstate w).

(* ============================================================================================== *)
(* ManyWorlds for program states =============================================================== *)

Definition ManyWorld: Type := list World.

Definition ManyWorld_init (num_q num_c: nat): ManyWorld.
Proof.
  refine ([{|
    W_num_clbits := num_c;
    W_qstate := den_init nq;
    W_cstate := tm_empty false;
    W_prob := 1;
  |}]).
  lra.
Defined.

(* ============================================================================================== *)
(* merging two worlds =========================================================================== *)

Definition Merge_world (w0 w1: World): World.
Proof.
  destruct w0 eqn:ew0, w1.
  destruct
    (Nat.eq_dec W_num_clbits0 W_num_clbits1),
    (tmb_equal W_cstate0 W_cstate1 W_num_clbits0) eqn:ec.
  subst W_num_clbits1.
  refine ({|
    W_num_clbits := W_num_clbits0;
    W_qstate := W_prob0 .* W_qstate0 + W_prob1 .* W_qstate1;
    W_cstate := W_cstate0;
    W_prob := W_prob0 + W_prob1;
  |}).
  lra.
  all: exact w0.
Defined.

Definition Merge_manyworld_suppl (w: World) (mw: ManyWorld): ManyWorld.
Proof.
  induction mw.
  - exact [w].
  - destruct
    (tmb_equal (W_cstate a) (W_cstate w) (W_num_clbits a)).
    destruct w as [nc qst cst p pv], a as [nc' qst' cst' p' pv']; simpl in *.
    refine ({|
      W_num_clbits := nc;
      W_qstate := (p / (p + p'))%com .* qst + (p' / (p + p'))%com .* qst';
      W_cstate := cst;
      W_prob := p + p';
    |} :: mw). (* merge *)
      lra.
    exact (a :: IHmw). (* nop *)
Defined.

Definition Merge_manyworld (mw: ManyWorld): ManyWorld.
Proof.
  destruct mw.
  - exact [].
  - destruct mw.
    + exact (Merge_manyworld_suppl w []).
    + exact (Merge_manyworld_suppl w (Merge_manyworld_suppl w0 mw)).
Defined.

Lemma Merge_manyworld_suppl_qstate_valid:
  forall (w: World) (mw: ManyWorld),
  den_valid (W_qstate w) -> Forall qstate_valid mw -> Forall qstate_valid (Merge_manyworld_suppl w mw).
Proof.
  induction mw.
  - intros; simpl.
    apply Forall_cons.
    apply H.
    apply Forall_nil.
  - intros; simpl.
    apply Forall_cons_iff in H0.
    destruct H0.
    destruct (tmb_equal (W_cstate a) (W_cstate w) (W_num_clbits a)).
    + destruct w as [nc qst cst p pv], a as [nc' qst' cst' p' pv']; simpl in *.
      apply Forall_cons.
      * apply den_valid_mix.
        all: assumption.
      * apply H1.
    + apply Forall_cons; auto; auto.
Qed.

Lemma Merge_manyworld_qstate_valid:
  forall (worlds: ManyWorld),
  Forall qstate_valid worlds -> Forall qstate_valid (Merge_manyworld worlds).
Proof.
  intros; simpl.
  induction worlds as [|w0[|w1 t] ].
  - apply Forall_nil.
  - apply H.
  - apply Forall_cons_iff in H; destruct H.
    apply Forall_cons_iff in H0; destruct H0.
    apply Merge_manyworld_suppl_qstate_valid.
    all: auto.
    apply Merge_manyworld_suppl_qstate_valid.
    all: auto.
Qed.

(* ============================================================================================== *)
(* execution ==================================================================================== *)

Fixpoint Execute_rotate_instr (theta phi lambda: R) (target: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec target nq).
    + exact ({|
        W_num_clbits := nc;
        W_qstate := den_uop (mat_single nq target (mat_rot theta phi lambda)) qstate ;
        W_cstate := cstate;
        W_prob := prob;
        W_prob_valid := Hp;
      |} :: (Execute_rotate_instr theta phi lambda target t)).
    + exact ({|
        W_num_clbits := nc;
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_prob_valid := Hp;
      |} :: (Execute_rotate_instr theta phi lambda target t)).  (* nop *)
Defined.

Fixpoint Execute_cnot_instr (control target: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (ge_dec nq 2), (lt_dec control nq), (lt_dec target nq).
    exact ({|
      W_num_clbits := nc;
      W_qstate := den_uop (mat_cnot control target) qstate;
      W_cstate := cstate;
      W_prob := prob;
      W_prob_valid := Hp;
      |} :: (Execute_cnot_instr control target t)).
    all: refine ({|
      W_num_clbits := nc;
      W_qstate := qstate;
      W_cstate := cstate;
      W_prob := prob;
      W_prob_valid := Hp;
    |} :: (Execute_cnot_instr control target t)).  (* nop *)
Defined.

Fixpoint Execute_swap_instr (q1 q2: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec q1 nq), (lt_dec q2 nq).
    exact ({|
      W_num_clbits := nc;
      W_qstate := den_uop (mat_swap q1 q2) qstate;
      W_cstate := cstate;
      W_prob := prob;
      W_prob_valid := Hp;
      |} :: (Execute_swap_instr q1 q2 t)).
    all: exact ({|
        W_num_clbits := nc;
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_prob_valid := Hp;
      |} :: (Execute_swap_instr q1 q2 t)).  (* nop *)
Defined.

Fixpoint Execute_measure_instr (qbit cbit: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec qbit nq).
    + specialize (com_real (den_prob_0 qbit qstate)) as prob0.
      specialize (com_real (den_prob_1 qbit qstate)) as prob1.
      destruct (Rgt_dec prob0 0), (Rgt_dec prob1 0).
      * refine ({|
          W_num_clbits := nc;
          W_qstate := den_measure_0 qbit qstate;
          W_cstate := tm_update cstate cbit false;
          W_prob := prob * prob0;
        |} :: {|
          W_num_clbits := nc;
          W_qstate := den_measure_1 qbit qstate;
          W_cstate := tm_update cstate cbit true;
          W_prob := prob * prob1;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        all: try nra.
      * refine ({|
          W_num_clbits := nc;
          W_qstate := den_measure_0 qbit qstate;
          W_cstate := tm_update cstate cbit false;
          W_prob := prob * prob0;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        nra.
      * refine ({|
          W_num_clbits := nc;
          W_qstate := den_measure_1 qbit qstate;
          W_cstate := tm_update cstate cbit true;
          W_prob := prob * prob1;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        nra.
      * exact (Execute_measure_instr qbit cbit t).  (* nop *)
  + exact (Execute_measure_instr qbit cbit t).  (* nop *)
Defined.

Fixpoint Execute_reset_instr (target: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[nc qstate cstate prob Hp] t].
  - exact [].
  - destruct (lt_dec target nq).
    + exact ({|
        W_num_clbits := nc;
        W_qstate := den_reset target qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_prob_valid := Hp;
      |} :: (Execute_reset_instr target t)).
    + exact ({|
        W_num_clbits := nc;
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_prob_valid := Hp;
      |} :: (Execute_reset_instr target t)).  (* nop *)
Defined.

Fixpoint Execute_suppl (ir: nat) (instr: Instruction) (worlds: ManyWorld): ManyWorld :=
  match ir with
  | O => worlds
  | S ir' => (
    match instr with
    | NopInstr                            => worlds
    | RotateInstr theta phi lambda target => Execute_rotate_instr theta phi lambda target worlds
    | CnotInstr control target            => Execute_cnot_instr control target worlds
    | SwapInstr q1 q2                     => Execute_swap_instr q1 q2 worlds
    | MeasureInstr qbit cbit              => Merge_manyworld (Execute_measure_instr qbit cbit worlds)
    | SeqInstr i1 i2                      => Execute_suppl ir' i2 (Execute_suppl ir' i1 worlds)
    | IfInstr cbit cond subinstr          => (
        concat (map (fun w =>
          if (eqb (W_cstate w cbit) cond)
          then Execute_suppl ir' subinstr [w]
          else [w]) worlds)
    )
    | ResetInstr target                   => Execute_reset_instr target worlds
    end
  )
  end.

Definition Execute (program: InlinedProgram): ManyWorld :=
  Execute_suppl
    (IP_num_subinstrs program)
    (IP_instrs program)
    (ManyWorld_init nq (IP_num_cbits program)).

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


Fixpoint Calculate_prob (num_cbits: nat) (worlds: ManyWorld): total_map R :=
  match worlds with
  | [] => tm_empty R0
  | w :: t =>
    let prev := Calculate_prob num_cbits t in
    let key := Cstate_to_binary num_cbits (W_cstate w) in
    tm_update prev key (prev key + W_prob w)%R
  end.

Definition Execute_and_calculate_prob (program: InlinedProgram): total_map R :=
  Calculate_prob (IP_num_cbits program) (Execute program).

(* ============================================================================================== *)
(* Proof about quantum states =================================================================== *)

Lemma Execute_rotate_instr_quantum_state_density:
  forall (theta phi lambda: R) (target: nat) (worlds: ManyWorld),
  Forall qstate_valid worlds ->
  Forall qstate_valid (Execute_rotate_instr theta phi lambda target worlds).
Proof.
  intros.
  induction worlds.
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
      apply IHworlds.
      apply Ht.
    + apply Forall_cons; simpl.
      apply H.
      apply IHworlds.
      apply Ht.
Qed.

Lemma Execute_cnot_instr_quantum_state_density:
  forall (control target: nat) (worlds: ManyWorld),
  Forall qstate_valid worlds -> Forall qstate_valid (Execute_cnot_instr control target worlds).
Proof.
  intros.
  induction worlds.
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
      apply IHworlds.
      apply Ht. }
      all: apply Forall_cons.
      all: simpl; try apply H.
      all: apply IHworlds.
      all: apply Ht.
Qed.

Lemma Execute_swap_instr_quantum_state_density:
  forall (q1 q2: nat) (worlds: ManyWorld),
  Forall qstate_valid worlds -> Forall qstate_valid (Execute_swap_instr q1 q2 worlds).
Proof.
  intros.
  induction worlds.
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
      apply IHworlds.
      apply Ht. }
      all: apply Forall_cons.
      all: simpl; try apply H.
      all: apply IHworlds.
      all: apply Ht.
Qed.

Lemma Execute_measure_instr_quantum_state_density:
  forall (qbit cbit: nat) (worlds: ManyWorld),
  Forall qstate_valid worlds -> Forall qstate_valid (Execute_measure_instr qbit cbit worlds).
Proof.
  intros.
  induction worlds.
  - apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec qbit nq).
    + destruct
      (Rgt_dec (com_real (den_prob_0 qbit W_qstate0)) 0),
      (Rgt_dec (com_real (den_prob_1 qbit W_qstate0)) 0).
      all: try repeat apply Forall_cons; simpl.
      all: unfold den_measure_0, den_measure_1 in *.
      all: try apply den_valid_measure.
      all: unfold den_prob_0, den_prob_1, den_prob in *.
      all: try apply H.
      all: try apply mat_proj0_projection; try apply mat_proj1_projection.
      all: unfold com_real in *.
      all: try apply com_proj_neq_fst.
      all: unfold NTC, INR; simpl; try lra.
      all: apply IHworlds.
      all: apply Ht.
    + apply IHworlds.
      apply Ht.
Qed.

Lemma Execute_reset_instr_quantum_state_density:
  forall (target: nat) (worlds: ManyWorld),
  Forall qstate_valid worlds -> Forall qstate_valid (Execute_reset_instr target worlds).
Proof.
  intros.
  induction worlds.
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
      apply IHworlds.
      apply Ht.
    + apply Forall_cons.
      apply H.
      apply IHworlds.
      apply Ht.
Qed.

Lemma Execute_suppl_empty_world: forall (ir: nat) (instr: Instruction),
  Execute_suppl ir instr [] = [].
Proof.
  induction ir, instr.
  all: try reflexivity.
  simpl.
  repeat rewrite IHir.
  reflexivity.
Qed.

Lemma Execute_suppl_nop: forall (ir: nat) (worlds: ManyWorld),
  Execute_suppl ir NopInstr worlds = worlds.
Proof.
  destruct ir, worlds.
  all: reflexivity.
Qed.

Arguments Execute_rotate_instr _ _ _ _ : simpl never.
Arguments Execute_cnot_instr _ _ _ : simpl never.
Arguments Execute_swap_instr _ _ _ : simpl never.
Arguments Execute_measure_instr _ _ _ : simpl never.

Lemma Execute_suppl_quantum_state_density:
  forall (ir: nat) (instr: Instruction) (worlds: ManyWorld),
  Forall qstate_valid worlds -> Forall qstate_valid (Execute_suppl ir instr worlds).
Proof.
  intros ir instr.
  revert ir.
  induction instr.
  all: intros; destruct ir; [simpl; apply H|].
  - rewrite Execute_suppl_nop.
    apply H.
  - apply Execute_rotate_instr_quantum_state_density; apply H.
  - apply Execute_cnot_instr_quantum_state_density; apply H.
  - apply Execute_swap_instr_quantum_state_density; apply H.
  - apply Merge_manyworld_qstate_valid.
    apply Execute_measure_instr_quantum_state_density; apply H.
  - apply IHinstr2; apply IHinstr1; apply H.
  - apply Forall_concat.
    apply Forall_map.
    induction worlds.
    + apply Forall_nil.
    + apply Forall_cons.
      * destruct (eqb (W_cstate a n) b).
        apply IHinstr.
        all: apply Forall_cons_iff in H.
        all: destruct H.
        all: apply Forall_cons.
        all: try apply H; try apply Forall_nil.
      * apply IHworlds.
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
  unfold ManyWorld_init.
  apply Forall_cons.
  apply den_valid_init.
  apply Forall_nil.
Qed.

End PROGRAM.
