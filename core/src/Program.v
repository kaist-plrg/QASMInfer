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
| NopInstr: Instruction
| RotateInstr: R -> R -> R -> nat -> Instruction  (* U (theta phi lambda) qbit *)
| CnotInstr: nat -> nat -> Instruction  (* CnotInstr a b: flip b iff a *)
| SwapInstr: nat -> nat -> Instruction  (* SwapInstr a b: swap a b *)
| MeasureInstr: nat -> nat -> Instruction  (* MeasureInstr q c: *)
| SeqInstr: Instruction -> Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction  (* if cbit == 0 (false) or cbit == 1 (true) *)
| ResetInstr: nat -> Instruction.  (* reset qbit to 0 *)


(* ============================================================================================== *)
(* inlined QASM2.0 program ====================================================================== *)

Record InlinedProgram: Type := {
  IP_num_qbits: nat;
  IP_num_cbits: nat;
  IP_num_subinstrs: nat;  (* numbers of all subinstructions, to prove decreasing argument of fix *)
  IP_instrs: Instruction;
}.

(* ============================================================================================== *)
(* MWI for program states ======================================================================= *)

Record World: Type := {
  W_qstate: Matrix; (* density matrix *)
  W_cstate: total_map bool;  (* false for 0, true for 1 *)
  W_prob: R; (* probability of the world *)
  W_num_qubits: nat;
  W_qstate_valid: Mbits W_qstate = W_num_qubits;
  W_prob_valid: (W_prob > 0)%R;
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
  lra.
Defined.

(* ============================================================================================== *)
(* merging two worlds =========================================================================== *)

Definition Merge_world (w1 w2: World): World.
Proof.
  destruct (Nat.eq_dec (w1.(W_num_qubits)) (w2.(W_num_qubits))).
  - destruct (tmb_equal (w1.(W_cstate)) (w2.(W_cstate)) (w1.(W_num_qubits))) eqn:ec.
    + refine ({|
        W_qstate := Den_mix w1.(W_qstate) w2.(W_qstate)  w1.(W_prob) w2.(W_prob) _;
        W_cstate := w1.(W_cstate);
        W_prob := w1.(W_prob) + w2.(W_prob);
        W_num_qubits := w1.(W_num_qubits);
      |}).
      rewrite Den_mix_bits.
      destruct w1; simpl; lia.
      destruct w1, w2; simpl in *; lra.
      Unshelve.
      destruct w1, w2; simpl in *; lia.
    + exact w1.
  - exact w1.
Defined.

Definition Merge_manyworld_suppl (w: World) (mw: ManyWorld): ManyWorld.
Proof.
  induction mw.
  - exact [w].
  - destruct (Nat.eq_dec (W_num_qubits a) (W_num_qubits w)).
    + destruct (tmb_equal (W_cstate a) (W_cstate w) (W_num_qubits a)).
      * refine ({|
          W_qstate := Den_mix (W_qstate a) (W_qstate w) (W_prob a) (W_prob w) _;
          W_cstate := W_cstate a;
          W_prob := W_prob a + W_prob w;
          W_num_qubits := W_num_qubits a;
        |} :: mw). (* merge *)
        Unshelve.
        all: destruct w, a; simpl in *; try lia; try lra.
      * exact (a :: IHmw).
    + exact (a :: IHmw).
Defined.

Definition Merge_manyworld (mw: ManyWorld): ManyWorld.
Proof.
  induction mw.
  - exact [].
  - exact (Merge_manyworld_suppl a mw).
Defined.

Lemma Merge_manyworld_suppl_quantum_state_density:
  forall (w: World) (mw: ManyWorld) (n: nat),
  DensityMatrix n (W_qstate w) ->
  Forall (fun world => DensityMatrix n (W_qstate world)) mw ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Merge_manyworld_suppl w mw).
Proof.
  induction mw.
  - intros.
    simpl.
    apply Forall_cons.
    apply H.
    apply Forall_nil.
  - intros.
    simpl.
    apply Forall_cons_iff in H0.
    destruct H0.
    destruct (Nat.eq_dec (W_num_qubits a) (W_num_qubits w)), (tmb_equal (W_cstate a) (W_cstate w) (W_num_qubits a)).
    + apply Forall_cons.
      * simpl.
        apply DensityMatrix_mix.
        all: destruct w, a; simpl; try lra; auto.
      * apply H1.
    + all: apply Forall_cons; auto; auto.
    + all: apply Forall_cons; auto; auto.
    + all: apply Forall_cons; auto; auto.
Qed.

Lemma Merge_manyworld_quantum_state_density:
  forall (worlds: ManyWorld) (n: nat),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Merge_manyworld worlds).
Proof.
  induction worlds.
  - intros.
    simpl.
    apply Forall_nil.
  - intros.
    apply Forall_cons_iff in H; destruct H.
    apply Merge_manyworld_suppl_quantum_state_density.
    all: auto.
Qed.

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
      lra.
      apply Qop_rot_bits.
      simpl_bits.
      rewrite Qop_sq_bits.
      lia.
      simpl_bits.
      reflexivity.
    + refine ({|
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_num_qubits := nq;
        W_qstate_valid := Hq;
      |} :: (Execute_rotate_instr theta phi lambda target t)).  (* nop *)
      lra.
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
    3-9: refine ({|
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_num_qubits := nq;
        W_qstate_valid := Hq;
      |} :: (Execute_cnot_instr control target t)).  (* nop *)
    Unshelve.
    all: try lra.
    rewrite Den_unitary_bits.
    apply Hq.
    simpl_bits.
    rewrite Qop_cnot_bits.
    lia.
    simpl_bits.
    reflexivity.
Defined.

Fixpoint Execute_swap_instr (q1 q2: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  - exact [].
  - destruct (lt_dec q1 nq), (lt_dec q2 nq).
    refine ({|
      W_qstate := Den_unitary qstate (Qop_swap nq q1 q2 l l0) _ _;
      W_cstate := cstate;
      W_prob := prob;
      W_num_qubits := nq;
      |} :: (Execute_swap_instr q1 q2 t)).
    3-5: refine ({|
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_num_qubits := nq;
        W_qstate_valid := Hq;
      |} :: (Execute_swap_instr q1 q2 t)).  (* nop *)
    Unshelve.
    all: try lra.
    rewrite Den_unitary_bits.
    apply Hq.
    simpl_bits.
    rewrite Qop_swap_bits.
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
        all: try nra.
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
        nra.
      * refine ({|
          W_qstate := Den_measure_1 qstate nq qbit l Hq;
          W_cstate := tm_update cstate cbit true;
          W_prob := prob * prob1;
          W_num_qubits := nq;
        |} ::
        (Execute_measure_instr qbit cbit t)).
        apply Den_measure_1_bits.
        nra.
      * apply (Execute_measure_instr qbit cbit t).  (* nop *)
  + apply (Execute_measure_instr qbit cbit t).  (* nop *)
Defined.

Fixpoint Execute_reset_instr (target: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  - exact [].
  - destruct (lt_dec target nq).
    + refine ({|
        W_qstate := Den_reset qstate target _;
        W_cstate := cstate;
        W_prob := prob;
        W_num_qubits := nq;
      |} :: (Execute_reset_instr target t)).
      Unshelve.
      all: try lra; try lia.
      rewrite Den_reset_bits.
      apply Hq.
    + refine ({|
        W_qstate := qstate;
        W_cstate := cstate;
        W_prob := prob;
        W_num_qubits := nq;
        W_qstate_valid := Hq;
      |} :: (Execute_reset_instr target t)).  (* nop *)
      lra.
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
    (ManyWorld_init (IP_num_qbits program) (IP_num_cbits program)).

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
  forall (theta phi lambda: R) (n target: nat) (worlds: ManyWorld),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Execute_rotate_instr theta phi lambda target worlds).
Proof.
  intros.
  induction worlds.
  - simpl.
    apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec target (W_num_qubits0)).
    + apply Forall_cons.
      simpl.
      apply DensityMatrix_unitary.
      apply H.
      apply Qop_sq_unitary.
      apply Qop_rot_unitary.
      apply IHworlds.
      apply Ht.
    + apply Forall_cons.
      simpl.
      apply H.
      apply IHworlds.
      apply Ht.
Qed.

Lemma Execute_cnot_instr_quantum_state_density:
  forall (n control target: nat) (worlds: ManyWorld),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Execute_cnot_instr control target worlds).
Proof.
  intros.
  induction worlds.
  - simpl.
    apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (ge_dec W_num_qubits0 2), (lt_dec control W_num_qubits0), (lt_dec target W_num_qubits0).
    { apply Forall_cons.
      simpl.
      apply DensityMatrix_unitary.
      apply H.
      apply Qop_cnot_unitary.
      apply IHworlds.
      apply Ht. }
      all: apply Forall_cons.
      all: simpl; try apply H.
      all: apply IHworlds.
      all: apply Ht.
Qed.

Lemma Execute_swap_instr_quantum_state_density:
  forall (n q1 q2: nat) (worlds: ManyWorld),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Execute_swap_instr q1 q2 worlds).
Proof.
  intros.
  induction worlds.
  - simpl.
    apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec q1 W_num_qubits0), (lt_dec q2 W_num_qubits0).
    { apply Forall_cons.
      simpl.
      apply DensityMatrix_unitary.
      apply H.
      apply Qop_swap_unitary.
      apply IHworlds.
      apply Ht. }
      all: apply Forall_cons.
      all: simpl; try apply H.
      all: apply IHworlds.
      all: apply Ht.
Qed.

Lemma Execute_measure_instr_quantum_state_density:
  forall (n qbit cbit: nat) (worlds: ManyWorld),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Execute_measure_instr qbit cbit worlds).
Proof.
  intros.
  induction worlds.
  - simpl.
    apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    specialize DensityMatrix_prob_pos as Hpos.
    destruct (lt_dec qbit W_num_qubits0).
    + destruct
      (Rgt_dec (Creal (Den_prob_0 W_qstate0 W_num_qubits0 qbit l W_qstate_valid0)) 0),
      (Rgt_dec (Creal (Den_prob_1 W_qstate0 W_num_qubits0 qbit l W_qstate_valid0)) 0).
      all: try repeat apply Forall_cons; simpl.
      all: unfold Den_measure_0, Den_measure_1 in *.
      all: try apply DensityMatrix_measure.
      all: unfold Den_prob_0, Den_prob_1, Den_prob, Mmult in *.
      all: try apply H.
      all: try apply Qproj0_n_t_proj.
      all: try apply Qproj1_n_t_proj.
      all: unfold Creal in *.
      all: try apply c_proj_neq_fst.
      all: unfold NTC, INR; simpl.
      all: try lra.
      all: apply IHworlds.
      all: apply Ht.
    + apply IHworlds.
      apply Ht.
Qed.

Lemma Execute_reset_instr_quantum_state_density:
  forall (n target: nat) (worlds: ManyWorld),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world))
    (Execute_reset_instr target worlds).
Proof.
  intros.
  induction worlds.
  - simpl.
    apply H.
  - destruct a.
    apply Forall_cons_iff in H.
    destruct H as [H Ht].
    simpl in *.
    destruct (lt_dec target (W_num_qubits0)).
    + apply Forall_cons.
      simpl.
      apply DensityMatrix_reset.
      apply H.
      apply IHworlds.
      apply Ht.
    + apply Forall_cons.
      simpl.
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
  forall (n ir: nat) (instr: Instruction) (worlds: ManyWorld),
  Forall (fun world => DensityMatrix n (W_qstate world)) worlds ->
  Forall (fun world => DensityMatrix n (W_qstate world)) (Execute_suppl ir instr worlds).
Proof.
  intros n ir instr.
  revert ir.
  induction instr.
  all: intros; destruct ir; [simpl; apply H|].
  - rewrite Execute_suppl_nop.
    apply H.
  - simpl.
    apply Execute_rotate_instr_quantum_state_density.
    apply H.
  - simpl.
    apply Execute_cnot_instr_quantum_state_density.
    apply H.
  - simpl.
    apply Execute_swap_instr_quantum_state_density.
    apply H.
  - simpl.
    apply Merge_manyworld_quantum_state_density.
    apply Execute_measure_instr_quantum_state_density.
    apply H.
  - simpl.
    apply IHinstr2.
    apply IHinstr1.
    apply H.
  - simpl.
    apply Forall_concat.
    apply Forall_map.
    induction worlds.
    + apply Forall_nil.
    + apply Forall_cons.
      * destruct (eqb (W_cstate a n0) b).
        { apply IHinstr.
          apply Forall_cons_iff in H.
          destruct H.
          apply Forall_cons.
          apply H.
          apply Forall_nil. }
        { apply Forall_cons_iff in H.
          destruct H.
          apply Forall_cons.
          apply H.
          apply Forall_nil. }
      * apply IHworlds.
        apply Forall_cons_iff in H.
        destruct H.
        apply H0.
  - simpl.
    apply Execute_reset_instr_quantum_state_density.
    apply H.
Qed.


Theorem Execute_quantum_state_density: forall (program: InlinedProgram), exists (n: nat),
  Forall (fun world => DensityMatrix n (W_qstate world)) (Execute program).
Proof.
  intros.
  destruct program.
  unfold Execute.
  simpl.
  exists IP_num_qbits0.
  apply Execute_suppl_quantum_state_density.
  unfold ManyWorld_init.
  apply Forall_cons.
  simpl.
  apply Den_0_init_DensityMatrix.
  apply Forall_nil.
Qed.
