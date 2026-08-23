Require Import QASMInfer.program.All.
Require Import QASMInfer.transform.Equiv.
Require Import QASMInfer.transform.Transform.


From Stdlib Require Import String.
From Stdlib Require Import List.
Open Scope nat_scope.
Bind Scope nat_scope with nat.
Open Scope R_scope.
Import List.ListNotations.
Open Scope list_scope.

Section FLATTEN_FUNCTION.

Fixpoint flatten_core (instr : Instruction) : Instruction :=
  match instr with
  | SeqInstr instrs =>
      fold_right
        (fun instr acc =>
           qasm_seq (flatten_core instr) acc)
        (SeqInstr [])
        instrs
  | IfInstr c b body =>
      IfInstr c b (flatten_core body)
  | _ =>
      instr
  end.

Lemma Instruction_equiv_flatten:
  forall (nq: nat) (instr: Instruction),
  Instruction_equiv nq
  instr
  (flatten_core instr).
Proof.
  intros nq.
  apply Instruction_ind'; simpl; intros; try reflexivity.
  - induction is; try reflexivity; simpl.
    inversion H; subst.
    rewrite Instruction_equiv_Seq_list_eq.
    transitivity (qasm{ ($(flatten_core a)); seq[ is ]}). {
      apply Instruction_equiv_rewrite_start.
      apply H2.
    }
    apply Instruction_equiv_rewrite_end.
    apply IHis.
    apply H3.
  - apply Instruction_if_Proper.
    apply H.
Qed.

End FLATTEN_FUNCTION.
