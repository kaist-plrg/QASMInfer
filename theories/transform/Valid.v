Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.

From Stdlib Require Import List.
From Stdlib.FSets Require Import FMapPositive FMapFacts.

Module PFacts := WFacts_fun PositiveMap.E PositiveMap.
Module PProperties := WProperties_fun PositiveMap.E PositiveMap.

Section ValidPS.

  Variable nq : nat. (* number of qubits *)

  Definition ValidBranch: Type :=
    { b: Branch nq | Branch_valid nq b }.

  Definition ValidProgramState: Type := PositiveMap.t ValidBranch.

  Definition ValidProgramState_proj (vps: ValidProgramState): ProgramState nq :=
    PositiveMap.map (fun vb => (proj1_sig vb)) vps.
  
  Lemma ValidProgramState_proj_proof (vps: ValidProgramState):
    ProgramState_valid nq (ValidProgramState_proj vps).
  Proof.
    intros cstate branch Hmapsto.
    apply PositiveMap.find_1 in Hmapsto.
    unfold ValidProgramState_proj in Hmapsto.
    rewrite PFacts.map_o in Hmapsto.
    destruct (@PositiveMap.find (@sig (Branch nq) (fun b : Branch nq => Branch_valid nq b)) cstate vps) eqn:E.
    - simpl in Hmapsto.
      inversion Hmapsto.
      exact (proj2_sig s).
    - simpl in Hmapsto.
      discriminate.
  Qed.

  Definition ValidProgramState_construct
    (ps : ProgramState nq) (valid : ProgramState_valid nq ps)
    : ValidProgramState.
  Proof.
    refine (
      let fix go (ps : ProgramState nq)
      : ProgramState_valid nq ps -> ValidProgramState :=
        match ps return ProgramState_valid nq ps -> ValidProgramState with
        | PositiveMap.Leaf _ =>
          fun _ => @PositiveMap.Leaf ValidBranch
        | PositiveMap.Node l o r =>
          fun valid0 =>
            PositiveMap.Node
            (go l _)
            _
            (go r _)
        end
      in go ps valid).
    - (* left subtree *)
      intros k b Hm.
      apply (valid0 (xO k) b).
      apply PositiveMap.find_2.
      simpl.
      apply PositiveMap.find_1.
      exact Hm.
    - (* current node *)
      destruct o as [b |].
      + refine (Some (exist _ b _)).
        apply (valid0 xH b).
        apply PositiveMap.find_2.
        simpl.
        reflexivity.
      + exact None.
    - (* right subtree *)
      intros k b Hm.
      apply (valid0 (xI k) b).
      apply PositiveMap.find_2.
      simpl.
      apply PositiveMap.find_1.
      exact Hm.
  Defined.

  Definition ValidProgramState_equiv (vps1 vps2: ValidProgramState): Prop :=
    ProgramState_equiv nq (ValidProgramState_proj vps1) (ValidProgramState_proj vps2).

  Definition ValidProgramState_merge (vps1 vps2: ValidProgramState): ValidProgramState.
  Proof.
    apply ValidProgramState_construct with
      (ps := ProgramState_merge nq (ValidProgramState_proj vps1) (ValidProgramState_proj vps2)).
    apply ProgramState_merge_valid.
    apply ValidProgramState_proj_proof.
    apply ValidProgramState_proj_proof.
  Qed.

  Lemma ValidProgramState_equiv_equivalence:
    Equivalence ValidProgramState_equiv.
  Proof.
    constructor.
    - intros vps. apply ProgramState_equiv_equivalence.
    - intros vps1 vps2 H.
      apply ProgramState_equiv_equivalence.
      apply H.
    - intros vps1 vps2 vps3 H1 H2.
      apply ProgramState_equiv_equivalence with (y := (ValidProgramState_proj vps2)).
      apply H1. apply H2.
  Qed.

  Lemma PositiveMap_map_step :
    forall f l o r,
      ProgramState_equiv nq
      (PositiveMap.map f (PositiveMap.Node l o r))
      (PositiveMap.Node (@PositiveMap.map (ValidBranch) _ f l) (Datatypes.option_map f o) (PositiveMap.map f r)).
  Proof.
    intros.
    intros cstate.
    rewrite PFacts.map_o.
    destruct cstate; simpl.
    - rewrite PFacts.map_o. reflexivity.
    - rewrite PFacts.map_o. reflexivity.
    - reflexivity.
  Qed.

  Lemma ValidProgramState_proj_construct :
    forall (ps: ProgramState nq) (Hvalid: ProgramState_valid nq ps),
      ProgramState_equiv nq
      (ValidProgramState_proj (ValidProgramState_construct ps Hvalid))
      ps.
  Proof.
    intros ps.
    unfold ValidProgramState_proj, ValidProgramState_construct.
    induction ps; intros Hvalid.
    - intros cstate.
      rewrite PFacts.map_o.
      repeat rewrite PFacts.empty_o.
      reflexivity.
    - rewrite PositiveMap_map_step.
      intros cstate; destruct cstate; simpl.
      + erewrite IHps2. reflexivity.
      + erewrite IHps1. reflexivity.
      + destruct o; simpl; reflexivity.
  Qed.

  Lemma ValidProgramState_rewrite:
    forall (ps1 ps2: ProgramState nq)
    (Hvalid1: ProgramState_valid nq ps1)
    (Hvalid2: ProgramState_valid nq ps2),
    ProgramState_equiv nq ps1 ps2 <->
    ValidProgramState_equiv
    (ValidProgramState_construct ps1 Hvalid1)
    (ValidProgramState_construct ps2 Hvalid2).
  Proof.
    intros.
    unfold ValidProgramState_equiv.
    repeat rewrite ValidProgramState_proj_construct.
    reflexivity.
  Qed.

  Lemma ValidProgramState_merge_rewrite:
    forall (ps1 ps2: ProgramState nq)
    (Hvalid1: ProgramState_valid nq ps1)
    (Hvalid2: ProgramState_valid nq ps2),
    ValidProgramState_equiv
    (ValidProgramState_construct (ProgramState_merge nq ps1 ps2) (ProgramState_merge_valid nq ps1 ps2 Hvalid1 Hvalid2))
    (ValidProgramState_merge (ValidProgramState_construct ps1 Hvalid1) (ValidProgramState_construct ps2 Hvalid2)).
  Proof.
    intros.
    unfold ValidProgramState_equiv.
    rewrite ValidProgramState_proj_construct.
  Admitted.

End ValidPS.