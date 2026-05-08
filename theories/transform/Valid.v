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

  Definition ValidProgramState_merge (vps1 vps2: ValidProgramState) : ValidProgramState :=
    ValidProgramState_construct
      (ProgramState_merge nq (ValidProgramState_proj vps1) (ValidProgramState_proj vps2))
      (ProgramState_merge_valid nq
        (ValidProgramState_proj vps1)
        (ValidProgramState_proj vps2)
        (ValidProgramState_proj_proof vps1)
        (ValidProgramState_proj_proof vps2)).

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

  Lemma ValidProgramState_construct_MapsTo_inv :
  forall k vb m (Hm : ProgramState_valid nq m),
    PositiveMap.MapsTo k vb (ValidProgramState_construct m Hm) ->
    PositiveMap.MapsTo k (proj1_sig vb) m.
  Proof.
    intros k vb m Hm Hmapsto.
    destruct vb. simpl.
    destruct m.
    - simpl in *.
  Admitted.

  Lemma ValidProgramState_proj_empty :
    ProgramState_equiv nq
      (ValidProgramState_proj (@PositiveMap.empty ValidBranch))
      (PositiveMap.empty (Branch nq)).
  Proof.
    intro cstate.
    repeat rewrite PFacts.empty_o.
    reflexivity.
  Qed.

  Lemma ValidProgramState_proj_add :
    forall (vps: ValidProgramState) k vb,
      ProgramState_equiv nq
        (ValidProgramState_proj (PositiveMap.add k vb vps))
        (PositiveMap.add k (proj1_sig vb) (ValidProgramState_proj vps)).
  Proof.
    intros vps k vb cstate.
    unfold ValidProgramState_proj.
    rewrite PFacts.map_o.
    repeat rewrite PFacts.add_o.
    destruct (PositiveMap.E.eq_dec k cstate).
    - reflexivity.
    - rewrite PFacts.map_o.
      reflexivity.
  Qed.

  Lemma ValidProgramState_in_iff :
    forall (vps: ValidProgramState) k,
      PositiveMap.In k vps <-> PositiveMap.In k (ValidProgramState_proj vps).
  Proof.
    intros.
    symmetry.
    apply PFacts.map_in_iff.
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

  Corollary ValidProgramState_proof_irrel:
    forall (ps: ProgramState nq)
    (Hvalid1 Hvalid2: ProgramState_valid nq ps),
    ValidProgramState_equiv
    (ValidProgramState_construct ps Hvalid1)
    (ValidProgramState_construct ps Hvalid2).
  Proof.
    intros.
    rewrite <- ValidProgramState_rewrite.
    reflexivity.
  Qed.

  Lemma ValidProgramState_merge_Proper:
    Proper (ValidProgramState_equiv ==> ValidProgramState_equiv ==> ValidProgramState_equiv)
    ValidProgramState_merge.
  Proof.
    intros x0 x1 Hx y0 y1 Hy.
    unfold ValidProgramState_equiv, ValidProgramState_merge.
    repeat rewrite ValidProgramState_proj_construct.
    apply ProgramState_merge_Proper.
    apply Hx. apply Hy.
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
    unfold ValidProgramState_equiv, ValidProgramState_merge.
    repeat rewrite ValidProgramState_proj_construct.
    apply ProgramState_merge_Proper.
    all: rewrite ValidProgramState_proj_construct.
    all: reflexivity.
  Qed.

  Variable F : PositiveMap.key -> Branch nq -> ProgramState nq.

  Hypothesis F_valid :
    forall k b,
      Branch_valid nq b ->
      ProgramState_valid nq (F k b).

  Definition stepF
    (k : PositiveMap.key)
    (b : Branch nq)
    (acc : ProgramState nq) : ProgramState nq :=
    ProgramState_merge nq acc (F k b).

  Definition VF
    (k : PositiveMap.key)
    (vb : ValidBranch) : ValidProgramState :=
    ValidProgramState_construct
      (F k (proj1_sig vb))
      (F_valid k _ (proj2_sig vb)).
  
  Definition VstepF
    (k : PositiveMap.key)
    (vb : ValidBranch)
    (vacc : ValidProgramState) : ValidProgramState :=
    ValidProgramState_merge vacc (VF k vb).
  
  Lemma VstepF_Proper :
    Proper (eq ==> eq ==> ValidProgramState_equiv ==> ValidProgramState_equiv)
      VstepF.
  Proof.
    intros k1 k2 Hk vb1 vb2 Hvb vacc1 vacc2 Hvacc.
    subst.
    unfold VstepF.
    apply ValidProgramState_merge_Proper.
    - exact Hvacc.
    - apply ValidProgramState_equiv_equivalence.
  Qed.

  Lemma construct_stepF :
    forall ps (Hps : ProgramState_valid nq ps) k b (Hb : Branch_valid nq b),
      ValidProgramState_equiv
        (ValidProgramState_construct
           (stepF k b ps)
           (ProgramState_merge_valid nq ps (F k b) Hps (F_valid k b Hb)))
        (VstepF k (exist _ b Hb)
           (ValidProgramState_construct ps Hps)).
  Proof.
    intros.
    unfold stepF, VstepF, VF.
    apply ValidProgramState_merge_rewrite.
  Qed.

  Lemma VstepF_transpose :
    PProperties.transpose_neqkey ValidProgramState_equiv VstepF.
  Proof.
    intros k1 k2 e1 e2 a Hk.
    destruct e1, e2.
  Admitted.

  Lemma fold_stepF_valid :
    forall m i,
      ProgramState_valid nq m ->
      ProgramState_valid nq i ->
      ProgramState_valid nq (PositiveMap.fold stepF m i).
  Proof.
    intros m i Hm Hi.
    eapply (PProperties.fold_rec_nodep
      (P := fun st => ProgramState_valid nq st)
      (f := stepF)
      (i := i)
      (m := m)); eauto.
    intros k b acc Hmap Hacc.
    unfold stepF.
    eapply ProgramState_merge_valid; eauto.
  Qed.

  Lemma construct_foldF' :
  forall m (Hm : ProgramState_valid nq m)
         i (Hi : ProgramState_valid nq i),
    ProgramState_valid nq (PositiveMap.fold stepF m i) /\
    forall (Hm' : ProgramState_valid nq m)
           (Hfold : ProgramState_valid nq (PositiveMap.fold stepF m i)),
      ValidProgramState_equiv
        (ValidProgramState_construct
           (PositiveMap.fold stepF m i)
           Hfold)
        (PositiveMap.fold VstepF
           (ValidProgramState_construct m Hm')
           (ValidProgramState_construct i Hi)).
  Proof.
    intros m Hm i Hi.
    apply PProperties.fold_rec.
    - intros m0 Hempty.
      split. apply Hi.
      intros Hm' Hfold.
      rewrite PProperties.fold_Empty.
      + apply ValidProgramState_proof_irrel.
      + apply eq_equivalence.
      + intros k vb Hmapsto.
        apply (Hempty k (proj1_sig vb)).
        unfold PositiveMap.MapsTo in Hmapsto.
        shelve.
    - intros k e a m' m'' Hmapsto Hnotin Hadd [Ha H].
      split.
      + unfold stepF.
        apply ProgramState_merge_valid.
        apply Ha.
        apply F_valid.
        apply (Hm k e Hmapsto).
      + intros Hm'' Hfold.
        assert (Hm': ProgramState_valid nq m'). shelve.
        apply ValidProgramState_equiv_equivalence with (y :=
          VstepF k (exist _ e (Hm _ _ Hmapsto))
          (PositiveMap.fold VstepF
            (ValidProgramState_construct m' Hm')
            (ValidProgramState_construct i Hi))
        ).
        * shelve.
        * apply ValidProgramState_equiv_equivalence.
          apply PProperties.fold_Add with (eqA:=ValidProgramState_equiv).
          -- apply ValidProgramState_equiv_equivalence.
          -- apply VstepF_Proper.
          -- apply VstepF_transpose.
          -- intros Hcontra.
             apply ValidProgramState_in_iff in Hcontra.
             apply Hnotin.
             destruct Hcontra as [b Hb].
             exists b.
             rewrite PFacts.find_mapsto_iff.
             rewrite PFacts.find_mapsto_iff in Hb.
             rewrite <- Hb.
             rewrite ValidProgramState_proj_construct.
             reflexivity.
          -- shelve.
  Admitted.

  Lemma construct_foldF :
    forall m (Hm : ProgramState_valid nq m)
           i (Hi : ProgramState_valid nq i),
      ValidProgramState_equiv
        (ValidProgramState_construct
           (PositiveMap.fold stepF m i)
           (fold_stepF_valid m i Hm Hi))
        (PositiveMap.fold VstepF
           (ValidProgramState_construct m Hm)
           (ValidProgramState_construct i Hi)).
  Proof.
    intros m Hm i Hi.
    apply construct_foldF'.
    apply Hm.
  Qed.
    
End ValidPS.