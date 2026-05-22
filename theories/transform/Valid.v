Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.

From Stdlib Require Import List Logic.
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

  Lemma ValidProgramState_proj_valid:
    forall (vps: ValidProgramState),
    ProgramState_valid nq (ValidProgramState_proj vps).
  Proof.
    intros vps.
    exact (ValidProgramState_proj_proof vps).
  Qed.

  Lemma ValidProgramState_construct_MapsTo :
  forall k b m (Hm : ProgramState_valid nq m)
         (Hkb : PositiveMap.MapsTo k b m)
         (Hb : Branch_valid nq b),
    PositiveMap.MapsTo k (exist _ b Hb)
      (ValidProgramState_construct m Hm).
  Proof.
    intros k b m Hm Hmapsto Hb.
    apply PositiveMap.find_2.
    apply PositiveMap.find_1 in Hmapsto.
    revert k b Hm Hmapsto Hb.
    induction m; intros k b Hm Hmapsto Hb; simpl in *.
    - destruct k; discriminate.
    - destruct k; simpl in *.
      + eapply IHm2. apply Hmapsto.
      + eapply IHm1. apply Hmapsto.
      + destruct o; simpl in Hmapsto.
        * inversion Hmapsto; subst.
          f_equal; f_equal.
          apply proof_irrelevance.
        * discriminate.
  Qed.

  Lemma ValidProgramState_construct_MapsTo_inv :
  forall k vb m (Hm : ProgramState_valid nq m),
    PositiveMap.MapsTo k vb (ValidProgramState_construct m Hm) ->
    PositiveMap.MapsTo k (proj1_sig vb) m.
  Proof.
    intros k vb m Hm Hmapsto.
    apply PositiveMap.find_2.
    apply PositiveMap.find_1 in Hmapsto.
    revert k vb Hm Hmapsto.
    induction m; intros k vb Hm Hmapsto; simpl in *.
    - destruct k; discriminate.
    - destruct k; simpl in *.
      + eapply IHm2. apply Hmapsto.
      + eapply IHm1. apply Hmapsto.
      + destruct o; simpl in Hmapsto.
        * inversion Hmapsto. reflexivity.
        * discriminate.
  Qed.

  Lemma ValidProgramState_construct_find_some :
  forall k b m (Hm : ProgramState_valid nq m)
         (Hb : Branch_valid nq b),
    PositiveMap.find k m = Some b ->
    PositiveMap.find k (ValidProgramState_construct m Hm)
    = Some (exist (Branch_valid nq) b Hb).
  Proof.
    intros k b m Hm Hb Hfind.
    apply PositiveMap.find_1.
    apply PositiveMap.find_2 in Hfind.
    apply ValidProgramState_construct_MapsTo.
    apply Hfind.
  Qed.

  Lemma ValidProgramState_construct_find_none :
  forall k m (Hm: ProgramState_valid nq m),
    PositiveMap.find k m = None ->
    PositiveMap.find k (ValidProgramState_construct m Hm) = None.
  Proof.
    intros k m.
    revert k.
    induction m; intros k Hm Hfind; simpl in *.
    - destruct k; reflexivity.
    - destruct k; simpl in *.
      + eapply IHm2. apply Hfind.
      + eapply IHm1. apply Hfind.
      + destruct o; try discriminate.
        reflexivity.
  Qed.

  Lemma ValidProgramState_construct_Add :
  forall k b m1 m2
         (Hm1 : ProgramState_valid nq m1)
         (Hm2 : ProgramState_valid nq m2)
         (Hb : Branch_valid nq b),
    PProperties.Add k b m1 m2 ->
    PProperties.Add k (exist (Branch_valid nq) b Hb)
      (ValidProgramState_construct m1 Hm1)
      (ValidProgramState_construct m2 Hm2).
  Proof.
    intros k b m1 m2 Hm1 Hm2 Hb Hadd.
    unfold PProperties.Add in *.
    intro y.
    specialize (Hadd y).

    rewrite PProperties.F.add_o in Hadd.
    rewrite PProperties.F.add_o.

    destruct (PositiveMap.E.eq_dec k y) as [Heq | Hneq].
    - apply ValidProgramState_construct_find_some.
      apply Hadd.
    - destruct (PositiveMap.find y m1) eqn:Hy.
      + assert (Hb0 : Branch_valid nq b0). {
          apply Hm1 with (cstate:=y).
          apply PositiveMap.find_2.
          apply Hy.
        }

        apply ValidProgramState_construct_find_some with (Hm:=Hm1) (Hb:=Hb0) in Hy.
        apply ValidProgramState_construct_find_some with (Hm:=Hm2) (Hb:=Hb0) in Hadd.

        change (ValidBranch) with (@sig (Branch nq) (Branch_valid nq)) in *.
        rewrite Hy, Hadd.
        reflexivity.
      + apply ValidProgramState_construct_find_none with (Hm:=Hm1) in Hy.
        apply ValidProgramState_construct_find_none with (Hm:=Hm2) in Hadd.
        change (ValidBranch) with (@sig (Branch nq) (Branch_valid nq)) in *.
        rewrite Hy, Hadd.
        reflexivity.
  Qed.

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
    (Hvalid2: ProgramState_valid nq ps2)
    (Hvalid: ProgramState_valid nq (ProgramState_merge nq ps1 ps2)),
    ValidProgramState_equiv
    (ValidProgramState_construct (ProgramState_merge nq ps1 ps2) Hvalid)
    (ValidProgramState_merge (ValidProgramState_construct ps1 Hvalid1) (ValidProgramState_construct ps2 Hvalid2)).
  Proof.
    intros.
    unfold ValidProgramState_equiv, ValidProgramState_merge.
    repeat rewrite ValidProgramState_proj_construct.
    apply ProgramState_merge_Proper.
    all: rewrite ValidProgramState_proj_construct.
    all: reflexivity.
  Qed.

  Lemma ValidProgramState_merge_commute:
    forall (ps1 ps2: ProgramState nq)
    (Hvalid1: ProgramState_valid nq ps1)
    (Hvalid2: ProgramState_valid nq ps2),
    ValidProgramState_equiv
    (ValidProgramState_merge (ValidProgramState_construct ps1 Hvalid1) (ValidProgramState_construct ps2 Hvalid2))
    (ValidProgramState_merge (ValidProgramState_construct ps2 Hvalid2) (ValidProgramState_construct ps1 Hvalid1)).
  Proof.
    intros ps1 ps2 Hvalid1 Hvalid2.
    unfold ValidProgramState_equiv, ValidProgramState_merge.
    intros y.
    repeat rewrite ValidProgramState_proj_construct.
    revert y.
    apply ProgramState_merge_commute.
    - apply ProgramState_valid_equal with (ps1:=ps1).
      apply Hvalid1.
      rewrite ValidProgramState_proj_construct. reflexivity.
    - apply ProgramState_valid_equal with (ps1:=ps2).
      apply Hvalid2.
      rewrite ValidProgramState_proj_construct. reflexivity.
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
    intros k1 k2 vb1 vb2 vacc Hneq.
    unfold VstepF, ValidProgramState_merge, ValidProgramState_equiv.
    intros y.
    repeat rewrite ValidProgramState_proj_construct.
    apply ProgramState_equiv_equivalence with (y :=
      (ProgramState_merge nq
        (ProgramState_merge nq (ValidProgramState_proj vacc)
        (ValidProgramState_proj (VF k2 vb2))) (ValidProgramState_proj (VF k1 vb1)))
    ).
    - apply ProgramState_merge_Proper; try reflexivity.
      apply ValidProgramState_proj_construct.
    - apply ProgramState_equiv_equivalence with (y :=
        (ProgramState_merge nq
          (ProgramState_merge nq (ValidProgramState_proj vacc)
          (ValidProgramState_proj (VF k1 vb1))) (ValidProgramState_proj (VF k2 vb2)))
      ).
      + apply ProgramState_merge_transpose_left.
        all: apply ValidProgramState_proj_valid.
      + apply ProgramState_merge_Proper; try reflexivity.
        apply ProgramState_equiv_equivalence.
        apply ValidProgramState_proj_construct.
  Qed.

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
        apply ValidProgramState_construct_MapsTo_inv in Hmapsto.
        apply Hmapsto.
    - intros k e a m' m'' Hmapsto Hnotin Hadd [Ha H].
      split.
      + unfold stepF.
        apply ProgramState_merge_valid.
        apply Ha.
        apply F_valid.
        apply (Hm k e Hmapsto).
      + intros Hm'' Hfold.
        assert (Hm': ProgramState_valid nq m'). {
          apply ProgramState_valid_add_inj with (k:=k) (b:=e).
          - apply Hnotin.
          - intros cstate branch Hm'.
            apply PositiveMap.find_1 in Hm'.
            rewrite <- Hadd in Hm'.
            apply Hm'' with (cstate:=cstate) (branch:=branch).
            apply PositiveMap.find_2.
            apply Hm'.
        }
        apply ValidProgramState_equiv_equivalence with (y :=
          VstepF k (exist _ e (Hm _ _ Hmapsto))
          (PositiveMap.fold VstepF
            (ValidProgramState_construct m' Hm')
            (ValidProgramState_construct i Hi))
        ).
        * apply ValidProgramState_equiv_equivalence with (y :=
            VstepF k (exist _ e (Hm k e Hmapsto))
            (ValidProgramState_construct a Ha)
          ).
          -- intro y. rewrite <- construct_stepF.
            apply ValidProgramState_proof_irrel.
          -- apply VstepF_Proper; try reflexivity.
            apply H.
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
          -- apply ValidProgramState_construct_Add.
             apply Hadd.
  Qed.

  Lemma construct_foldF :
    forall m (Hm : ProgramState_valid nq m)
           i (Hi : ProgramState_valid nq i)
           (H: ProgramState_valid nq (PositiveMap.fold stepF m i)),
      ValidProgramState_equiv
        (ValidProgramState_construct
           (PositiveMap.fold stepF m i)
           H)
        (PositiveMap.fold VstepF
           (ValidProgramState_construct m Hm)
           (ValidProgramState_construct i Hi)).
  Proof.
    intros m Hm i Hi H.
    apply construct_foldF'.
    apply Hm.
  Qed.
    
End ValidPS.