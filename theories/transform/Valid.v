Require Import QASMInfer.util.All.
Require Import QASMInfer.matrix.All.
Require Import QASMInfer.property.All.
Require Import QASMInfer.operator.All.
Require Import QASMInfer.program.All.

Require Import QASMInfer.transform.Equiv.

From Stdlib Require Import List Logic.
From Stdlib Require Import Classes.RelationClasses Classes.Morphisms.
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
  
  Definition ValidProgramState_empty : ValidProgramState :=
    @PositiveMap.empty ValidBranch.

  Definition ValidProgramState_add
    (k : PositiveMap.key)
    (b : Branch nq)
    (Hb : Branch_valid nq b)
    (vps : ValidProgramState)
    : ValidProgramState :=
    PositiveMap.add k (exist _ b Hb) vps.

  Definition ValidProgramState_map
    (g : Branch nq -> Branch nq)
    (Hg : forall b, Branch_valid nq b -> Branch_valid nq (g b))
    (vps : ValidProgramState)
    : ValidProgramState :=
    PositiveMap.map
      (fun vb =>
        exist _
          (g (proj1_sig vb))
          (Hg _ (proj2_sig vb)))
      vps.

  Lemma ValidBranch_eq
  (vb1 vb2 : ValidBranch)
  : proj1_sig vb1 = proj1_sig vb2 -> vb1 = vb2.
  Proof.
    destruct vb1 as [b1 Hb1].
    destruct vb2 as [b2 Hb2].
    simpl.
    intros H.
    subst b2.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma ValidProgramState_equiv_iff
  (vps1 vps2 : ValidProgramState)
  : ValidProgramState_equiv vps1 vps2 <-> PositiveMap.Equal vps1 vps2.
  Proof.
    unfold ValidProgramState_equiv.
    unfold ProgramState_equiv.
    unfold PositiveMap.Equal.
    unfold ValidProgramState_proj.
    split.
    - intros H k.
      specialize (H k).
      repeat rewrite PFacts.map_o in H.
      unfold ValidBranch in *.
      destruct (@PositiveMap.find (@sig (Branch nq) (fun b : Branch nq => Branch_valid nq b)) k vps1) as [[b1 Hb1] |] eqn:E1;
      destruct (@PositiveMap.find (@sig (Branch nq) (fun b : Branch nq => Branch_valid nq b)) k vps2) as [[b2 Hb2] |] eqn:E2;
      subst; simpl in H; try discriminate; try reflexivity.
      inversion H; subst.
      f_equal; f_equal.
      apply proof_irrelevance.
    - intros H k.
      repeat rewrite PFacts.map_o.
      rewrite H.
      reflexivity.
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

  Lemma ValidProgramState_proj_map :
    forall
      (g : Branch nq -> Branch nq)
      (Hg : forall b, Branch_valid nq b -> Branch_valid nq (g b))
      (vps : ValidProgramState),
      ProgramState_equiv nq
        (ValidProgramState_proj (ValidProgramState_map g Hg vps))
        (PositiveMap.map g (ValidProgramState_proj vps)).
  Proof.
    intros g Hg vps cstate.
    unfold ValidProgramState_proj, ValidProgramState_map.
    repeat rewrite PFacts.map_o.
    Set Printing Implicit.
    destruct (@PositiveMap.find {b : Branch nq | Branch_valid nq b} cstate vps) as [[b Hb] |]; reflexivity.
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

  Lemma ValidProgramState_construct_empty_rewrite
    (Hempty : ProgramState_valid nq (PositiveMap.empty (Branch nq)))
    :
    ValidProgramState_equiv
      (ValidProgramState_construct
         (PositiveMap.empty (Branch nq))
         Hempty)
      (ValidProgramState_empty).
  Proof.
    unfold ValidProgramState_equiv, ValidProgramState_empty.
    intro y.
    pose proof
      (ValidProgramState_proj_construct
         (PositiveMap.empty (Branch nq)) Hempty y) as H.
    rewrite H.
    unfold ValidProgramState_proj.
    rewrite PFacts.map_o.
    rewrite PFacts.empty_o.
    rewrite PFacts.empty_o.
    reflexivity.
  Qed.

  Lemma ValidProgramState_construct_add_rewrite
    k b Hb m Hm Hadd
    :
    ValidProgramState_equiv
      (ValidProgramState_construct
         (PositiveMap.add k b m)
         Hadd)
      (ValidProgramState_add k b Hb
         (ValidProgramState_construct m Hm)).
  Proof.
    unfold ValidProgramState_equiv, ValidProgramState_add.
    intro y.

    pose proof
      (ValidProgramState_proj_construct
         (PositiveMap.add k b m) Hadd y) as Hleft.
    rewrite Hleft.

    unfold ValidProgramState_proj.
    repeat rewrite PFacts.map_o.
    repeat rewrite PFacts.add_o.

    destruct (PositiveMap.E.eq_dec k y) as [Heq | Hneq].
    - reflexivity.
    - pose proof
        (ValidProgramState_proj_construct m Hm y) as Hmproj.
      unfold ValidProgramState_proj in Hmproj.
      rewrite PFacts.map_o in Hmproj.
      symmetry.
      exact Hmproj.
  Qed.

  Lemma ValidProgramState_construct_map_rewrite
    (g : Branch nq -> Branch nq)
    (Hg : forall b, Branch_valid nq b -> Branch_valid nq (g b))
    ps Hps Hmap
    :
    ValidProgramState_equiv
      (ValidProgramState_construct
         (PositiveMap.map g ps)
         Hmap)
      (ValidProgramState_map g Hg
         (ValidProgramState_construct ps Hps)).
  Proof.
    unfold ValidProgramState_equiv, ValidProgramState_map.
    intro y.

    pose proof
      (ValidProgramState_proj_construct
         (PositiveMap.map g ps) Hmap y) as Hleft.
    rewrite Hleft.
    rewrite PFacts.map_o.

    unfold ValidProgramState_proj.
    repeat rewrite PFacts.map_o.

    pose proof
      (ValidProgramState_proj_construct ps Hps y) as Hpsproj.
    unfold ValidProgramState_proj in Hpsproj.
    rewrite PFacts.map_o in Hpsproj.

    Set Printing Implicit.

    destruct (@PositiveMap.find {x : Branch nq | Branch_valid nq x} y (ValidProgramState_construct ps Hps))
      as [[br Hbr] |] eqn:E1;
    destruct (PositiveMap.find y ps)
      as [br' |] eqn:E2;
    simpl in *; try discriminate; try reflexivity.

    inversion Hpsproj; subst.
    reflexivity.
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

  Lemma ValidProgramState_fold_Proper
    (f: positive -> ValidBranch -> PositiveMap.t (ValidBranch) -> PositiveMap.t (ValidBranch)):
    (forall k vb, Proper (ValidProgramState_equiv ==> ValidProgramState_equiv) (f k vb)) ->
    Proper (ValidProgramState_equiv ==> ValidProgramState_equiv ==> ValidProgramState_equiv)
    (PositiveMap.fold f).
  Proof.
    intros Hf vb1 vb2 Hbv v1 v2 Hv.
    rewrite PositiveMap.fold_1, PositiveMap.fold_1.
    apply (fold_left_eqlistA_Proper (POrd.O.eqke (elt:=ValidBranch))).
    - intros [k1 b1] [k2 b2] acc1 acc2 Hpq Hacc.
      destruct Hpq as [Hk Hb]. simpl in *.
      rewrite Hk, Hb.
      apply Hf. apply Hacc.
    - apply POrd.elements_Equal_eqlistA.
      rewrite <- ValidProgramState_equiv_iff.
      apply Hbv.
    - apply Hv.
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
    forall (vps1 vps2: ValidProgramState),
    ValidProgramState_equiv
    (ValidProgramState_merge vps1 vps2)
    (ValidProgramState_merge vps2 vps1).
  Proof.
    intros vps1 vps2.
    unfold ValidProgramState_equiv, ValidProgramState_merge.
    repeat rewrite ValidProgramState_proj_construct.
    apply ProgramState_merge_commute.
    all: apply ValidProgramState_proj_valid.
  Qed.

  Lemma ValidProgramState_merge_transpose:
    forall (vps vps1 vps2: ValidProgramState),
    ValidProgramState_equiv
    (ValidProgramState_merge vps1 (ValidProgramState_merge vps2 vps))
    (ValidProgramState_merge vps2 (ValidProgramState_merge vps1 vps)).
  Proof.
    intros vps vps1 vps2.
    unfold ValidProgramState_equiv, ValidProgramState_merge.
    rewrite ValidProgramState_proj_construct.
    apply ProgramState_equiv_equivalence.
    rewrite ValidProgramState_proj_construct.

    apply ProgramState_equiv_equivalence with (y :=
      ProgramState_merge nq (ValidProgramState_proj vps2)
      (ProgramState_merge nq (ValidProgramState_proj vps1) (ValidProgramState_proj vps))
    ). {
      apply ProgramState_merge_Proper.
      apply ProgramState_equiv_equivalence.
      rewrite ValidProgramState_proj_construct.
      apply ProgramState_equiv_equivalence.
    }

    apply ProgramState_equiv_equivalence.

    apply ProgramState_equiv_equivalence with (y :=
      ProgramState_merge nq (ValidProgramState_proj vps1)
      (ProgramState_merge nq (ValidProgramState_proj vps2) (ValidProgramState_proj vps))
    ). {
      apply ProgramState_merge_Proper.
      apply ProgramState_equiv_equivalence.
      rewrite ValidProgramState_proj_construct.
      apply ProgramState_equiv_equivalence.
    }

    apply ProgramState_merge_transpose.
    all: apply ValidProgramState_proj_valid.
  Qed.

  Lemma ValidProgramState_merge_transpose_left:
    forall (vps vps1 vps2: ValidProgramState),
    ValidProgramState_equiv
    (ValidProgramState_merge (ValidProgramState_merge vps vps2) vps1)
    (ValidProgramState_merge (ValidProgramState_merge vps vps1) vps2).
  Proof.
    intros vps vps1 vps2.
    unfold ValidProgramState_equiv.
    intros y.
    rewrite (ValidProgramState_merge_commute _ vps1).
    rewrite (ValidProgramState_merge_commute _ vps2).

    transitivity (PositiveMap.find y
      (ValidProgramState_proj (ValidProgramState_merge vps1 (ValidProgramState_merge vps2 vps)))
    ). {
      apply ValidProgramState_merge_Proper.
      apply ValidProgramState_equiv_equivalence.
      apply ValidProgramState_merge_commute.
    }

    rewrite ValidProgramState_merge_transpose.
    apply ValidProgramState_merge_Proper.
    apply ValidProgramState_equiv_equivalence.
    apply ValidProgramState_merge_commute.
  Qed.

  Lemma ValidProgramState_map_add :
    forall
      (g : Branch nq -> Branch nq)
      (Hg : forall b, Branch_valid nq b -> Branch_valid nq (g b))
      k b Hb
      (vps : ValidProgramState),
      ValidProgramState_equiv
        (ValidProgramState_map g Hg
          (ValidProgramState_add k b Hb vps))
        (ValidProgramState_add k (g b) (Hg b Hb)
          (ValidProgramState_map g Hg vps)).
  Proof.
    intros g Hg k b Hb vps.
    apply ValidProgramState_equiv_iff.
    intro y.
    unfold ValidProgramState_map, ValidProgramState_add.

    rewrite PFacts.map_o.
    repeat rewrite PFacts.add_o.

    destruct (PositiveMap.E.eq_dec k y) as [Heq | Hneq].
    - reflexivity.
    - rewrite PFacts.map_o.
      reflexivity.
  Qed.

  Lemma ValidProgramState_fold_add :
    forall
      (f : PositiveMap.key ->
          ValidBranch ->
          ValidProgramState ->
          ValidProgramState),
      Proper
        (eq ==> eq ==> ValidProgramState_equiv ==> ValidProgramState_equiv)
        f ->
      PProperties.transpose_neqkey ValidProgramState_equiv f ->
      forall k b Hb
            (vps init : ValidProgramState),
        ~ PositiveMap.In k vps ->
        ValidProgramState_equiv
          (PositiveMap.fold f
            (ValidProgramState_add k b Hb vps)
            init)
          (f k (exist _ b Hb)
            (PositiveMap.fold f vps init)).
  Proof.
    intros f Hproper Htranspose k b Hb vps init Hnotin.
    unfold ValidProgramState_add.

    eapply PProperties.fold_Add with (eqA := ValidProgramState_equiv).
    - apply ValidProgramState_equiv_equivalence.
    - exact Hproper.
    - exact Htranspose.
    - exact Hnotin.
    - unfold PProperties.Add.
      intro y.
      reflexivity.
  Qed.

  Lemma ValidProgramState_map_swap_merge
    (g : Branch nq -> Branch nq)
    (Hg : forall b, Branch_valid nq b -> Branch_valid nq (g b))
    (H: forall ps1 ps2,
      ProgramState_valid nq ps1 ->
      ProgramState_valid nq ps2 ->
      ProgramState_equiv nq
        (PositiveMap.map g (ProgramState_merge nq ps1 ps2))
        (ProgramState_merge nq
          (PositiveMap.map g ps1)
          (PositiveMap.map g ps2)))
    :
    forall vps1 vps2,
      ValidProgramState_equiv
        (ValidProgramState_map g Hg
          (ValidProgramState_merge vps1 vps2))
        (ValidProgramState_merge
          (ValidProgramState_map g Hg vps1)
          (ValidProgramState_map g Hg vps2)).
  Proof.
    intros vps1 vps2.
    unfold ValidProgramState_equiv.

    rewrite (ValidProgramState_proj_map g Hg
      (ValidProgramState_merge vps1 vps2)).

    unfold ValidProgramState_merge.
    repeat rewrite ValidProgramState_proj_construct.

    eapply ProgramState_equiv_equivalence with
      (y :=
        ProgramState_merge nq
          (PositiveMap.map g (ValidProgramState_proj vps1))
          (PositiveMap.map g (ValidProgramState_proj vps2))).
    - apply H.
      all: apply ValidProgramState_proj_valid.
    - apply ProgramState_merge_Proper.
      + apply ProgramState_equiv_equivalence.
        apply ValidProgramState_proj_map.
      + apply ProgramState_equiv_equivalence.
        apply ValidProgramState_proj_map.
  Qed.
  
  Variable F : PositiveMap.key -> Branch nq -> ProgramState nq.

  Hypothesis F_valid :
    forall k b,
      Branch_valid nq b ->
      ProgramState_valid nq (F k b).

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
           (fold_step nq F k b ps)
           (ProgramState_merge_valid nq ps (F k b) Hps (F_valid k b Hb)))
        (VstepF k (exist _ b Hb)
           (ValidProgramState_construct ps Hps)).
  Proof.
    intros.
    unfold VstepF, VF.
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

  Lemma ValidProgramState_fold_VstepF_add :
    forall k b Hb
          (vps init : ValidProgramState),
      ~ PositiveMap.In k vps ->
      ValidProgramState_equiv
        (PositiveMap.fold VstepF
          (ValidProgramState_add k b Hb vps)
          init)
        (VstepF k (exist _ b Hb)
          (PositiveMap.fold VstepF vps init)).
  Proof.
    intros k b Hb vps init Hnotin.
    eapply ValidProgramState_fold_add.
    - apply VstepF_Proper.
    - apply VstepF_transpose.
    - exact Hnotin.
  Qed.

  Lemma fold_stepF_valid :
    forall m i,
      ProgramState_valid nq m ->
      ProgramState_valid nq i ->
      ProgramState_valid nq (PositiveMap.fold (fold_step nq F) m i).
  Proof.
    intros m i Hm Hi.
    eapply (PProperties.fold_rec_nodep
      (P := fun st => ProgramState_valid nq st)
      (f := (fold_step nq F))
      (i := i)
      (m := m)); eauto.
    intros k b acc Hmap Hacc.
    eapply ProgramState_merge_valid; eauto.
  Qed.

  Lemma construct_foldF' :
  forall m (Hm : ProgramState_valid nq m)
         i (Hi : ProgramState_valid nq i),
    ProgramState_valid nq (PositiveMap.fold (fold_step nq F) m i) /\
    forall (Hm' : ProgramState_valid nq m)
           (Hfold : ProgramState_valid nq (PositiveMap.fold (fold_step nq F) m i)),
      ValidProgramState_equiv
        (ValidProgramState_construct
           (PositiveMap.fold (fold_step nq F) m i)
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
      + apply ProgramState_merge_valid.
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
           (H: ProgramState_valid nq (PositiveMap.fold (fold_step nq F) m i)),
      ValidProgramState_equiv
        (ValidProgramState_construct
           (PositiveMap.fold (fold_step nq F) m i)
           H)
        (PositiveMap.fold VstepF
           (ValidProgramState_construct m Hm)
           (ValidProgramState_construct i Hi)).
  Proof.
    intros m Hm i Hi H.
    apply construct_foldF'.
    apply Hm.
  Qed.

  Lemma ProgramState_fold_stepF_add :
    forall k b (Hb : Branch_valid nq b)
           (m init : ProgramState nq)
           (Hm : ProgramState_valid nq m)
           (Hi : ProgramState_valid nq init),
      ~ PositiveMap.In k m ->
      ProgramState_equiv nq
        (PositiveMap.fold (fold_step nq F)
           (PositiveMap.add k b m)
           init)
        (fold_step nq F k b
           (PositiveMap.fold (fold_step nq F) m init)).
  Proof.
    intros k b Hb m init Hm Hi Hnotin.

    assert (Hadd : ProgramState_valid nq (PositiveMap.add k b m)).
    { apply ProgramState_add_valid; assumption. }

    assert (Hfold_m :
      ProgramState_valid nq (PositiveMap.fold (fold_step nq F) m init)).
    { apply fold_stepF_valid; assumption. }

    assert (Hfold_add :
      ProgramState_valid nq
        (PositiveMap.fold (fold_step nq F) (PositiveMap.add k b m) init)).
    { apply fold_stepF_valid; assumption. }

    assert (Hright :
      ProgramState_valid nq
        (fold_step nq F k b (PositiveMap.fold (fold_step nq F) m init))).
    {
      apply ProgramState_merge_valid.
      - exact Hfold_m.
      - apply F_valid. exact Hb.
    }

    rewrite (ValidProgramState_rewrite
      (PositiveMap.fold (fold_step nq F) (PositiveMap.add k b m) init)
      (fold_step nq F k b (PositiveMap.fold (fold_step nq F) m init))
      Hfold_add Hright).

    apply ValidProgramState_equiv_equivalence with
      (y :=
        PositiveMap.fold VstepF
          (ValidProgramState_construct
            (PositiveMap.add k b m) Hadd)
          (ValidProgramState_construct init Hi)).
    - apply construct_foldF.
    - apply ValidProgramState_equiv_equivalence with
        (y :=
          PositiveMap.fold VstepF
            (ValidProgramState_add k b Hb
              (ValidProgramState_construct m Hm))
            (ValidProgramState_construct init Hi)).
      + apply ValidProgramState_fold_Proper.
        * intros k0 vb.
          unfold Proper, respectful.
          intros acc1 acc2 Hacc.
          apply VstepF_Proper; try reflexivity.
          exact Hacc.
        * apply ValidProgramState_construct_add_rewrite.
        * apply ValidProgramState_equiv_equivalence.
      + apply ValidProgramState_equiv_equivalence with
          (y :=
            VstepF k (exist _ b Hb)
              (PositiveMap.fold VstepF
                (ValidProgramState_construct m Hm)
                (ValidProgramState_construct init Hi))).
        * apply ValidProgramState_fold_VstepF_add.
          intros Hcontra.
          apply ValidProgramState_in_iff in Hcontra.
          apply Hnotin.
          destruct Hcontra as [b' Hb'].
          exists b'.
          rewrite PFacts.find_mapsto_iff.
          rewrite PFacts.find_mapsto_iff in Hb'.
          rewrite <- Hb'.
          rewrite ValidProgramState_proj_construct.
          reflexivity.
        * apply ValidProgramState_equiv_equivalence with
            (y :=
              VstepF k (exist _ b Hb)
                (ValidProgramState_construct
                  (PositiveMap.fold (fold_step nq F) m init) Hfold_m)).
          -- apply VstepF_Proper; try reflexivity.
             apply ValidProgramState_equiv_equivalence.
             apply construct_foldF.
          -- apply ValidProgramState_equiv_equivalence with
               (y :=
                 ValidProgramState_construct
                   (fold_step nq F k b (PositiveMap.fold (fold_step nq F) m init))
                   (ProgramState_merge_valid nq
                     (PositiveMap.fold (fold_step nq F) m init)
                     (F k b)
                     Hfold_m
                     (F_valid k b Hb))).
             ++ apply ValidProgramState_equiv_equivalence.
                apply construct_stepF.
             ++ apply ValidProgramState_proof_irrel.
  Qed.
    
End ValidPS.

Global Instance ValidProgramState_equiv_Equivalence_inst
  (nq : nat)
  :
  Equivalence (ValidProgramState_equiv nq).
Proof.
  apply ValidProgramState_equiv_equivalence.
Qed.

Global Instance ValidProgramState_proj_Proper_inst
  (nq : nat)
  :
  Proper
    (ValidProgramState_equiv nq ==> ProgramState_equiv nq)
    (ValidProgramState_proj nq).
Proof.
  intros vps1 vps2 H.
  exact H.
Qed.

Global Instance ValidProgramState_find_Proper_inst
  (nq : nat) (k : PositiveMap.key)
  :
  Proper
    (ValidProgramState_equiv nq ==> eq)
    (@PositiveMap.find (ValidBranch nq) k).
Proof.
  intros vps1 vps2 H.
  apply ValidProgramState_equiv_iff in H.
  exact (H k).
Qed.

Global Instance ValidProgramState_add_Proper_inst
  (nq : nat)
  :
  Proper
    (eq ==> eq ==> ValidProgramState_equiv nq ==> ValidProgramState_equiv nq)
    (@PositiveMap.add (ValidBranch nq)).
Proof.
  intros k1 k2 Hk vb1 vb2 Hvb vps1 vps2 Hvps.
  subst k2 vb2.
  apply ValidProgramState_equiv_iff.
  apply ValidProgramState_equiv_iff in Hvps.
  intro y.
  repeat rewrite PFacts.add_o.
  destruct (PositiveMap.E.eq_dec k1 y).
  - reflexivity.
  - apply Hvps.
Qed.

Global Instance ValidProgramState_lifted_add_Proper_inst
  (nq : nat)
  (k : PositiveMap.key)
  (b : Branch nq)
  (Hb : Branch_valid nq b)
  :
  Proper
    (ValidProgramState_equiv nq ==> ValidProgramState_equiv nq)
    (ValidProgramState_add nq k b Hb).
Proof.
  intros vps1 vps2 Hvps.
  unfold ValidProgramState_add.
  apply ValidProgramState_equiv_iff.
  apply ValidProgramState_equiv_iff in Hvps.
  intro y.
  repeat rewrite PFacts.add_o.
  destruct (PositiveMap.E.eq_dec k y).
  - reflexivity.
  - apply Hvps.
Qed.

Global Instance ValidProgramState_map_Proper_inst
  (nq : nat)
  :
  Proper
    ((eq ==> eq) ==> ValidProgramState_equiv nq ==> ValidProgramState_equiv nq)
    (@PositiveMap.map (ValidBranch nq) (ValidBranch nq)).
Proof.
  intros f g Hfg vps1 vps2 Hvps.
  apply ValidProgramState_equiv_iff.
  apply ValidProgramState_equiv_iff in Hvps.
  intro y.
  repeat rewrite PFacts.map_o.
  rewrite Hvps.
  destruct (PositiveMap.find y vps2) as [vb |]; simpl.
  - f_equal. apply Hfg. reflexivity.
  - reflexivity.
Qed.

Global Instance ValidProgramState_lifted_map_Proper_inst
  (nq : nat)
  (g : Branch nq -> Branch nq)
  (Hg : forall b, Branch_valid nq b -> Branch_valid nq (g b))
  :
  Proper
    (ValidProgramState_equiv nq ==> ValidProgramState_equiv nq)
    (ValidProgramState_map nq g Hg).
Proof.
  intros vps1 vps2 Hvps.
  unfold ValidProgramState_map.
  apply ValidProgramState_equiv_iff.
  apply ValidProgramState_equiv_iff in Hvps.
  intro y.
  repeat rewrite PFacts.map_o.
  rewrite Hvps.
  reflexivity.
Qed.

Global Instance ValidProgramState_merge_Proper_inst
  (nq : nat)
  :
  Proper
    (ValidProgramState_equiv nq ==>
     ValidProgramState_equiv nq ==>
     ValidProgramState_equiv nq)
    (ValidProgramState_merge nq).
Proof.
  apply ValidProgramState_merge_Proper.
Qed.

Global Instance ValidProgramState_fold_Proper_inst
  (nq : nat)
  (f : positive ->
       ValidBranch nq ->
       PositiveMap.t (ValidBranch nq) ->
       PositiveMap.t (ValidBranch nq))
  (Hf : forall k vb,
      Proper
        (ValidProgramState_equiv nq ==> ValidProgramState_equiv nq)
        (f k vb))
  :
  Proper
    (ValidProgramState_equiv nq ==>
     ValidProgramState_equiv nq ==>
     ValidProgramState_equiv nq)
    (PositiveMap.fold f).
Proof.
  apply ValidProgramState_fold_Proper.
  exact Hf.
Qed.

Global Instance VstepF_fold_step_Proper_inst
  (nq : nat)
  (F : PositiveMap.key -> Branch nq -> ProgramState nq)
  (F_valid :
     forall k b,
       Branch_valid nq b ->
       ProgramState_valid nq (F k b))
  :
  Proper
    (ValidProgramState_equiv nq ==>
     ValidProgramState_equiv nq ==>
     ValidProgramState_equiv nq)
    (PositiveMap.fold (VstepF nq F F_valid)).
Proof.
  apply ValidProgramState_fold_Proper.
  intros k vb.
  unfold VstepF.
  intros acc1 acc2 Hacc.
  apply ValidProgramState_merge_Proper.
  - exact Hacc.
  - reflexivity.
Qed.
