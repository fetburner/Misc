Require Import List Ensembles Finite_sets_facts Relations Program Omega.

Section ARS.
  Variable A : Set.
  Variable R : A -> A -> Prop.

  Inductive nfold_composition : nat -> A -> A -> Prop :=
    | nfold_composition_ident x :
        nfold_composition 0 x x
    | nfold_composition_comp n x y z :
        R x y ->
        nfold_composition n y z ->
        nfold_composition (S n) x z.
  Hint Constructors nfold_composition.

  Definition reducible x := exists y, R x y.
  Definition in_normal_form x := forall y, ~R x y.
  Arguments in_normal_form x /.
  Definition normal_form_of x y :=
    clos_refl_trans _ R x y /\ in_normal_form y.
  Arguments normal_form_of x y /.
  Definition joinable x y :=
    exists z, clos_refl_trans _ R x z /\ clos_refl_trans _ R y z.
  Arguments joinable x y /.

  Definition Church_Rosser :=
    forall x y,
    clos_refl_sym_trans _ R x y ->
    joinable x y.
  Definition confluent :=
    forall x y1 y2,
    clos_refl_trans _ R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2.
  Definition semi_confluent :=
    forall x y1 y2,
    R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2.
  Definition locally_confluent :=
    forall a1 a2 a3,
    R a1 a2 ->
    R a1 a3 ->
    joinable a2 a3.

  Definition terminating :=
    well_founded (fun x y => R y x).
  Definition normalizing :=
    forall x, exists y, normal_form_of x y.

  Hint Constructors clos_refl_trans.

  Theorem Church_Rosser_impl_confluent :
    Church_Rosser ->
    confluent.
  Proof.
    intros HCR ? y1 y2 Hrtc1 Hrtc2.
    assert (Hrstc : clos_refl_sym_trans _ R y1 y2).
    { apply clos_rt_clos_rst in Hrtc1.
      apply clos_rt_clos_rst in Hrtc2.
      apply rst_sym in Hrtc1.
      eapply rst_trans; eauto. }
    eauto.
  Qed.

  Lemma confluent_impl_semi_confluent :
    confluent ->
    semi_confluent.
  Proof.
    Hint Resolve rt_step.
    intros ? ? ? ? ? ?.
    eauto.
  Qed.

  Lemma semi_confluent_impl_Church_Rosser :
    semi_confluent ->
    Church_Rosser.
  Proof.
    intros Hsc x ? Hrstc.
    apply clos_rst_rst1n_iff in Hrstc.
    induction Hrstc as [| ? ? ? [ | ] ? [w []]]; simpl; eauto.
    - edestruct Hsc as [? []]; eauto.
  Qed.

  Corollary confluent_normal_form :
    confluent ->
    forall x y,
    clos_refl_sym_trans _ R x y ->
    in_normal_form y ->
    clos_refl_trans _ R x y.
  Proof.
    intros Hc ? ? Hrstc Hnf.
    specialize
      (semi_confluent_impl_Church_Rosser
        (confluent_impl_semi_confluent Hc)).
    intros HCR.
    specialize (HCR _ _ Hrstc).
    destruct HCR as [? [? Hrtc]].
    apply clos_rt_rt1n in Hrtc.
    inversion Hrtc as [| ? ? HR ]; subst.
    - assumption.
    - destruct (Hnf _ HR).
  Qed.

  Corollary confluent_both_normal_form :
    confluent ->
    forall x y,
    clos_refl_sym_trans _ R x y ->
    in_normal_form x ->
    in_normal_form y ->
    x = y.
  Proof.
    intros Hc ? ? Hrstc Hnfx Hnfy.
    specialize (confluent_normal_form Hc _ _ Hrstc Hnfy).
    intros Hrtc.
    apply clos_rt_rt1n in Hrtc.
    inversion Hrtc as [| ? ? HR ]; subst.
    - reflexivity.
    - destruct (Hnfx _ HR).
  Qed.

  Fact confluent_most_one_normal_form :
    confluent ->
    forall x, uniqueness (fun y => normal_form_of x y).
  Proof.
    intros Hc ? ? ? [Hrtc1] [Hrtc2].
    destruct (Hc _ _ _ Hrtc1 Hrtc2) as [? [Hrtc1' Hrtc2']].
    apply confluent_both_normal_form; eauto.
    apply clos_rt_clos_rst in Hrtc1'.
    apply clos_rt_clos_rst in Hrtc2'.
    apply rst_sym in Hrtc2'.
    eapply rst_trans; eauto.
  Qed.

  Lemma normalizing_confluent_normal_form :
    normalizing /\ confluent
    <-> (forall x, exists! y, normal_form_of x y).
  Proof.
    split.
    - intros [Hn Hc] x.
      destruct (Hn x) as [y].
      exists y.
      split.
      + eauto.
      + intros ?.
        apply confluent_most_one_normal_form; eauto.
    - intros Hunique.
      split; intros x; destruct (Hunique x) as [x' []]; eauto.
      intros y1 y2 ? ?.
      destruct (Hunique y1) as [y1' [[]]].
      destruct (Hunique y2) as [y2' [[]]].
      simpl in *.
      replace y1' with x' in * by eauto.
      replace y2' with x' in * by eauto.
      eauto.
  Qed.

  Theorem rst_iff_normal_form_equiv :
    confluent ->
    forall x x' y y',
    normal_form_of x x' ->
    normal_form_of y y' ->
    (clos_refl_sym_trans _ R x y <-> x' = y').
  Proof.
    intros Hc x x' y y' [Hrtcx] [Hrtcy].
    apply clos_rt_clos_rst in Hrtcx.
    apply clos_rt_clos_rst in Hrtcy.
    split.
    - intros Hrstc.
      apply rst_sym in Hrtcx.
      apply confluent_both_normal_form; eauto.
      eapply rst_trans; eauto.
      eapply rst_trans; eauto.
    - intros; subst.
      apply rst_sym in Hrtcy.
      eapply rst_trans; eauto.
  Qed.

  Definition finitely_branching := forall x, Finite _ (R x).
  Definition globally_finite := forall x, Finite _ (clos_trans _ R x).
  Definition acyclic := forall x, ~clos_trans _ R x x.

  Hint Constructors clos_trans.

  Lemma clos_trans_inversion : forall A R x z,
    clos_trans A R x z ->
    R x z \/ (exists y, R x y /\ clos_trans _ R y z).
  Proof.
    intros ? ? ? ? Htc.
    apply clos_trans_t1n in Htc.
    inversion Htc as [| ? ? ? Htc' ]; subst.
    - eauto.
    - apply clos_t1n_trans in Htc'.
      eauto.
  Qed.

  Lemma finitely_branching_impl_globally_finite :
    terminating ->
    finitely_branching ->
    globally_finite.
  Proof.
    Hint Constructors Singleton.
    intros Ht Hfb x.
    induction x as [x IH] using (Fix Ht).
    assert (IHHFP : forall P,
      Finite _ P ->
      forall Q,
      Finite _ Q ->
      Included _ P (R x) ->
      Included _ Q (clos_trans _ R x) ->
      Included _ (clos_trans _ R x) (Union _ Q (fun z => exists y, P y /\ (y = z \/ clos_trans _ R y z))) ->
      Finite _ (clos_trans _ R x)).
    - induction 1 as [ | P HFP ? y ]; intros ? HFQ HR Htc Hcomplete.
      + apply Finite_downward_closed with (A := Q).
        * assumption.
        * intros y HIn.
          apply Hcomplete in HIn.
          destruct HIn as [ | ? [ ? [ [ ] ] ] ];
              eauto with v62.
      + apply IHFinite with (Q := Add _ (Union _ Q (clos_trans _ R y)) y).
        * { apply Union_preserves_Finite.
            - apply Union_preserves_Finite.
              + assumption.
              + apply IH.
                apply HR.
                eauto 7 with v62.
            - apply Singleton_is_finite. }
        * eauto 7 with v62.
        * { intros ? HInQ.
            destruct HInQ as [ ? [ ] | ? HIn ].
            - eauto.
            - assert (HR' : R x y);
                [ apply HR | ];
                eauto with v62.
            - inversion HIn; subst.
              left.
              apply HR.
              eauto with v62. }
        * intros ? HIntc.
          specialize (Hcomplete _ HIntc).
          destruct Hcomplete as [ | ? Hcomplete ];
            [ | destruct Hcomplete as [? [ [ | ? HSingleton ] Hor ]];
                  [ | inversion HSingleton ];
                  destruct Hor ];
            subst;
            eauto 7 with v62.
    - apply IHHFP with (P := R x) (Q := Empty_set _); eauto with v62.
      intros ? Htc.
      right.
      apply clos_trans_inversion in Htc.
      destruct Htc as [ | [ ? [ ] ] ];
        eauto 7 with v62.
  Qed.

  Definition bounded :=
    forall x, exists n, forall y, ~nfold_composition n x y.

  Lemma terminating_iff_bounded :
    finitely_branching ->
    (terminating <-> bounded).
  Proof.
    intros Hfb.
    split.
    - intros Ht x.
      assert (H : exists n, forall m, n <= m -> forall y, ~ nfold_composition m x y).
      { induction x as [ x IH ] using (well_founded_induction Ht).
        assert (IHys : forall P,
          Finite _ P ->
          forall Q,
          Finite _ Q ->
          Same_set _ (R x) (Union _ P Q) ->
          (exists n, forall m,
          n <= m ->
          Included _ Q (fun y => forall z, ~ nfold_composition m y z)) ->
          exists n, forall m,
          n <= m ->
          forall y, ~nfold_composition m x y).
        + induction 1 as [ | P ? ? y ]; intros Q ? [ Hsound Hcomplete ] [ n Hacc ].
          * { exists (S n).
              intros m ? z Hnfold.
              inversion Hnfold as [ | m' ? ? ? HR Hnfold' ]; subst.
              - omega.
              - eapply Hacc with (m := m').
                + omega.
                + specialize (Hsound _ HR).
                  destruct Hsound as [ ? Hcontra | ? HIn ].
                  * inversion Hcontra.
                  * apply HIn.
                + apply Hnfold'. }
          * { assert (HR : R x y) by (apply Hcomplete; eauto with v62).
              apply IHFinite with (Q := Add _ Q y).
              - apply Union_preserves_Finite.
                + assumption.
                + apply Singleton_is_finite.
              - split.
                + intros ? HR'.
                  specialize (Hsound _ HR').
                  destruct Hsound as [ ? [ | ? HSingleton ] | ];
                    [ | inversion HSingleton; subst | ];
                    eauto with v62.
                + intros ? [ ? ? | ? [ ? ? | ? HSingleton ] ];
                    [ | | inversion HSingleton; subst ];
                    eauto with v62.
              - destruct (IH _ HR) as [ n' IH' ].
                destruct (le_dec n n');
                  [ exists n'
                  | exists n ];
                  (intros m ? ? [ ? ? | ? HSingleton ];
                    [ apply Hacc
                    | inversion HSingleton; subst;
                      intros z ?;
                      apply IH' with (m := m) (y := z) ]; eauto); omega. }
        + apply IHys with (P := R x) (Q := Empty_set _).
          * apply Hfb.
          * constructor.
          * eauto with v62.
          * exists 0.
            intros ? ? ? []. }
      destruct H as [n H].
      exists n.
      apply H.
      omega.
    - intros Hbounded x.
      destruct (Hbounded x) as [ n Hbounded' ].
      generalize dependent x.
      induction n as [ | ? IHn ];
        intros ? Hbounded';
        constructor;
        intros.
      + exfalso.
         eapply Hbounded'; eauto.
      + apply IHn.
        intros ? ?.
        eapply Hbounded'.
        eauto.
  Qed.

  Lemma Newman :
    terminating ->
    locally_confluent ->
    confluent.
  Proof.
    Local Hint Constructors clos_refl_trans_1n.
    Local Hint Resolve clos_rt1n_rt.
    Local Hint Resolve clos_rt_rt1n.
    intros HSN HLC a1 a2 a3 HRs12 HRs13.
    unfold joinable.
    apply clos_rt_rt1n in HRs12.
    apply clos_rt_rt1n in HRs13.
    generalize dependent a3.
    generalize dependent a2.
    induction a1 as [a1 IHa1] using (well_founded_induction HSN).
    intros ? HRs12 ? HRs13.
    inversion HRs12 as [| a1' ? HR11' HRs1'2 ];
      inversion HRs13 as [| a1'' ? HR11'' HRs1''3 ]; subst;
        eauto.
    destruct (HLC _ _ _ HR11' HR11'') as [? [HRs1'4]].
    apply clos_rt_rt1n in HRs1'4.
    destruct (IHa1 _ HR11' _ HRs1'2 _ HRs1'4) as [a5 []].
    assert (HRs1''5 : clos_refl_trans_1n _ R a1'' a5) by eauto.
    destruct (IHa1 _ HR11'' _ HRs1''3 _ HRs1''5) as [? []].
    eauto.
  Qed.
End ARS.

Lemma terminating_transitive_closure A R :
  terminating A R <-> terminating _ (clos_trans _ R).
Proof.
  Local Hint Constructors clos_trans.
  split;
    intros Ht x;
    induction x as [x IH] using (well_founded_induction Ht);
    constructor;
    intros y HR;
    [ apply clos_trans_t1n in HR;
      inversion HR as [ ? HR' | ? ? HR' HR'' ]; subst;
      specialize (IH _ HR');
      [ | apply clos_t1n_trans in HR'';
          inversion IH; subst ] | ];
    eauto.
Qed.

Lemma acyclic_and_globally_finite_impl_terminating A R :
  acyclic A R ->
  globally_finite _ R ->
  terminating _ R.
Proof.
  intros Hacyclic Hgf.
  apply terminating_transitive_closure.
  intros x.
  destruct (finite_cardinal _ _ (Hgf x)) as [n].
  generalize dependent x.
  induction n as [n IH]
    using (well_founded_induction (well_founded_ltof _ (fun x => x)));
    unfold ltof in *.
  intros x Hcardinal.
  constructor.
  intros y Htc.
  destruct (finite_cardinal _ _ (Hgf y)) as [m].
  apply IH with (y := m); eauto.
  apply incl_st_card_lt with
    (X := clos_trans _ R y)
    (Y := clos_trans _ R x); eauto.
  split; eauto with v62.
  intros Heq.
  apply Hacyclic with (x := y).
  rewrite Heq.
  assumption.
Qed.
