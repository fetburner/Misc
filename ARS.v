Require Import List Relations Program Omega.

Section ARS.
  Variable A : Set.
  Variable R : A -> A -> Prop.

  Inductive nfold_composition A R : nat -> A -> A -> Prop :=
    | nfold_composition_ident : forall x,
        nfold_composition A R 0 x x
    | nfold_composition_comp : forall n x y z,
        R x y ->
        nfold_composition A R n y z ->
        nfold_composition A R (S n) x z.
  Hint Constructors nfold_composition.

  Definition reducible x := (exists y, R x y).
  Definition in_normal_form x := (forall y, ~R x y).
  Arguments in_normal_form x /.
  Definition normal_form_of x y :=
    (clos_refl_trans _ R x y /\ in_normal_form y).
  Arguments normal_form_of x y /.
  Definition joinable x y :=
    (exists z, clos_refl_trans _ R x z /\ clos_refl_trans _ R y z).
  Arguments joinable x y /.

  Definition Church_Rosser :=
    (forall x y,
    clos_refl_sym_trans _ R x y ->
    joinable x y).
  Definition confluent :=
    (forall x y1 y2,
    clos_refl_trans _ R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2).
  Definition semi_confluent :=
    (forall x y1 y2,
    R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2).

  Definition terminating :=
    (well_founded (fun x y => R y x)).
  Definition normalizing :=
    (forall x, exists y, normal_form_of x y).

  Hint Constructors clos_refl_trans.

  Theorem Church_Rosser_impl_confluent :
    Church_Rosser ->
    confluent.
  Proof.
    intros HCR ? y1 y2 Hrtc1 Hrtc2.
    assert (Hrstc : clos_refl_sym_trans _ R y1 y2) by
    ( apply clos_rt_clos_rst in Hrtc1;
      apply clos_rt_clos_rst in Hrtc2;
      apply rst_sym in Hrtc1;
      eapply rst_trans; eauto ).
    apply HCR.
    apply Hrstc.
  Qed.

  Lemma confluent_impl_semi_confluent :
    confluent ->
    semi_confluent.
  Proof.
    intros Hc x y1 ? HR1 Hrtc2.
    assert (Hrtc1 : clos_refl_trans _ R x y1) by
    ( apply rt_step;
      apply HR1 ).
    eapply Hc.
    - apply Hrtc1.
    - apply Hrtc2.
  Qed.

  Lemma semi_confluent_impl_Church_Rosser :
    semi_confluent ->
    Church_Rosser.
  Proof.
    intros Hsc x ? Hrstc. 
    apply clos_rst_rst1n_iff in Hrstc.
    induction Hrstc as [| ? ? ? [ | ] ]; simpl.
    - eauto.
    - destruct IHHrstc as [? []].
      eauto.
    - destruct IHHrstc as [w []].
      assert (Hjoinable : joinable x w) by
      ( eapply Hsc; eauto ).
      destruct Hjoinable as [? []].
      eauto.
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
    - specialize (Hnf _ HR).
      destruct Hnf.
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
    - specialize (Hnfx _ HR).
      destruct Hnfx.
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
      exists x'.
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

  Definition finitely_branching := forall x, exists ys,
    Forall (R x) ys /\ (forall y, R x y -> In y ys).
  Definition globally_finite := forall x, exists ys,
    Forall (clos_trans _ R x) ys
    /\ (forall y, clos_trans _ R x y -> In y ys).
  Definition acyclic := forall x, ~clos_trans _ R x x.

  Hint Constructors clos_trans.

  Lemma Forall_and_app : forall A (P : A -> Prop) xs ys,
    Forall P xs ->
    Forall P ys ->
    Forall P (xs ++ ys).
  Proof.
    intros.
    apply Forall_forall.
    intros x HIn.
    apply in_app_or in HIn.
    destruct HIn;
      generalize dependent x;
      apply Forall_forall;
      assumption.
  Qed.

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
    (forall x,
    { ys | Forall (R x) ys
        /\ (forall y, R x y -> In y ys) }) ->
    forall x,
    { ys | Forall (clos_trans _ R x) ys
        /\ (forall y, clos_trans _ R x y -> In y ys) }.
  Proof.
    Hint Resolve in_or_app.
    intros Ht Hfb x.
    induction x as [x IH] using (Fix Ht).
    assert (IHy : forall ys acc,
      Forall (R x) ys ->
      Forall (clos_trans _ R x) acc ->
      (forall y, clos_trans _ R x y -> In y acc \/ Exists (fun x' => x' = y \/ clos_trans _ R x' y) ys) ->
      { ys | Forall (clos_trans A R x) ys /\
          (forall y, clos_trans A R x y -> In y ys) }).
    - intros ys.
      induction ys as [| y ys IHys ]; intros acc Hsound ? Hcomplete.
      + exists acc.
        split.
        * assumption.
        * { intros ? Htc.
            destruct (Hcomplete _ Htc) as [| Hcontra ].
            - assumption.
            - inversion Hcontra. }
      + assert (Forall (R x) ys) by (inversion Hsound; subst; eauto).
        assert (HR : R x y) by (inversion Hsound; subst; eauto).
        destruct (IH _ HR) as [zs [Hsound0]].
        apply IHys with (acc := y :: zs ++ acc); eauto.
        * { constructor.
            - eauto.
            - apply Forall_and_app.
              + eapply Forall_impl; [| apply Hsound0 ].
                eauto.
              + eauto. }
        * { intros y' Htc.
            destruct (Hcomplete _ Htc) as [| HExists ]; simpl.
            - eauto.
            - inversion HExists as [ ? ? [ ? | Htc' ] |];
                subst;
                eauto 7. }
    - destruct (Hfb x) as [ys []].
      apply IHy with (ys := ys) (acc := []); eauto.
      intros y Htc.
      right.
      apply Exists_exists.
      apply clos_trans_inversion in Htc.
      destruct Htc as [ | [ ? [ ? Htc' ] ] ]; eauto.
  Defined.

  Definition bounded :=
    forall x, exists n, forall m,
    n <= m ->
    forall y, ~nfold_composition _ R m x y.

  Lemma terminating_iff_bounded :
    finitely_branching ->
    (terminating <-> bounded).
  Proof.
    intros Hfb.
    split.
    - intros Ht x.
      induction x as [ x IH ] using (well_founded_induction Ht).
      assert (IHys : forall ys,
        Forall (R x) ys ->
        forall acc,
        Forall (R x) acc ->
        (forall y, R x y -> In y acc \/ In y ys) ->
        (exists n, forall m,
        n <= m ->
        Forall (fun y => forall z,
          R x y ->
          nfold_composition _ R m y z ->
          False) acc) ->
        exists n, forall m,
        n <= m ->
        forall y, ~nfold_composition _ R m x y).
      + induction 1 as [ | y ? HR ]; intros acc ? Hcomplete [ n Hacc ].
        * { exists (S n).
            intros m ? z Hnfold.
            inversion Hnfold as [ | m' ? ? ? HR ]; subst.
            - omega.
            - assert (Hle : n <= m') by omega.
              specialize (Hacc _ Hle).
              destruct (Hcomplete _ HR) as [ | Hcontra ].
              + eapply Forall_forall in Hacc; eauto.
              + inversion Hcontra. }
        * { apply IHForall with (acc := y :: acc); eauto.
            - intros ? HR'.
              simpl in *.
              destruct (Hcomplete _ HR') as [ | [ | ] ]; eauto.
            - specialize (IH _ HR).
              destruct IH as [ n' IH ].
              destruct (le_dec n n');
                [ exists n'
                | exists n ];
                intros m ?;
                (constructor;
                  [ intros ? HR';
                    apply IH
                  | apply Hacc ];
                  omega). }
      + destruct (Hfb x) as [ ys [ ] ].
        apply IHys with (ys := ys) (acc := []);
          [ | | | exists 0 ];
          eauto.
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
        intros m ? z ?.
        apply Hbounded' with (m := S m) (y := z).
        * omega.
        * eauto.
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
