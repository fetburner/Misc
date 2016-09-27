Require Import Relations Program.

Section ARS.
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Notation reducible x := (exists y, R x y).
  Notation in_normal_form x := (forall y, ~R x y).
  Notation normal_form_of x y :=
    (clos_refl_trans _ R x y /\ in_normal_form y).
  Notation joinable x y :=
    (exists z, clos_refl_trans _ R x z /\ clos_refl_trans _ R y z).

  Notation Church_Rosser :=
    (forall x y,
    clos_refl_sym_trans _ R x y ->
    joinable x y).
  Notation confluent :=
    (forall x y1 y2,
    clos_refl_trans _ R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2).
  Notation semi_confluent :=
    (forall x y1 y2,
    R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2).

  Notation terminating :=
    (well_founded (fun x y => R y x)).
  Notation normalizing :=
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
    induction Hrstc as [| ? ? ? [ | ] ].
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
    normalizing ->
    confluent ->
    forall x, exists! y, normal_form_of x y.
  Proof.
    intros Hn Hc x.
    destruct (Hn x) as [y].
    exists y.
    split.
    - eauto.
    - intros ?.
      apply confluent_most_one_normal_form; eauto.
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
End ARS.
