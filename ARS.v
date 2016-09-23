Require Import Relations.

Section ARS.
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Notation joinable x y :=
    (exists z, clos_refl_trans _ R x z /\ clos_refl_trans _ R y z).

  Notation Church_Rosser :=
    (forall x y, clos_refl_sym_trans _ R x y -> joinable x y).
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

  Hint Constructors clos_refl_trans.

  Lemma Church_Rosser_impl_confluent : Church_Rosser -> confluent.
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

  Lemma confluent_impl_semi_confluent : confluent -> semi_confluent.
  Proof.
    intros Hc x y1 y2 HR1 Hrtc2.
    assert (Hrtc1 : clos_refl_trans _ R x y1) by
    ( apply rt_step;
      apply HR1 ).
    eapply Hc.
    - apply Hrtc1.
    - apply Hrtc2.
  Qed.

  Lemma semi_confluent_impl_Church_Rosser : semi_confluent -> Church_Rosser.
  Proof.
    intros Hsc ? y Hrstc. 
    apply clos_rst_rst1n_iff in Hrstc.
    induction Hrstc as [| ? ? ? [ HR | HR ] ].
    - eauto.
    - destruct IHHrstc as [? []].
      eauto.
    - destruct IHHrstc as [w []].
      assert (Hjoinable : joinable x w) by
      ( eapply Hsc; eauto ).
      destruct Hjoinable as [? []].
      eauto.
  Qed.
End ARS.
