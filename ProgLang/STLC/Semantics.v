Require Import Relations.
Require Id Types Exp.
Require Import BigstepSubst SmallstepCbv.

Theorem evalto_impl_simplto_multi : forall e v,
  evalto e v ->
  clos_refl_trans _ simplto e v.
Proof.
  Hint Constructors clos_refl_trans.
  intros ? ? Hevalto.
  induction Hevalto; eauto.
  - eapply rt_trans.
    + eapply S_AppL_multi.
      eauto.
    + eapply rt_trans.
      * eapply S_AppR_multi; eauto.
      * eauto.
Qed.

Lemma simplto_preserves_evalto : forall e e',
  simplto e e' ->
  forall v,
  evalto e' v ->
  evalto e v.
Proof.
  intros ? ? Hsimplto.
  induction Hsimplto;
    intros ? Hevalto;
    inversion Hevalto;
    subst;
    eauto.
Qed.
Hint Resolve simplto_preserves_evalto.

Lemma simplto_preserves_diverge : forall e e',
  simplto e e' ->
  diverge e' ->
  diverge e.
Proof.
  intros ? ? Hsimplto Hdiverge.
  induction Hsimplto;
    inversion Hdiverge;
    subst;
    eauto.
Qed.

Theorem simplto_multi_impl_evalto : forall e v,
  clos_refl_trans _ simplto e v ->
  Exp.value v ->
  evalto e v.
Proof.
  intros ? ? Hsimplto ?.
  apply clos_rt_rt1n in Hsimplto.
  Hint Constructors clos_refl_trans_1n.
  induction Hsimplto; eauto.
Qed.

Lemma diverge_impl_simpl : forall e,
  diverge e ->
  exists e', simplto e e' /\ diverge e'.
Proof.
  Ltac extract_evalto H :=
    (let H' := fresh in
    generalize (evalto_value _ _ H); intros H';
    apply evalto_impl_simplto_multi in H;
    apply clos_rt_rt1n in H;
    inversion H; subst; clear H;
      [| match goal with
         | H : clos_refl_trans_1n _ simplto _ ?v, H' : Exp.value ?v |- _ =>
             apply clos_rt1n_rt in H;
             generalize (simplto_multi_impl_evalto _ _ H H'); intros ?
         end ]).
  intros e Hdiverge.
  induction e; inversion Hdiverge; subst.
  - destruct (IHe1 H0) as [? []].
    eauto.
  - extract_evalto H1; eauto.
    destruct (IHe2 H2) as [? []]; eauto 7.
  - extract_evalto H1; eauto.
    extract_evalto H2; eauto.
Qed.
