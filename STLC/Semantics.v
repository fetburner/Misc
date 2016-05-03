Require Import Relations.
Require Types Exp.
Require Import Bigstep Smallstep.

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
  - eapply rt_trans.
    + eapply S_If_multi.
      eauto.
    + eauto.
  - eapply rt_trans.
    + eapply S_If_multi.
      eauto.
    + eauto.
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
