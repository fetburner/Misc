Require Import List Relations Program.
Require Import Id Types Exp SmallstepCbv Typing.

Lemma preservation : forall e e',
  simplto e e' ->
  forall env t,
  typed env e t ->
  typed env e' t.
Proof.
  intros ? ? Hsimplto.
  induction Hsimplto; intros ? ? Htyped; inversion Htyped; eauto.

  inversion H3.
  eapply substitution with (env' := []); eauto.
  reflexivity.
Qed.

Lemma progress : forall e t,
  typed [] e t ->
  value e \/ exists e', simplto e e'.
Proof.
  intros ? ? Htyped.
  remember [] as env.
  induction Htyped; subst; simpl in *; eauto.
  - destruct x; congruence.
  - destruct (IHHtyped1 eq_refl) as [ H | []]; [| eauto ].
    destruct (canonical_form_fun _ _ _ H Htyped1); subst.
    destruct (IHHtyped2 eq_refl) as [| []]; eauto.
Qed.

Theorem type_safety : forall e e',
  clos_refl_trans _ simplto e e' ->
  forall t,
  typed [] e t ->
  value e' \/ exists e'', simplto e' e''.
Proof.
  intros ? ? H.
  apply clos_rt_rt1n in H.
  Hint Resolve preservation progress.
  induction H; intros ? Htyped; eauto.
Qed.

