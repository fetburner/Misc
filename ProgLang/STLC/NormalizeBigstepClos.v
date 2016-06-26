Require Import Arith List Omega Program.
Require Id Exp Types.
Require Import BigstepClos Typing.

Fixpoint SN v t :=
  match t with
  | Types.Var _ =>
      False
  | Types.Bool =>
      exists b, v = Value.Bool b
  | Types.Fun t1 t2 =>
      exists env e, v = Value.Clos env e
      /\ (forall v1, SN v1 t1 -> exists v2, evalto (v1 :: env) e v2 /\ SN v2 t2)
  end.

Lemma fundamental_theory : forall tenv e t,
  typed tenv e t ->
  forall env,
  length tenv = length env ->
  (forall i v t,
    nth i (map Some env) None = Some v ->
    nth i (map Some tenv) None = Some t ->
    SN v t) ->
  exists v, evalto env e v /\ SN v t.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros ? Hlength Henv; simpl in *; eauto.
  - destruct (lt_dec x (length env)).
    + exists (nth x env0 (Value.Bool true)).
      split.
      * econstructor.
        rewrite <- map_nth with (f := Some).
        apply nth_indep.
        rewrite map_length.
        omega.
      * eapply Henv; eauto.
        rewrite <- map_nth with (f := Some).
        apply nth_indep.
        rewrite map_length.
        omega.
    + rewrite nth_overflow in * by (rewrite map_length; omega).
      congruence.
  - eexists.
    split; eauto.
    do 2 eexists.
    split; eauto.
    intros ? ?.
    apply IHHtyped; simpl; eauto.
    intros i ? ? ? ?.
    destruct i.
    + congruence.
    + eauto.
  - destruct (IHHtyped1 _ Hlength Henv) as [? [? [? [? [? Hsubst]]]]].
    destruct (IHHtyped2 _ Hlength Henv) as [? [? HSN]].
    subst.
    destruct (Hsubst _ HSN) as [? []].
    eauto.
Qed.

Theorem normalize : forall e t,
  typed [] e t ->
  exists v, evalto [] e v.
Proof.
  intros ? ? ?.
  assert (Hfund : exists v, evalto [] e v /\ SN v t).
  - eapply fundamental_theory; eauto.
    simpl.
    intros i ? ? ? ?.
    destruct i; congruence.
  - destruct Hfund as [? []].
    eauto.
Qed.
