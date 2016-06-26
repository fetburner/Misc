Require Import Arith List Program.
Require Id Types Exp.
Require Import SmallstepFullBeta Typing.

Notation SN e :=
  (Acc (fun e e' => red e' e) e).

Fixpoint reducible e t :=
  match t with
  | Types.Var _ => SN e
  | Types.Bool => SN e
  | Types.Fun t1 t2 =>
      forall v, reducible v t1 -> reducible (Exp.App e v) t2
  end.
Hint Constructors Acc.

Inductive neutral : Exp.t -> Prop :=
  | N_App : forall e1 e2,
      neutral (Exp.App e1 e2)
  | N_Bool : forall b,
      neutral (Exp.Bool b).
Hint Constructors neutral.

Lemma CR2 : forall t e e',
  red e e' ->
  reducible e t -> reducible e' t.
Proof.
  intros t.
  induction t; intros ? ? ? Hreducible; simpl in *;
    solve [ eauto | inversion Hreducible; eauto ]. 
Qed.
Hint Resolve CR2.

Lemma CR1_CR3 : forall t,
  (forall e, reducible e t -> SN e) /\
  (forall e, neutral e ->
    (forall e', red e e' -> reducible e' t) -> reducible e t).
Proof.
  intros t.
  induction t; split; simpl in *; eauto.
  - intros ? H.
    destruct IHt1 as [ IHt1C1 IHt1C3 ].
    assert (Hc : reducible (Exp.Bool true) t1).
    + apply IHt1C3; eauto.
      intros ? Hred.
      inversion Hred.
    + apply H in Hc.
      destruct IHt2 as [ IHt2C1 ].
      apply IHt2C1 in Hc.
      clear H.
      remember (Exp.App e (Exp.Bool true)) as e'.
      generalize dependent e.
      induction Hc; intros; subst.
      eauto.
  - intros ? Hneutral H ? HRt1.
    destruct IHt1 as [ IHt1C1 IHt1C3 ].
    destruct IHt2 as [ IHt2C1 IHt2C3 ].
    apply IHt2C3; eauto.
    specialize (IHt1C1 _ HRt1).
    induction IHt1C1.
    intros ? Hred.
    inversion Hred; subst; eauto.
    inversion Hneutral.
Qed.

Let CR1 t := proj1 (CR1_CR3 t).
Let CR3 t := proj2 (CR1_CR3 t).
Hint Resolve CR1.

Lemma reducible_abs : forall e1 t1 t2,
  (forall v, reducible v t1 -> reducible (Exp.subst 0 [v] e1) t2) ->
  reducible (Exp.Abs t1 e1) (Types.Fun t1 t2).
Proof.
  simpl.
  intros ? ? ? Hsubst ? Hreducible.
  generalize (CR1 _ _ Hreducible). intros HSN.
  generalize (CR1 _ _ (Hsubst _ Hreducible)). intros HSNsubst.
  generalize dependent e1.
  induction HSN as [? ? IH].
  intros.
  remember (Exp.subst 0 [x] e1) as e.
  generalize dependent e1.
  generalize dependent x.
  induction HSNsubst as [? ? IH'].
  intros.
  apply CR3; eauto.
  intros ? Hred.
  inversion Hred; subst; eauto 7.
  inversion H4; subst.
  eapply IH'; try reflexivity; eauto.
Qed.

Lemma fundamental_property : forall tenv e t,
  typed tenv e t ->
  forall env,
  length env = length tenv ->
  (forall i e t,
    nth i (map Some env) None = Some e ->
    nth i (map Some tenv) None = Some t ->
    reducible e t) ->
  reducible (Exp.subst 0 env e) t.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros ? Hlength Henv; simpl in *; eauto.
  - rewrite Exp.shift_0.
    rewrite <- minus_n_O.
    destruct (lt_dec x (length env)).
    + eapply Henv; eauto.
      rewrite <- map_nth with (f := Some).
      apply nth_indep.
      rewrite map_length.
      omega.
    + rewrite nth_overflow in * by (rewrite map_length; omega).
      congruence.
  - apply reducible_abs.
    intros ? ?.
    rewrite Exp.subst_meld; simpl; eauto.
    apply IHHtyped; simpl; eauto.
    intros i ? ? ? ?.
    destruct i.
    + congruence.
    + eapply Henv; eauto.
  - constructor.
    intros ? Hcontra.
    inversion Hcontra.
Qed.

Theorem strong_normalize : forall e t,
  typed [] e t ->
  SN e.
Proof.
  intros ? ? ?.
  apply fundamental_property with (env := []) in H; simpl; eauto.
  - rewrite Exp.subst_nil in *.
    eauto.
  - intros [] ? ?; congruence.
Qed.
