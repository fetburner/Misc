Require Import Arith List Omega Relations Program.

Module Types.
  Inductive t :=
    | Base
    | Fun : t -> t -> t.
End Types.

Module Exp.
  Inductive t :=
    | Var : nat -> t
    | Abs : Types.t -> t -> t
    | App : t -> t -> t.

  Fixpoint shift c d e :=
    match e with
    | Var x => Var (if lt_dec x c then x else d + x)
    | Abs t e => Abs t (shift (S c) d e)
    | App e1 e2 => App (shift c d e1) (shift c d e2)
    end.

  Fixpoint subst x es e :=
    match e with
    | Var y =>
        if le_dec x y then shift 0 x (nth (y - x) es (Var (y - x - length es)))
        else Var y
    | Abs t e => Abs t (subst (S x) es e)
    | App e1 e2 => App (subst x es e1) (subst x es e2)
    end.
End Exp.

Inductive value : Exp.t -> Prop :=
  | V_Abs : forall e t, value (Exp.Abs t e).
Hint Constructors value.

Inductive simplto : Exp.t -> Exp.t -> Prop :=
  | S_AppL : forall e1 e1' e2,
      simplto e1 e1' ->
      simplto (Exp.App e1 e2) (Exp.App e1' e2)
  | S_AppR : forall v1 e2 e2',
      value v1 ->
      simplto e2 e2' ->
      simplto (Exp.App v1 e2) (Exp.App v1 e2')
  | S_App : forall e t v2,
      value v2 ->
      simplto (Exp.App (Exp.Abs t e) v2) (Exp.subst 0 [v2] e).
Hint Constructors simplto.

Inductive typed : list Types.t -> Exp.t -> Types.t -> Prop :=
  | T_Var : forall env x d,
      x < length env ->
      typed env (Exp.Var x) (nth x env d)
  | T_Abs : forall env e t1 t2,
      typed (t1 :: env) e t2 ->
      typed env (Exp.Abs t1 e) (Types.Fun t1 t2)
  | T_App : forall env e1 e2 t1 t2,
      typed env e1 (Types.Fun t1 t2) ->
      typed env e2 t1 ->
      typed env (Exp.App e1 e2) t2.
Hint Constructors typed.

Lemma typed_weakening : forall env env' e t,
  typed env e t ->
  typed (env ++ env') e t.
Proof.
  intros ? ? ? ? Htyped.
  induction Htyped; eauto.

  erewrite <- app_nth1 by omega.
  econstructor.
  rewrite app_length.
  omega.
Qed.

Lemma typed_shift : forall env e t,
  typed env e t ->
  forall env' env'' env''',
  env = env' ++ env''' ->
  typed (env' ++ env'' ++ env''') (Exp.shift (length env') (length env'') e) t.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros env' env'' env''' ?; subst; simpl; eauto.
  - destruct (lt_dec x (length env')).
    + rewrite app_nth1 by omega.
      apply typed_weakening.
      auto.
    + replace (nth x (env' ++ env''') d)
      with (nth (length env'' + x) (env' ++ env'' ++ env''') d).
      * constructor.
        repeat rewrite app_length in *.
        omega.
      * repeat rewrite app_nth2 by omega.
        f_equal.
        omega.
  - constructor.
    apply (IHHtyped (t1 :: env')).
    eauto.
Qed.

Lemma canonical_form_fun : forall v t1 t2,
  value v ->
  typed [] v (Types.Fun t1 t2) ->
  exists e, v = Exp.Abs t1 e.
Proof.
  intros ? ? ? Hvalue Htyped.
  inversion Hvalue; subst; inversion Htyped; eauto.
Qed.

Lemma substitution : forall e1 t1 env,
  typed env e1 t1 ->
  forall env' env'' e2 t2,
  env = env' ++ t2 :: env'' ->
  typed env'' e2 t2 ->
  typed (env' ++ env'') (Exp.subst (length env') [e2] e1) t1.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros env' ? ? ? ? Htyped'; subst; simpl in *; eauto.
  - destruct (le_dec (length env') x); rewrite app_length in *; simpl in *.
    + rewrite app_nth2 by omega.
      eapply typed_shift with (env' := []); [| reflexivity ].
      remember (x - length env') as y.
      destruct y as [| y ].
      * eauto.
      * destruct y; simpl; constructor; omega.
    + rewrite app_nth1 by omega.
      apply typed_weakening.
      constructor.
      omega.
  - constructor.
    eapply (IHHtyped (t1 :: env')); simpl; eauto.
Qed.

Lemma preservation : forall e e',
  simplto e e' ->
  forall env t,
  typed env e t ->
  typed env e' t.
Proof.
  intros ? ? Hsimplto.
  induction Hsimplto; intros ? ? Htyped; inversion Htyped; eauto.
  
  inversion H3.
  eapply substitution with (env' := []); [| reflexivity |]; eauto.
Qed.

Lemma progress : forall e t,
  typed [] e t ->
  value e \/ exists e', simplto e e'.
Proof.
  intros ? ? Htyped.
  remember [] as env.
  induction Htyped; subst; simpl in *; eauto.
  - omega.
  - destruct (IHHtyped1 eq_refl) as [| []]; [| eauto ].
    destruct (canonical_form_fun _ _ _ H Htyped1).
    subst.
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

