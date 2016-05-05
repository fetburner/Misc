Require Import Arith List Program.
Require Import Id Types Exp.

Inductive typed : list Types.t -> Exp.t -> Types.t -> Prop :=
  | T_Var : forall env x t,
      nth x (map Some env) None = Some t ->
      typed env (Exp.Var x) t
  | T_Abs : forall env e t1 t2,
      typed (t1 :: env) e t2 ->
      typed env (Exp.Abs t1 e) (Types.Fun t1 t2)
  | T_App : forall env e1 e2 t1 t2,
      typed env e1 (Types.Fun t1 t2) ->
      typed env e2 t1 ->
      typed env (Exp.App e1 e2) t2
  | T_Bool : forall env b,
      typed env (Exp.Bool b) Types.Bool
  | T_If : forall env e1 e2 e3 t,
      typed env e1 Types.Bool ->
      typed env e2 t ->
      typed env e3 t ->
      typed env (Exp.If e1 e2 e3) t.
Hint Constructors typed.

Lemma typed_shift : forall env e t,
  typed env e t ->
  forall env' env'' env''',
  env = env' ++ env''' ->
  typed (env' ++ env'' ++ env''') (Exp.shift (length env') (length env'') e) t.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros env' env'' env''' ?; subst; simpl; eauto.
  - destruct (le_dec (S x) (length env')); econstructor; repeat rewrite map_app in *.
    + rewrite app_nth1 in * by (rewrite map_length; omega).
      assumption.
    + repeat rewrite app_nth2 in * by (repeat rewrite map_length; omega).
      repeat rewrite map_length in *.
      replace (length env'' + x - length env' - length env'')
      with (x - length env') by omega.
      assumption.
  - constructor.
    apply (IHHtyped (t1 :: env')).
    reflexivity.
Qed.

Lemma substitution : forall e t env,
  typed env e t ->
  forall env' t' env'' v,
  env = env' ++ t' :: env'' ->
  typed env'' v t' ->
  typed (env' ++ env'') (Exp.subst (length env') [v] e) t.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros env' ? ? ? ? ?; subst; simpl in *; eauto.
  - rewrite map_app in *.
    destruct (le_dec (length env') x).
    + rewrite app_nth2 in * by (rewrite map_length; omega).
      eapply typed_shift with (env' := []); [| reflexivity ].
      rewrite map_length in *.
      remember (x - length env') as y.
      destruct y; simpl in *.
      * congruence.
      * destruct y; rewrite <- minus_n_O; eauto.
    + econstructor.
      rewrite map_app.
      repeat rewrite app_nth1 in * by (rewrite map_length; omega).
      assumption.
  - constructor.
    eapply (IHHtyped (t1 :: env')); simpl; eauto.
Qed.

Lemma canonical_form_fun : forall v t1 t2,
  Exp.value v ->
  typed [] v (Types.Fun t1 t2) ->
  exists e, v = Exp.Abs t1 e.
Proof.
  intros ? ? ? Hv Htyped.
  inversion Hv; subst; inversion Htyped; eauto.
Qed.

Lemma canonical_form_bool : forall v,
  Exp.value v ->
  typed [] v Types.Bool ->
  exists b, v = Exp.Bool b.
Proof.
  intros ? Hv Htyped.
  inversion Hv; subst; inversion Htyped; eauto.
Qed.
