Require Import Arith List Program.
Require Import Id Types Exp Constraint.

Lemma Forall_app : forall X (P : X -> Prop) l l',
  Forall P (l ++ l') -> Forall P l /\ Forall P l'.
Proof.
  intros ? ? l ? H.
  induction l; simpl in *.
  + eauto.
  + inversion H; subst.
    destruct (IHl H3).
    eauto.
Qed.

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
      typed env (Exp.Bool b) Types.Bool.
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

Fixpoint extract env xs e :=
  match e with
  | Exp.Var x =>
      option_map (fun t => (t, [], xs)) (nth x (map Some env) None)
  | Exp.Abs t1 e =>
      match extract (t1 :: env) xs e with
      | None => None
      | Some (t2, c, xs') => Some (Types.Fun t1 t2, c, xs')
      end
  | Exp.App e1 e2 =>
      match extract env xs e1 with
      | None => None
      | Some (t1, c1, xs') =>
          match extract env xs' e2 with
          | None => None
          | Some (t2, c2, xs'') =>
              let x := Id.FSet.fresh xs'' in
              Some (Types.Var x, (t1, Types.Fun t2 (Types.Var x)) :: c1 ++ c2, Id.FSet.add x xs'')
          end
      end
  | Exp.Bool _ => Some (Types.Bool, [], xs)
  end.

Lemma extract_variables : forall e env xs t c xs',
  extract env xs e = Some (t, c, xs') ->
  Id.FSet.Subset xs xs'.
Proof.
  fix 1.
  intros e ? ? ? ? ? Hextract.
  Hint Resolve
    FSetProperties.subset_trans
    FSetProperties.subset_add_2
    FSetProperties.subset_refl.
  destruct e; simpl in *;
    repeat match goal with
    | H : context [extract ?env ?xs ?e] |- _ =>
        let o := fresh in
        let IHo := fresh in
        remember (extract env xs e) as o eqn:IHo;
        symmetry in IHo;
        destruct o as [[[] ?]|]; simpl in H;
        [ apply extract_variables in IHo
        | congruence ]
    | H : Some _ = Some _ |- _ => inversion H; subst; clear H
    | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
    end; eauto.
  - destruct (nth n (map Some env) None); simpl in *;
    inversion Hextract; subst.
    apply FSetProperties.subset_refl.
Qed.

Lemma extract_sound : forall e env xs t c xs' s,
  extract env xs e = Some (t, c, xs') ->
  Forall (fun t => Id.FSet.Subset (Types.FV t) xs) env ->
  Id.FSet.Subset (Exp.FTV e) xs ->
  unifies s c ->
  typed (map (Types.subst s) env) (Exp.subst_type s e) (Types.subst s t).
Proof.
  fix 1.
  intros e ? ? ? ? ? s Hextract Henv ? ?.
  Hint Resolve FSetProperties.subset_trans.
  destruct e; simpl in *;
    repeat match goal with
    | H : context [extract ?env ?xs ?e] |- _ =>
        let o := fresh in
        let IHo := fresh in
        remember (extract env xs e) as o eqn:IHo;
        symmetry in IHo;
        destruct o as [[[] ?]|]; simpl in H;
        [ generalize (extract_sound _ _ _ _ _ _ s IHo); intros;
          generalize (extract_variables _ _ _ _ _ _ IHo); intros;
          clear IHo
        | congruence ]
    | H : Some _ = Some _ |- _ => inversion H; subst; clear H
    | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
    end;
    repeat (match goal with
    | H : Id.FSet.Subset (Id.FSet.union ?s1 ?s2) ?s3 |- _ =>
        assert (Id.FSet.Subset s1 s3) by (intros ? ?; apply H; eauto);
        assert (Id.FSet.Subset s2 s3) by (intros ? ?; apply H; eauto);
        clear H
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
    end; simpl in *); eauto.
  - remember (nth n (map Some env) None) as o.
    destruct o; simpl in *; inversion Hextract; subst.
    destruct (lt_dec n (length env)).
    + constructor.
      rewrite nth_indep with (d' := Some (Types.subst s Types.Bool)) by (repeat rewrite map_length; omega).
      rewrite nth_indep with (d' := Some Types.Bool) in Heqo by (rewrite map_length; omega).
      repeat rewrite map_nth in *.
      congruence.
    + rewrite nth_overflow in Heqo by (rewrite map_length; omega).
      congruence.
  - econstructor.
    + rewrite H8 in *.
      apply H1; eauto.
    + apply H2; eauto.
      eapply Forall_impl; [| apply Henv ].
      simpl.
      eauto.
Qed.
