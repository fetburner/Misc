Require Import Arith List Omega Program.

Module Types.
  Inductive t :=
    | Bool : t
    | Fun : t -> t -> t.
End Types.

Module Exp.
  Inductive t :=
    | Var : nat -> t
    | Abs : Types.t -> t -> t
    | App : t -> t -> t.

  Fixpoint shift c d e :=
    match e with
    | Var x => Var (if le_dec (S x) c then x else d + x)
    | Abs t e => Abs t (shift (S c) d e)
    | App e1 e2 => App (shift c d e1) (shift c d e2)
    end.

  Ltac elim_shift_subst_var :=
    repeat (match goal with
    | |- context [le_dec ?x ?c] => destruct (le_dec x c)
    | H : context [le_dec ?x ?c] |- _ => destruct (le_dec x c)
    end; simpl in *).

  Lemma shift_0 : forall e c,
    shift c 0 e = e.
  Proof.
    intros e.
    induction e; intros ?; simpl;
      f_equal;
      elim_shift_subst_var;
      eauto.
  Qed.
  Hint Rewrite shift_0.

  Fixpoint subst x es e :=
    match e with
    | Var y => 
        if le_dec x y then shift 0 x (nth (y - x) es (Var (y - x - length es)))
        else Var y
    | Abs t e => Abs t (subst (S x) es e)
    | App e1 e2 => App (subst x es e1) (subst x es e2)
    end.

  Lemma subst_ignore : forall e c d x es,
    c <= x ->
    length es + x <= d + c ->
    subst x es (shift c d e) = shift c (d - length es) e.
  Proof.
    fix 1.
    intros e ? ? ? ? ? ?.
    destruct e; simpl; f_equal;
      try apply subst_ignore;
      try omega.
    repeat ((rewrite nth_overflow by omega; simpl)
      || elim_shift_subst_var);
    f_equal; omega.
  Qed.
  Hint Rewrite subst_ignore using (simpl; omega).

  Lemma subst_meld : forall e x x' es es',
    x' = length es + x ->
    subst x es (subst x' es' e) = subst x (es ++ es') e.
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    subst.
    destruct e; simpl;
      f_equal;
      auto.
    elim_shift_subst_var; auto; try omega.
    + rewrite subst_ignore by omega.
      rewrite app_nth2 by omega.
      rewrite app_length.
      repeat (f_equal; try omega).
    + rewrite app_nth1 by omega.
      f_equal.
      apply nth_indep.
      omega.
  Qed.

  Lemma subst_nil : forall x e,
    subst x [] e = e.
  Proof.
    fix 2.
    intros ? e.
    destruct e; simpl;
      f_equal;
      eauto.
    elim_shift_subst_var; auto.
    remember (n - x) as y.
    destruct y; simpl; elim_shift_subst_var; f_equal; omega.
  Qed.
End Exp.

Inductive value : Exp.t -> Prop :=
  | V_Abs : forall e t, value (Exp.Abs t e).
Hint Constructors value.

Inductive evalto : Exp.t -> Exp.t -> Prop :=
  | E_Abs : forall e t,
      evalto (Exp.Abs t e) (Exp.Abs t e)
  | E_App : forall e1 e2 e v2 v t,
      evalto e1 (Exp.Abs t e) ->
      evalto e2 v2 ->
      evalto (Exp.subst 0 [v2] e) v ->
      evalto (Exp.App e1 e2) v.

CoInductive diverge : Exp.t -> Prop :=
  | D_AppL : forall e1 e2,
      diverge e1 ->
      diverge (Exp.App e1 e2)
  | D_AppR : forall e1 e2 v1,
      evalto e1 v1 ->
      diverge e2 ->
      diverge (Exp.App e1 e2)
  | D_App : forall e1 e2 e v2 t,
      evalto e1 (Exp.Abs t e) ->
      evalto e2 v2 ->
      diverge (Exp.subst 0 [v2] e) ->
      diverge (Exp.App e1 e2).
Hint Constructors evalto diverge.

Lemma evalto_ident : forall v,
  value v ->
  evalto v v.
Proof.
  intros ? Hv.
  inversion Hv; eauto.
Qed.
Hint Resolve evalto_ident.

Lemma evalto_deterministic : forall e v,
  evalto e v ->
  forall v',
  evalto e v' ->
  v = v'.
Proof.
  intros e v Hevalto.
  induction Hevalto; intros v' Hevalto'; inversion Hevalto';
  repeat (subst; match goal with
    | [ Hevalto : evalto ?t ?v, IH : forall v, evalto ?t v -> _ = v |- _ ] =>
        let H := fresh in
        generalize (IH _ Hevalto); intros H;
        inversion H;
        clear Hevalto
    end); congruence.
Qed.

Lemma evalto_diverge_disjoint : forall e v,
  evalto e v -> diverge e -> False.
Proof.
  intros e v Hevalto Hdiverge.
  induction Hevalto; inversion Hdiverge; subst; eauto.
  repeat (match goal with
    | H : evalto ?e _, H' : evalto ?e _ |- _ =>
        generalize (evalto_deterministic _ _ H _ H');
        intros;
        clear H
    | H : Exp.Abs _ _ = Exp.Abs _ _ |- _ => inversion H
    end; subst); eauto.
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
      typed env (Exp.App e1 e2) t2.
Hint Constructors typed.

(* ugly definition... *)
Fixpoint V t v : Prop :=
  match t with
  | Types.Bool => False
  | Types.Fun t1 t2 =>
      exists e,
      v = Exp.Abs t1 e /\ (forall v, V t1 v ->
      (* exp t2 (Exp.subst 0 [v] e) *)
      (exists v', evalto (Exp.subst 0 [v] e) v' /\ V t2 v')
      \/ diverge (Exp.subst 0 [v] e))
  end.

Lemma V_impl_value : forall t v,
  V t v ->
  value v.
Proof.
  intros t v ?.
  destruct t; destruct v; simpl in *;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : False |- _ => destruct H
    end; solve [ congruence | auto ].
Qed.
Hint Resolve V_impl_value.

Lemma fundamental_property : forall env e t,
  typed env e t ->
  forall vs,
  length env = length vs ->
  (forall i v t,
    nth i (map Some vs) None = Some v ->
    nth i (map Some env) None = Some t ->
    V t v) ->
  (exists v, evalto (Exp.subst 0 vs e) v /\ V t v)
  \/ diverge (Exp.subst 0 vs e).
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros vs Hlength Henv; simpl in *.
  - left.
    rewrite Exp.shift_0 in *.
    rewrite <- minus_n_O in *.
    destruct (lt_dec x (length vs)).
    + assert (HV : V t (nth x vs (Exp.Var (x - length vs)))).
      * eapply Henv; [| eassumption ].
        rewrite <- map_nth with (f := Some).
        apply nth_indep.
        rewrite map_length.
        assumption.
      * eauto.
    + rewrite nth_overflow in * by (rewrite map_length; omega).
      discriminate.
  - left.
    eexists.
    split; [ constructor |].
    eexists.
    split; [ reflexivity |].
    intros ? ?.
    rewrite Exp.subst_meld by (simpl; omega).
    apply IHHtyped; simpl; [ congruence |].
    intros i ? ? ? ?.
    destruct i.
    * congruence.
    * eapply Henv; eassumption.
  - destruct (IHHtyped1 _ Hlength Henv) as [[? [? [? [? Hsubst]]]] | ]; eauto.
    subst.
    destruct (IHHtyped2 _ Hlength Henv) as [[? [? HV]]| ]; eauto.
    destruct (Hsubst _ HV) as [[? []]|]; eauto.
Qed.
            
Lemma type_safety : forall e t,
  typed [] e t ->
  (exists v, evalto e v) \/ diverge e.
Proof.
  intros ? ? Htyped.
  apply fundamental_property with (vs := []) in Htyped; auto.
  - rewrite Exp.subst_nil in *.
    destruct Htyped as [[? []]|]; eauto.
  - intros i ? ? ? ?.
    destruct i; simpl in *; discriminate.
Qed.
