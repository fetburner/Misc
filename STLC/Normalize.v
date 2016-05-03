Require Import Arith List Program.
Require Import Syntax Bigstep Typing.

(* ugly definition... *)
Fixpoint V t v : Prop :=
  match t with
  | Types.Bool => False
  | Types.Fun t1 t2 =>
      exists e,
      v = Exp.Abs t1 e /\ (forall v, V t1 v ->
      (* exp t2 (Exp.subst 0 [v] e) *)
      exists v', evalto (Exp.subst 0 [v] e) v' /\ V t2 v')
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
  exists v, evalto (Exp.subst 0 vs e) v /\ V t v.
Proof.
  intros ? ? ? Htyped.
  induction Htyped; intros vs Hlength Henv; simpl in *.
  - rewrite Exp.shift_0 in *.
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
  - eexists.
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
  - destruct (IHHtyped1 _ Hlength Henv) as [? [? [? [? Hsubst]]]].
    subst.
    destruct (IHHtyped2 _ Hlength Henv) as [? [? HV]].
    destruct (Hsubst _ HV) as [? []].
    eauto.
Qed.
            
Lemma normalize : forall e t,
  typed [] e t ->
  exists v, evalto e v.
Proof.
  intros ? ? Htyped.
  apply fundamental_property with (vs := []) in Htyped; auto.
  - rewrite Exp.subst_nil in *.
    destruct Htyped as [? []]; eauto.
  - intros i ? ? ? ?.
    destruct i; simpl in *; discriminate.
Qed.
