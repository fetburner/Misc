Require Import List Omega.
Require Id.

Inductive t :=
  | Bool
  | Fun : t -> t -> t
  | Var : Id.t -> t.

Fixpoint FV t :=
  match t with
  | Bool => Id.FSet.empty
  | Fun t1 t2 => Id.FSet.union (FV t1) (FV t2)
  | Var x => Id.FSet.singleton x
  end.

Fixpoint size t :=
  match t with
  | Bool => 1
  | Fun t1 t2 => 1 + size t1 + size t2
  | Var _ => 1
  end.

Fixpoint subst s t :=
  match t with
  | Bool => Bool
  | Fun t1 t2 => Fun (subst s t1) (subst s t2)
  | Var x => s x
  end.

Definition eq_dec : forall t1 t2 : t, { t1 = t2 } + { t1 <> t2 }.
Proof.
  refine (fix eq_dec t1 t2 :=
    match t1 as t1_ return { t1_ = t2 } + { t1_ <> t2 } with
    | Bool =>
        match t2 with
        | Bool => left _
        | _ => right _
        end
    | Fun t11 t12 =>
        match t2 with
        | Fun t21 t22 =>
            if eq_dec t11 t21 then
              if eq_dec t12 t22 then left _
              else right _
            else right _
        | _ => right _
        end
    | Var x =>
        match t2 with
        | Var y =>
            if Id.eq_dec x y then left _
            else right _
        | _ => right _
        end
    end); congruence.
Qed.

Lemma size_gt_0 : forall t,
  0 < size t.
Proof.
  intros t.
  destruct t; simpl in *; omega.
Qed.

Lemma subst_FV : forall x s t,
  Id.FSet.In x (FV (subst s t)) ->
  exists y, Id.FSet.In x (FV (s y)) /\ Id.FSet.In y (FV t).
Proof.
  intros x s t H.
  induction t; simpl in *; eauto.
  - destruct (Id.FSet.empty_spec H).
  - apply Id.FSet.union_spec in H.
    destruct H as [H | H];
    [ destruct (IHt1 H) as [? []]
    | destruct (IHt2 H) as [? []]];
    eauto.
Qed.

Lemma subst_id : forall t, subst Var t = t.
Proof.
  intros t.
  induction t; simpl in *; congruence.
Qed.

Lemma subst_ext : forall s s' t,
  (forall x, Id.FSet.In x (FV t) -> s x = s' x) ->
  subst s t = subst s' t.
Proof.
  intros ? ? t ?.
  induction t; simpl in *; f_equal; eauto.
Qed.

Lemma subst_subst : forall s s' t,
  subst s (subst s' t) = subst (fun x => subst s (s' x)) t.
Proof.
  intros ? ? t.
  induction t; simpl in *; f_equal; eauto.
Qed.

Lemma unifies_occur : forall x t,
  Var x <> t -> Id.FSet.In x (FV t) -> forall s, s x <> subst s t.
Proof.
  intros x t ? ? s Hunifies.
  assert (Hsize : size (subst s t) <= size (s x)) by (rewrite Hunifies; omega).
  clear Hunifies.
  induction t; simpl in *.
  - destruct (Id.FSet.empty_spec H0).
  - apply Id.FSet.union_spec in H0.
    destruct H0; [ apply IHt1 | apply IHt2 ];
      try (intros Hcontra; rewrite <- Hcontra in *; simpl in *);
      solve [ omega | eauto ].
  - apply Id.FSet.singleton_spec in H0.
    congruence.
Qed.

Definition subst_single x t1 y :=
  if Id.eq_dec x y then t1
  else Var y.

Lemma subst_single_preserves_unifies : forall x t0 s t,
  s x = subst s t0 ->
  subst s (subst (subst_single x t0) t) = subst s t.
Proof.
  intros ? ? ? t ?.
  induction t; simpl in *; f_equal; eauto.
  unfold subst_single.
  destruct (Id.eq_dec x t1); subst; eauto.
Qed.
