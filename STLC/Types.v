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

Fixpoint subst x t0 t :=
  match t with
  | Bool => Bool
  | Fun t1 t2 => Fun (subst x t0 t1) (subst x t0 t2)
  | Var y =>
      if Id.eq_dec x y then t0
      else Var y
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

Lemma subst_occur : forall x t1 t2,
  Id.FSet.In x (FV (subst x t1 t2)) ->
  Id.FSet.In x (FV t1).
Proof.
  intros x t1 t2 ?.
  induction t2; simpl in *; eauto.
  - destruct (Id.FSet.empty_spec H).
  - apply Id.FSet.union_spec in H.
    destruct H; eauto.
  - destruct (Id.eq_dec x t0); simpl in *.
    + eauto.
    + eapply Id.FSet.singleton_spec in H.
      congruence.
Qed.

Lemma subst_fv : forall x y t1 t2,
  Id.FSet.In x (FV (subst y t1 t2)) ->
  Id.FSet.In x (FV t1) \/ Id.FSet.In x (FV t2).
Proof.
  intros ? ? ? t2 ?.
  induction t2; simpl in *; eauto.
  - apply Id.FSet.union_spec in H.
    destruct H as [ H | H ];
    [ destruct (IHt2_1 H)
    | destruct (IHt2_2 H) ]; eauto 9.
  - destruct (Id.eq_dec y t0); eauto.
Qed.

Lemma subst_notin_fv : forall x t1 t2,
  ~Id.FSet.In x (FV t2) -> subst x t1 t2 = t2.
Proof.
  intros ? ? t2 ?.
  induction t2; simpl in *; f_equal; eauto 6.
  - destruct (Id.eq_dec x t0).
    + exfalso.
      apply H.
      apply Id.FSet.singleton_spec.
      eauto.
    + eauto.
Qed.

Definition subst_list s t :=
  (fold_left (fun t s =>
    subst (fst s) (snd s) t) s t).

Lemma subst_list_Bool : forall s,
  subst_list s Bool = Bool.
Proof.
  intros s.
  induction s; simpl; eauto.
Qed.

Lemma subst_list_Fun : forall s t1 t2,
  subst_list s (Fun t1 t2) = Fun (subst_list s t1) (subst_list s t2).
Proof.
  intros s.
  induction s; intros ? ?; simpl; eauto.
Qed.

Notation unifies s t1 t2 :=
  (subst_list s t1 = subst_list s t2).

Lemma subst_preserves_unifies : forall x t0 s t,
  unifies s (Var x) t0 ->
  unifies s t (subst x t0 t).
Proof.
  intros ? ? ? t ?.
  induction t; simpl in *; eauto.
  - repeat rewrite subst_list_Fun.
    f_equal; eauto.
  - destruct (Id.eq_dec x t1); subst; eauto.
Qed.

Lemma unifies_occur : forall x t,
  Var x <> t -> Id.FSet.In x (FV t) -> forall s, ~unifies s (Var x) t.
Proof.
  intros x t ? ? s Hunifies.
  assert (Hsize : size (subst_list s t) <= size (subst_list s (Var x))) by (rewrite Hunifies; omega).
  clear Hunifies.
  induction t; simpl in *.
  - destruct (Id.FSet.empty_spec H0).
  - apply Id.FSet.union_spec in H0.
    rewrite subst_list_Fun in *.
    simpl in *.
    destruct H0; [ apply IHt1 | apply IHt2 ]; eauto;
      try (intros Hcontra; rewrite Hcontra in *);
      omega.
  - apply Id.FSet.singleton_spec in H0.
    congruence.
Qed.
