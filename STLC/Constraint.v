Require Import List Recdef Omega Finite_sets_facts.
Require Id Types.

Lemma Forall_map : forall X Y (P : Y -> Prop) (f : X -> Y) l,
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  intros ? ? ? ? l.
  split; intros H.
  - apply Forall_forall.
    intros ? ?.
    Hint Resolve in_map.
    eapply Forall_forall in H; eauto.
  - induction l;
    simpl;
    inversion H;
    eauto.
Qed.

Definition t := list (Types.t * Types.t).

Notation FV c :=
  (fold_right Id.FSet.union Id.FSet.empty
    (map (fun p => Id.FSet.union (Types.FV (fst p)) (Types.FV (snd p))) c)).

Notation size c :=
  (fold_right plus 0 (map (fun p =>
    Types.size (fst p) + Types.size (snd p)) c)).

Notation subst x t c :=
  (map (fun p => (Types.subst x t (fst p), Types.subst x t (snd p))) c).

Notation subst_list s c :=
  (map (fun p => (Types.subst_list s (fst p), Types.subst_list s (snd p))) c).

Notation unifies s c :=
  (Forall (fun p => Types.unifies s (fst p) (snd p)) c).

Lemma subst_occur : forall x t c,
  Id.FSet.In x (FV (subst x t c)) -> Id.FSet.In x (Types.FV t).
Proof.
  intros ? ? c H.
  induction c as [| [] ]; simpl in *.
  - destruct (Id.FSet.empty_spec H).
  - apply Id.FSet.union_spec in H.
    destruct H as [ H | H ].
    + apply Id.FSet.union_spec in H.
      Hint Resolve Types.subst_occur.
      destruct H; eauto.
    + eauto.
Qed.

Lemma subst_fv : forall x y t c,
  Id.FSet.In x (FV (subst y t c)) -> Id.FSet.In x (Types.FV t) \/ Id.FSet.In x (FV c).
Proof.
  intros ? ? ? c H.
  induction c as [| [] ]; simpl in *.
  - destruct (Id.FSet.empty_spec H).
  - apply Id.FSet.union_spec in H.
    destruct H as [ H | H ].
    + apply Id.FSet.union_spec in H.
      destruct H as [ H | H ];
      destruct (Types.subst_fv _ _ _ _ H); eauto 6.
    + destruct (IHc H); eauto.
Qed.

Lemma subst_preserves_unifies : forall x t0 s c,
  Types.unifies s (Types.Var x) t0 ->
  unifies s c ->
  unifies s (subst x t0 c).
Proof.
  intros ? ? ? ? ? ?.
  apply Forall_map.
  eapply Forall_impl; [| eauto ].
  intros [] ?.
  simpl in *.
  repeat rewrite <- Types.subst_preserves_unifies;
  eauto.
Qed.

Hint Resolve subst_preserves_unifies.

Definition lt c1 c2 :=
  (Id.FSet.cardinal (FV c1) <= Id.FSet.cardinal (FV c2)) /\
  (Id.FSet.cardinal (FV c2) <= Id.FSet.cardinal (FV c1) -> size c1 < size c2).

Lemma lt_subst : forall c x t t1 t2,
  ~Id.FSet.In x (Types.FV t) ->
  (t1 = t /\ t2 = Types.Var x \/ t1 = Types.Var x /\ t2 = t) ->
  lt (subst x t c) ((t1, t2) :: c).
Proof.
  intros c x t ? ? Hmem Heq.
  assert (Hcardinal : Id.FSet.cardinal (FV (subst x t c)) < Id.FSet.cardinal (FV ((t1, t2) :: c))).
  - apply Id.FSetProperties.subset_cardinal_lt with (x := x); simpl.
    + intros y HIn.
      destruct (subst_fv _ _ _ _ HIn);
      destruct Heq as [[] | []]; subst; eauto.
    + destruct Heq as [[] | []]; subst; simpl; eauto 6.
    + intros Hoccur.
      apply subst_occur in Hoccur.
      eauto.
  - split; omega.
Qed.

Lemma lt_cons : forall p c,
  lt c (p :: c).
Proof.
  intros [t] c.
  split; simpl in *.
  - apply Id.FSetProperties.subset_cardinal.
    intros ? ?.
    eauto.
  - specialize (Types.size_gt_0 t). intros. omega.
Qed.

Lemma lt_fun : forall t11 t12 t21 t22 c',
  lt ((t11, t21) :: (t12, t22) :: c')
    ((Types.Fun t11 t12, Types.Fun t21 t22) :: c').
Proof.
  intros.
  split; simpl.
  - apply Id.FSetProperties.subset_cardinal.
    intros ? H.
    apply Id.FSet.union_spec in H.
    destruct H as [ H | H ].
    + apply Id.FSet.union_spec in H.
      destruct H; eauto 7.
    + apply Id.FSet.union_spec in H.
      destruct H as [ H | H ].
      * apply Id.FSet.union_spec in H.
        destruct H; eauto 7.
      * eauto.
  - omega.
Qed.

Hint Resolve lt_subst lt_cons lt_fun.

Lemma lt_wf : well_founded lt.
Proof.
  intros c.
  remember (Id.FSet.cardinal (FV c)) as n.
  generalize dependent c.
  induction n as [n IHn] using lt_wf_ind.
  intros.
  induction c as [c IHc] using (induction_ltof1 _ (fun c => size c)).
  subst.
  constructor.
  intros c' Hlt.
  destruct Hlt as [ ? Hlt ].
  destruct (eq_nat_dec (Id.FSet.cardinal (FV c)) (Id.FSet.cardinal (FV c'))).
  - apply IHc; eauto.
    apply Hlt.
    omega.
  - eapply IHn; eauto.
    omega.
Qed.

Function unify c { wf lt c } :=
  match c with
  | nil => Some nil
  | (t1, t2) :: c' =>
      if Types.eq_dec t1 t2 then unify c'
      else
        match t1, t2 with
        | Types.Var x, _ =>
            if Id.FSet.mem x (Types.FV t2) then None
            else option_map (cons (x, t2)) (unify (subst x t2 c'))
        | _, Types.Var x =>
            if Id.FSet.mem x (Types.FV t1) then None
            else option_map (cons (x, t1)) (unify (subst x t1 c'))
        | Types.Fun t11 t12, Types.Fun t21 t22 =>
            unify ((t11, t21) :: (t12, t22) :: c')
        | _, _ => None
        end
  end.
Proof.
  - intros. apply lt_cons.
  - intros. apply lt_subst; eauto.
    intros H.
    apply Id.FSet.mem_spec in H.
    congruence.
  - intros. apply lt_fun.
  - intros. apply lt_subst; eauto.
    intros H.
    apply Id.FSet.mem_spec in H.
    congruence.
  - intros. apply lt_subst; eauto.
    intros H.
    apply Id.FSet.mem_spec in H.
    congruence.
  - apply lt_wf.
Qed.

Theorem unify_sound : forall c s,
  unify c = Some s -> unifies s c.
Proof.
  intros c.
  induction c as [[| [t1 t2]] IHc] using (well_founded_induction lt_wf);
    rewrite unify_equation;
    intros ? Hunify.
  - inversion Hunify.
    eauto.
  - destruct (Types.eq_dec t1 t2).
    + subst.
      eauto.
    + destruct t1; destruct t2;
        repeat match goal with
        | H : context [if Id.FSet.mem ?x ?s then _ else _] |- _ =>
            let b := fresh in
            remember (Id.FSet.mem x s) as b;
            destruct b;
            [| let H' := fresh in
               assert (H' : ~Id.FSet.In x s)
                 by (intros H'; apply Id.FSet.mem_spec in H'; congruence) ]
        | H : option_map (cons _) (unify ?c) = _ |- _ =>
            let o := fresh in
            let Heqo := fresh in
            remember (unify c) as o eqn:Heqo;
            symmetry in Heqo;
            destruct o
        | H : unify ?c = Some ?s |- _ =>
            assert (unifies s c) by (apply IHc; eauto); clear H
        end;
        repeat (match goal with
        | _ => rewrite Types.subst_list_Fun in *
        | _ => rewrite Types.subst_notin_fv in * by eauto
        | H : Some _ = Some _ |- _ => inversion H; clear H
        | |- context [Id.eq_dec ?x ?y] => destruct (Id.eq_dec x y)
        | H : ~Id.FSet.In ?x (Id.FSet.union ?s1 ?s2) |- _ =>
            assert (~Id.FSet.In x s1) by eauto;
            assert (~Id.FSet.In x s2) by eauto;
            clear H
        | |- Forall _ (_ :: _) => constructor
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H
        | H : Forall _ (map _ _) |- _ => apply Forall_map in H
        end; simpl in *; subst);
        solve [ eauto | congruence ].
Qed.

Notation moregen s s' :=
  (exists s0, forall e, Types.subst_list s e = Types.subst_list s0 (Types.subst_list s' e)).

Lemma moregen_extend : forall subs x t subs',
  Types.unifies subs (Types.Var x) t ->
  moregen subs subs' ->
  moregen subs ((x, t) :: subs').
Proof.
  intros ? x t ? ? Hmoregen.
  destruct Hmoregen as [ s0 Hmoregen' ].
  exists s0.
  intros ?.
  simpl.
  rewrite <- Hmoregen'.
  erewrite Types.subst_preserves_unifies; eauto.
Qed.

Theorem unify_complete : forall c s,
  unifies s c ->
  exists s', unify c = Some s' /\ moregen s s'.
Proof.
  intros c.
  induction c as [[| [t1 t2]] IHc] using (well_founded_induction lt_wf);
    rewrite unify_equation;
    intros s Hunifies.
  - exists nil.
    simpl.
    eauto.
  - destruct (Types.eq_dec t1 t2).
    + subst.
      inversion Hunifies.
      eauto.
    + inversion Hunifies. subst. clear Hunifies.
      simpl in *.
      destruct t1; destruct t2;
        repeat match goal with
        | |- context [Id.FSet.mem ?x ?s] =>
            let b := fresh in
            let Heqb := fresh in
            remember (Id.FSet.mem x s) as b eqn:Heqb;
            symmetry in Heqb;
            destruct b;
            [ apply Id.FSet.mem_spec in Heqb;
              exfalso;
              eapply Types.unifies_occur; eauto
            | let H' := fresh in
              assert (H' : ~Id.FSet.In x s)
                by (intros H'; apply Id.FSet.mem_spec in H'; congruence) ]
        | |- context [unify ?c] =>
            let H := fresh in
            assert (H : exists s', unify c = Some s' /\ moregen s s');
            [ apply IHc; eauto
            | destruct H as [? [H]];
              rewrite H ]
        end;
        repeat (simpl in *; match goal with
        | H : Types.Fun _ _ = Types.Fun _ _ |- _ => inversion H; clear H
        | _ => apply moregen_extend
        | _ => apply subst_preserves_unifies
        | _ => rewrite Types.subst_list_Bool in *
        | _ => rewrite Types.subst_list_Fun in *
        | |- exists _, Some _ = Some _ /\ _ =>
            eexists;
            split; [ reflexivity |]
        end);
        solve [ eauto | congruence ].
Qed.
