Require Import Program.
Require Import Id Types Exp.

Inductive evalto : Exp.t -> Exp.t -> Prop :=
  | E_Abs : forall e t,
      evalto (Exp.Abs t e) (Exp.Abs t e)
  | E_App : forall e1 e2 e v2 v t,
      evalto e1 (Exp.Abs t e) ->
      evalto e2 v2 ->
      evalto (Exp.subst 0 [v2] e) v ->
      evalto (Exp.App e1 e2) v
  | E_Bool : forall b,
      evalto (Exp.Bool b) (Exp.Bool b).

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
  Exp.value v ->
  evalto v v.
Proof.
  intros ? Hv.
  inversion Hv; eauto.
Qed.
Hint Resolve evalto_ident.

Lemma evalto_value : forall e v,
  evalto e v ->
  Exp.value v.
Proof.
  intros ? ? Hevalto.
  induction Hevalto; eauto.
Qed.
Hint Resolve evalto_value.

Lemma evalto_deterministic : forall e v,
  evalto e v ->
  forall v',
  evalto e v' ->
  v = v'.
Proof.
  intros e v Hevalto.
  induction Hevalto; intros v' Hevalto'; inversion Hevalto';
  repeat (subst; match goal with
    | Hevalto : evalto ?e ?v, IH : forall v, evalto ?e v -> _ = v |- _ =>
        let H := fresh in
        generalize (IH _ Hevalto); intros H;
        inversion H;
        clear Hevalto
    end); congruence.
Qed.

Lemma evalto_diverge_disjoint : forall e v,
  evalto e v ->
  diverge v ->
  False.
Proof.
  intros ? ? Hevalto Hdiverge.
  induction Hevalto; inversion Hdiverge;
  repeat (subst; match goal with
    | H : evalto ?e _, H' : evalto ?e _ |- _ =>
        generalize (evalto_deterministic _ _ H _ H');
        intros;
        clear H
    | H : Exp.Abs _ _ = Exp.Abs _ _ |- _ => inversion H
    end); eauto.
Qed.
