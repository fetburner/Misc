Require Import Program.
Require Import Types Exp.

Inductive evalto : Exp.t -> Exp.t -> Prop :=
  | E_Abs : forall e t,
      evalto (Exp.Abs t e) (Exp.Abs t e)
  | E_App : forall e1 e2 e v2 v t,
      evalto e1 (Exp.Abs t e) ->
      evalto e2 v2 ->
      evalto (Exp.subst 0 [v2] e) v ->
      evalto (Exp.App e1 e2) v
  | E_Bool : forall b,
      evalto (Exp.Bool b) (Exp.Bool b)
  | E_IfTrue : forall e1 e2 e3 v2,
      evalto e1 (Exp.Bool true) ->
      evalto e2 v2 ->
      evalto (Exp.If e1 e2 e3) v2
  | E_IfFalse : forall e1 e2 e3 v3,
      evalto e1 (Exp.Bool false) ->
      evalto e3 v3 ->
      evalto (Exp.If e1 e2 e3) v3.
Hint Constructors evalto.

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
    | [ Hevalto : evalto ?t ?v, IH : forall v, evalto ?t v -> _ = v |- _ ] =>
        let H := fresh in
        generalize (IH _ Hevalto); intros H;
        inversion H;
        clear Hevalto
    end); congruence.
Qed.
