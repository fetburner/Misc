Require Import Program.
Require Import Syntax.

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
Hint Constructors evalto.

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
