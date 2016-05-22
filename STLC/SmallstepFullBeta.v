Require Import Arith List Program.
Require Id Exp Types.

Inductive red : Exp.t -> Exp.t -> Prop :=
  | R_Abs : forall t e e',
      red e e' ->
      red (Exp.Abs t e) (Exp.Abs t e')
  | R_AppL : forall e1 e1' e2,
      red e1 e1' ->
      red (Exp.App e1 e2) (Exp.App e1' e2)
  | R_AppR : forall e1 e2 e2',
      red e2 e2' ->
      red (Exp.App e1 e2) (Exp.App e1 e2')
  | R_Red : forall t e e2,
      red (Exp.App (Exp.Abs t e) e2) (Exp.subst 0 [e2] e).
Hint Constructors red.

Lemma red_subst : forall e e',
  red e e' ->
  forall x es,
  red (Exp.subst x es e) (Exp.subst x es e').
Proof.
  intros ? ? Hred.
  induction Hred; intros ? ?; simpl; eauto.
  rewrite Exp.subst_subst_distr by omega.
  simpl.
  rewrite <- minus_n_O.
  eauto.
Qed.
Hint Resolve red_subst.
