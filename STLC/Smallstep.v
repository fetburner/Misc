Require Import Relations Program.
Require Id Types Exp.

Inductive simplto : Exp.t -> Exp.t -> Prop :=
  | S_AppL : forall e1 e1' e2,
      simplto e1 e1' ->
      simplto (Exp.App e1 e2) (Exp.App e1' e2)
  | S_AppR : forall v1 e2 e2',
      Exp.value v1 ->
      simplto e2 e2' ->
      simplto (Exp.App v1 e2) (Exp.App v1 e2')
  | S_App : forall e t v2,
      Exp.value v2 ->
      simplto (Exp.App (Exp.Abs t e) v2) (Exp.subst 0 [v2] e)
  | S_If : forall e1 e1' e2 e3,
      simplto e1 e1' ->
      simplto (Exp.If e1 e2 e3) (Exp.If e1' e2 e3)
  | S_IfTrue : forall e2 e3,
      simplto (Exp.If (Exp.Bool true) e2 e3) e2
  | S_IfFalse : forall e2 e3,
      simplto (Exp.If (Exp.Bool false) e2 e3) e3.
Hint Constructors simplto.

Hint Local Constructors clos_refl_trans.

Lemma S_AppL_multi : forall e1 e1' e2,
  clos_refl_trans _ simplto e1 e1' ->
  clos_refl_trans _ simplto (Exp.App e1 e2) (Exp.App e1' e2).
Proof.
  intros ? ? ? Hclos.
  induction Hclos; eauto.
Qed.

Lemma S_AppR_multi : forall v1 e2 e2',
  Exp.value v1 ->
  clos_refl_trans _ simplto e2 e2' ->
  clos_refl_trans _ simplto (Exp.App v1 e2) (Exp.App v1 e2').
Proof.
  intros ? ? ? ? Hclos.
  induction Hclos; eauto.
Qed.

Lemma S_If_multi : forall e1 e1' e2 e3,
  clos_refl_trans _ simplto e1 e1' ->
  clos_refl_trans _ simplto (Exp.If e1 e2 e3) (Exp.If e1' e2 e3).
Proof.
  intros ? ? ? ? H.
  induction H; eauto.
Qed.
