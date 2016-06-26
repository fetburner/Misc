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
      simplto (Exp.App (Exp.Abs t e) v2) (Exp.subst 0 [v2] e).
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

Lemma value_cannot_simpl : forall v,
  Exp.value v -> forall e, ~simplto v e.
Proof.
  intros ? Hvalue ? Hcontra.
  induction Hvalue; inversion Hcontra.
Qed.

Lemma simplto_deterministic : forall e e',
  simplto e e' ->
  forall e'',
  simplto e e'' ->
  e' = e''.
Proof.
  intros ? ? Hsimplto.
  induction Hsimplto; intros ? Hsimplto';
    inversion Hsimplto'; subst; clear Hsimplto';
    repeat match goal with
    | H : simplto ?e _ |- _ =>
        match goal with
        | _ =>
            let H' := fresh in
            assert (H' : Exp.value e) by eauto;
            destruct (value_cannot_simpl _ H' _ H)
        | IH : forall _, simplto ?e _ -> _ |- _ =>
            apply IH in H; subst
        end
    end;
    congruence.
Qed.
