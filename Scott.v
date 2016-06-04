Require Import Arith List Program Omega Relations Classical.

Module Exp.
  Inductive t :=
    | Var : nat -> t
    | Abs : t -> t
    | App : t -> t -> t.

  Fixpoint shift c d e :=
    match e with
    | Var x => Var (if le_lt_dec c x then d + x else x)
    | Abs e => Abs (shift (S c) d e)
    | App e1 e2 => App (shift c d e1) (shift c d e2)
    end.

  Ltac elim_shift_subst_var :=
    repeat (match goal with
    | |- context [le_lt_dec ?x ?c] => destruct (le_lt_dec x c)
    | H : context [le_lt_dec ?x ?c] |- _ => destruct (le_lt_dec x c)
    end; simpl in *).

  Lemma shift_0 : forall e c,
    shift c 0 e = e.
  Proof.
    intros e.
    induction e; intros ?; simpl; eauto;
      f_equal;
      elim_shift_subst_var;
      eauto.
  Qed.
  Hint Rewrite shift_0.

  Lemma shift_meld : forall e c c' d d',
    c <= c' <= c + d ->
    shift c' d' (shift c d e) = shift c (d + d') e.
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    destruct e; simpl; f_equal;
      try rewrite shift_meld by omega;
      eauto.
    elim_shift_subst_var; omega.
  Qed.

  Fixpoint subst x es e :=
    match e with
    | Var y =>
        if le_lt_dec x y then shift 0 x (nth (y - x) es (Var (y - x - length es)))
        else Var y
    | Abs e => Abs (subst (S x) es e)
    | App e1 e2 => App (subst x es e1) (subst x es e2)
    end.

  Lemma subst_ignore : forall e c d x es,
    c <= x ->
    length es + x <= d + c ->
    subst x es (shift c d e) = shift c (d - length es) e.
  Proof.
    fix 1.
    intros e ? ? ? ? ? ?.
    destruct e; simpl;
      repeat rewrite subst_ignore by omega;
      eauto.
    repeat ((rewrite nth_overflow by omega; simpl) || elim_shift_subst_var);
    repeat (f_equal; try omega).
  Qed.
  Hint Rewrite subst_ignore using (simpl; omega).
End Exp.

Inductive red : Exp.t -> Exp.t -> Prop :=
  | R_Abs : forall e e',
      red e e' ->
      red (Exp.Abs e) (Exp.Abs e')
  | R_AppL : forall e1 e1' e2,
      red e1 e1' ->
      red (Exp.App e1 e2) (Exp.App e1' e2)
  | R_AppR : forall e1 e2 e2',
      red e2 e2' ->
      red (Exp.App e1 e2) (Exp.App e1 e2')
  | R_Red : forall e e2,
      red (Exp.App (Exp.Abs e) e2) (Exp.subst 0 [e2] e).
Hint Constructors red.

Notation equiv m n := (clos_refl_sym_trans _ red m n).
Hint Constructors clos_refl_sym_trans.

Lemma equiv_congr_App : forall e1 e1',
  equiv e1 e1' ->
  forall e2 e2',
  equiv e2 e2' ->
  equiv (Exp.App e1 e2) (Exp.App e1' e2').
Proof.
  intros ? ? Hequiv1.
  induction Hequiv1; intros ? ? Hequiv2; induction Hequiv2; eauto 8.
Qed.

Definition Yc :=
  let w := Exp.Abs (Exp.App (Exp.Var 1) (Exp.App (Exp.Var 0) (Exp.Var 0))) in
  Exp.Abs (Exp.App w w).

Definition fixedpoint_operator p :=
  forall f, equiv (Exp.App p f) (Exp.App f (Exp.App p f)).

Lemma Yc_fixedpoint_operator : fixedpoint_operator Yc.
Proof.
  intros ?.
  apply clos_rst1n_rst.
  eright.
  - left.
    apply R_Red.
  - eright.
    + left.
      apply R_Red.
    + eright; [| left ].
      right.
      simpl.
      rewrite Exp.subst_ignore by (simpl; omega).
      rewrite Exp.shift_meld by omega.
      simpl.
      rewrite Exp.shift_0.
      apply R_AppR.
      apply R_Red.
Qed.

Theorem fixedpoint : forall f,
  exists x, equiv x (Exp.App f x).
Proof.
  intros ?.
  eexists.
  eapply Yc_fixedpoint_operator.
Qed.

Notation CBool b :=
  (Exp.Abs (Exp.Abs (Exp.Var (if b then 1 else 0)))).

Theorem Scott : forall (P : Exp.t -> Prop) m0 m1,
  P m0 ->
  ~P m1 ->
  (forall m n, P m -> equiv m n -> P n) ->
  ~exists f, forall m,
    (P m -> equiv (Exp.App f m) (CBool true)) /\
    (~P m -> equiv (Exp.App f m) (CBool false)).
Proof.
  intros P m0 m1 ? ? ? Hdecidable.
  destruct Hdecidable as [f Hdecidable].
  (* \x. F x M1 M0 *)
  remember
    (Exp.Abs
      (Exp.App
        (Exp.App
          (Exp.App
            (Exp.shift 0 1 f)
            (Exp.Var 0))
          (Exp.shift 0 1 m1))
        (Exp.shift 0 1 m0))) as g.
  destruct (fixedpoint g) as [p Hfixedpoint]; subst.
  destruct (Hdecidable p) as [Htrue Hfalse].
  destruct (classic (P p)) as [Hp | Hp].
  - assert (equiv p m1); eauto.
    apply Htrue in Hp.
    eapply rst_trans.
    + apply Hfixedpoint.
    + eapply rst_trans.
      * apply rst_step.
        eauto.
      * { simpl.
          repeat rewrite Exp.subst_ignore by (simpl; omega).
          simpl.
          repeat rewrite Exp.shift_0.
          eapply rst_trans.
          - apply equiv_congr_App;
            [ apply equiv_congr_App |]; eauto.
          - eapply rst_trans.
            + apply rst_step.
              eauto.
            + simpl.
              eapply rst_trans.
              * apply rst_step.
                eauto.
              * rewrite Exp.subst_ignore by (simpl; omega).
                simpl.
                rewrite Exp.shift_0.
                eauto. }
  - assert (equiv p m0); eauto.
    apply Hfalse in Hp.
    eapply rst_trans.
    + apply Hfixedpoint.
    + eapply rst_trans.
      * apply rst_step.
        eauto.
      * { simpl.
          repeat rewrite Exp.subst_ignore by (simpl; omega).
          simpl.
          repeat rewrite Exp.shift_0.
          eapply rst_trans.
          - apply equiv_congr_App;
            [ apply equiv_congr_App |]; eauto.
          - eapply rst_trans.
            + apply rst_step.
              eauto.
            + simpl.
              eapply rst_trans.
              * apply rst_step.
                eauto.
              * simpl.
                rewrite Exp.shift_0.
                eauto. }
Qed.
