Require Import Arith List Program Omega Relations.
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
Hint Constructors red clos_refl_trans.

Lemma R_Abs_multi : forall e e' t,
  clos_refl_trans _ red e e' ->
  clos_refl_trans _ red (Exp.Abs t e) (Exp.Abs t e').
Proof.
  intros ? ? ? Hmulti.
  induction Hmulti; eauto.
Qed.

Lemma R_AppL_multi : forall e1 e1' e2,
  clos_refl_trans _ red e1 e1' ->
  clos_refl_trans _ red (Exp.App e1 e2) (Exp.App e1' e2).
Proof.
  intros ? ? ? Hmulti.
  induction Hmulti; eauto.
Qed.

Lemma R_AppR_multi : forall e1 e2 e2',
  clos_refl_trans _ red e2 e2' ->
  clos_refl_trans _ red (Exp.App e1 e2) (Exp.App e1 e2').
Proof.
  intros ? ? ? Hmulti.
  induction Hmulti; eauto.
Qed.
Hint Resolve R_Abs_multi R_AppL_multi R_AppR_multi.

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

Inductive pr : Exp.t -> Exp.t -> Prop :=
  | PR_Var : forall x,
      pr (Exp.Var x) (Exp.Var x)
  | PR_Abs : forall e e' t,
      pr e e' ->
      pr (Exp.Abs t e) (Exp.Abs t e')
  | PR_App : forall e1 e1' e2 e2',
      pr e1 e1' ->
      pr e2 e2' ->
      pr (Exp.App e1 e2) (Exp.App e1' e2')
  | PR_Red : forall e1 e1' e2 e2' t,
      pr e1 e1' ->
      pr e2 e2' ->
      pr (Exp.App (Exp.Abs t e1) e2) (Exp.subst 0 [e2'] e1')
  | PR_Bool : forall b,
      pr (Exp.Bool b) (Exp.Bool b).
Hint Constructors pr.

Lemma pr_refl : forall e, pr e e.
Proof.
  intros e.
  induction e; eauto.
Qed.
Hint Resolve pr_refl.

Lemma red_impl_pr : forall e e',
  red e e' -> pr e e'.
Proof.
  intros ? ? Hred.
  induction Hred; eauto.
Qed.
Hint Resolve red_impl_pr.

Lemma pr_impl_redmulti : forall e e',
  pr e e' -> clos_refl_trans _ red e e'.
Proof.
  intros ? ? Hpr.
  induction Hpr; eauto 7.
Qed.
Hint Resolve pr_impl_redmulti.

Lemma prmulti_iff_redmulti : forall e e',
  clos_refl_trans _ pr e e' <->
  clos_refl_trans _ red e e'.
Proof.
  intros ? ?.
  split; intros Hmulti; induction Hmulti; eauto.
Qed.

Fixpoint reduce_all_redex m :=
  match m with
  | Exp.Var x => Exp.Var x
  | Exp.Abs t m =>
      Exp.Abs t (reduce_all_redex m)
  | Exp.App (Exp.Abs t m) n =>
      Exp.subst 0 [reduce_all_redex n] (reduce_all_redex m)
  | Exp.App m n =>
      Exp.App (reduce_all_redex m) (reduce_all_redex n)
  | Exp.Bool b => Exp.Bool b
  end.

Lemma shift_preserves_pr : forall e e',
  pr e e' ->
  forall c d, pr (Exp.shift c d e) (Exp.shift c d e').
Proof.
  intros ? ? Hpr.
  induction Hpr; intros ? ?; simpl; eauto.
  rewrite Exp.subst_shift_distr by omega.
  simpl.
  rewrite <- minus_n_O.
  eauto.
Qed.

Lemma pr_subst : forall n n',
  pr n n' ->
  forall x m m',
  pr m m' ->
  pr (Exp.subst x [m] n) (Exp.subst x [m'] n').
Proof.
  intros ? ? Hpr1.
  induction Hpr1; intros ? ? ? Hpr2; simpl; eauto.
  - Exp.elim_shift_subst_var; eauto.
    destruct (x - x0) as [| []]; simpl; eauto.
    apply shift_preserves_pr.
    eauto.
  - rewrite Exp.subst_subst_distr by omega.
    simpl.
    rewrite <- minus_n_O.
    eauto.
Qed.

Lemma finite_development : forall m n,
  pr m n ->
  pr n (reduce_all_redex m).
Proof.
  intros ? ? Hpr.
  induction Hpr; simpl; eauto.
  - destruct e1; simpl in *; eauto.
    inversion Hpr1; subst.
    inversion IHHpr1; subst.
    eauto.
  - apply pr_subst; eauto.
Qed.

Lemma pr_church_rosser' : forall m m',
  clos_refl_trans _ pr m m' ->
  forall m'',
  pr m m'' ->
  exists m''',
  pr m' m''' /\
  clos_refl_trans _ pr m'' m'''.
Proof.
  intros ? ? Hmulti.
  apply clos_rt_rt1n in Hmulti.
  induction Hmulti; intros ? ?.
  - eauto.
  - apply finite_development in H.
    apply finite_development in H0.
    destruct (IHHmulti _ H) as [? []].
    eauto.
Qed.

Lemma pr_church_rosser : forall m m',
  clos_refl_trans _ pr m m' ->
  forall m'',
  clos_refl_trans _ pr m m'' ->
  exists m''',
  clos_refl_trans _ pr m' m''' /\
  clos_refl_trans _ pr m'' m'''.
Proof.
  intros ? ? Hmulti.
  apply clos_rt_rt1n in Hmulti.
  induction Hmulti; intros ? Hmulti'.
  - eauto.
  - apply clos_rt1n_rt in Hmulti.
    apply (pr_church_rosser' _ _ Hmulti') in H.
    destruct H as [? [? H]].
    apply IHHmulti in H.
    destruct H as [? []].
    eauto.
Qed.

Lemma red_church_rosser : forall m m' m'',
  clos_refl_trans _ red m m' ->
  clos_refl_trans _ red m m'' ->
  exists m''',
  clos_refl_trans _ red m' m''' /\
  clos_refl_trans _ red m'' m'''.
Proof.
  intros ? ? ? H H'.
  apply prmulti_iff_redmulti in H.
  apply prmulti_iff_redmulti in H'.
  destruct (pr_church_rosser _ _ H _ H') as [? [H'' H''']].
  apply prmulti_iff_redmulti in H''.
  apply prmulti_iff_redmulti in H'''.
  eauto.
Qed.
