Require Import Arith List Omega Program.
Require Id Types.

Inductive t :=
  | Var : nat -> t
  | Abs : Types.t -> t -> t
  | App : t -> t -> t
  | Bool : bool -> t.

Fixpoint FTV e :=
  match e with
  | Var _ => Id.FSet.empty
  | Abs t e => Id.FSet.union (Types.FV t) (FTV e)
  | App e1 e2 => Id.FSet.union (FTV e1) (FTV e2)
  | Bool _ => Id.FSet.empty
  end.

Fixpoint subst_type s e :=
  match e with
  | Var x => Var x
  | Abs t e => Abs (Types.subst s t) (subst_type s e)
  | App e1 e2 => App (subst_type s e1) (subst_type s e2)
  | Bool b => Bool b
  end.

Fixpoint shift c d e :=
  match e with
  | Var x => Var (if le_dec (S x) c then x else d + x)
  | Abs t e => Abs t (shift (S c) d e)
  | App e1 e2 => App (shift c d e1) (shift c d e2)
  | Bool b => Bool b
  end.

Ltac elim_shift_subst_var :=
  repeat (match goal with
  | |- context [le_dec ?x ?c] => destruct (le_dec x c)
  | H : context [le_dec ?x ?c] |- _ => destruct (le_dec x c)
  end; simpl in *).

Lemma shift_0 : forall e c,
  shift c 0 e = e.
Proof.
  intros e.
  induction e; intros ?; simpl;
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
  destruct e; simpl;
    repeat rewrite shift_meld by omega;
    eauto.
  elim_shift_subst_var; f_equal; omega.
Qed.

Lemma shift_swap : forall e c c' d d',
  c' <= c ->
  shift c' d' (shift c d e) = shift (d' + c) d (shift c' d' e).
Proof.
  fix 1.
  intros e ? ? ? ? ?.
  destruct e; simpl; f_equal;
    try rewrite shift_swap by omega;
    try solve [auto | f_equal; omega].
  elim_shift_subst_var; omega.
Qed.
Hint Rewrite shift_swap using omega.

Fixpoint subst x es e :=
  match e with
  | Var y =>
      if le_dec x y then shift 0 x (nth (y - x) es (Var (y - x - length es)))
      else Var y
  | Abs t e => Abs t (subst (S x) es e)
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Bool b => Bool b
  end.

Lemma subst_ignore : forall e c d x es,
  c <= x ->
  length es + x <= d + c ->
  subst x es (shift c d e) = shift c (d - length es) e.
Proof.
  fix 1.
  intros e ? ? ? ? ? ?.
  destruct e; simpl; f_equal;
    try apply subst_ignore;
    try omega.
  repeat ((rewrite nth_overflow by omega; simpl)
    || elim_shift_subst_var);
  f_equal; omega.
Qed.
Hint Rewrite subst_ignore using (simpl; omega).

Lemma subst_meld : forall e x x' es es',
  x' = length es + x ->
  subst x es (subst x' es' e) = subst x (es ++ es') e.
Proof.
  fix 1.
  intros e ? ? ? ? ?.
  subst.
  destruct e; simpl;
    f_equal;
    auto.
  elim_shift_subst_var; auto; try omega.
  + rewrite subst_ignore by omega.
    rewrite app_nth2 by omega.
    rewrite app_length.
    repeat (f_equal; try omega).
  + rewrite app_nth1 by omega.
    f_equal.
    apply nth_indep.
    omega.
Qed.

Lemma shift_subst_distr : forall e c d x es,
  c <= x ->
  shift c d (subst x es e) = subst (d + x) es (shift c d e).
Proof.
  fix 1.
  intros e ? ? ? ? ?.
  destruct e; simpl;
    repeat rewrite shift_subst_distr by omega;
    repeat (f_equal; try omega).
  elim_shift_subst_var;
    try rewrite shift_meld by omega;
    repeat (f_equal; try omega).
Qed.
Hint Rewrite shift_subst_distr using omega.

Lemma subst_shift_distr : forall e c d x es,
  x <= c ->
  shift c d (subst x es e) =
  subst x (map (shift (c - x) d) es) (shift (length es + c) d e).
Proof.
  fix 1.
  intros e ? ? ? ? ?.
  destruct e; simpl;
    repeat rewrite subst_shift_distr by omega;
    repeat (f_equal; try omega).
  elim_shift_subst_var; auto; try omega;
    repeat rewrite <- map_nth with (f := shift 0 x);
    rewrite <- map_nth with (f := shift c d);
    rewrite map_length.
  - replace (map (shift c d) (map (shift 0 x) es))
    with (map (shift 0 x) (map (shift (c - x) d) es)).
    + destruct (lt_dec (n - x) (length es)).
      * apply nth_indep.
        repeat rewrite map_length.
        omega.
      * simpl.
        do 2 f_equal.
        elim_shift_subst_var; omega.
    + repeat rewrite map_map.
      apply map_ext.
      intros ?.
      rewrite shift_swap by omega.
      f_equal.
      omega.
  - repeat rewrite nth_overflow by (repeat rewrite map_length; omega).
    simpl.
    f_equal.
    elim_shift_subst_var; omega.
Qed.

Lemma subst_subst_distr : forall e x x' es es',
  x' <= x ->
  subst x es (subst x' es' e)
  = subst x' (map (subst (x - x') es) es') (subst (length es' + x) es e).
Proof.
  fix 1.
  intros e ? ? ? ? ?.
  destruct e; simpl;
    try solve
      [ eauto
      | f_equal;
        rewrite subst_subst_distr by omega;
        repeat (f_equal; try omega) ].
  elim_shift_subst_var; eauto; try omega.
  - rewrite nth_overflow by (repeat rewrite map_length; omega).
    simpl.
    rewrite subst_ignore by (try rewrite map_length; omega).
    rewrite map_length.
    elim_shift_subst_var; try omega.
    clear l1.
    (* repeat (f_equal; try omega) *)
    f_equal.
    + omega.
    + f_equal.
      * omega.
      * do 2 f_equal.
        omega.
  - clear l0.
    rewrite map_length.
    repeat rewrite <- map_nth with (f := shift 0 x').
    rewrite <- map_nth with (f := subst x es).
    replace (map (subst x es) (map (shift 0 x') es'))
      with (map (shift 0 x') (map (subst (x - x') es) es'));
    repeat rewrite map_map.
    + destruct (eq_nat_dec x x').
      * subst.
        apply nth_indep.
        rewrite map_length.
        omega.
      * f_equal.
        simpl.
        elim_shift_subst_var; eauto; omega.
    + apply map_ext.
      intros ?.
      rewrite shift_subst_distr by omega.
      f_equal.
      omega.
Qed.

Lemma subst_nil : forall x e,
  subst x [] e = e.
Proof.
  fix 2.
  intros ? e.
  destruct e; simpl;
    f_equal;
    eauto.
  elim_shift_subst_var; auto.
  remember (n - x) as y.
  destruct y; simpl; elim_shift_subst_var; f_equal; omega.
Qed.

Inductive value : t -> Prop :=
  | V_Abs : forall e t, value (Abs t e)
  | V_Bool : forall b, value (Bool b).
Hint Constructors value.
