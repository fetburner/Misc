Require Import Arith List Omega Program.
Require Types.

Inductive t :=
  | Var : nat -> t
  | Abs : Types.t -> t -> t
  | App : t -> t -> t
  | Bool : bool -> t
  | If : t -> t -> t -> t.

Fixpoint shift c d e :=
  match e with
  | Var x => Var (if le_dec (S x) c then x else d + x)
  | Abs t e => Abs t (shift (S c) d e)
  | App e1 e2 => App (shift c d e1) (shift c d e2)
  | Bool b => Bool b
  | If e1 e2 e3 => If (shift c d e1) (shift c d e2) (shift c d e3)
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

Fixpoint subst x es e :=
  match e with
  | Var y =>
      if le_dec x y then shift 0 x (nth (y - x) es (Var (y - x - length es)))
      else Var y
  | Abs t e => Abs t (subst (S x) es e)
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Bool b => Bool b
  | If e1 e2 e3 => If (subst x es e1) (subst x es e2) (subst x es e3)
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
