Require Import Arith Div2 Omega Recdef.

Function bsearch (p : nat -> bool) n { wf lt n } :=
  match n with
  | O => 0
  | _ =>
      let m := div2 n in
      if p m then bsearch p m
      else S m + bsearch (fun x => p (S m + x)) (n - S m)
  end.
Proof.
  + intros. apply lt_div2. omega.
  + intros. omega.
  + apply lt_wf.
Defined.

Lemma bsearch_correct : forall n p n0,
  (forall n, n0 <= n -> p n = true) ->
  (forall n, p n = true -> n0 <= n) ->
  n0 <= n ->
  bsearch p n = n0.
Proof.
  intros n.
  induction n as [[| n'] IHn] using lt_wf_ind;
    intros ? ? H H' ?;
    rewrite bsearch_equation.
  + omega.
  + remember (p (div2 (S n'))) as b.
    destruct b.
    - apply IHn; eauto.
      apply lt_div2.
      omega.
    - destruct (le_dec n0 (div2 (S n'))) as [ Hle |].
      * apply H in Hle.
        congruence.
      * { rewrite IHn with (n0 := n0 - S (div2 (S n'))); try omega.
          + intros.
            apply H.
            omega.
          + intros ? Hp.
            apply H' in Hp.
            omega.
        }
Qed.

Definition bsearch' p n :=
  bsearch (fun x => negb (p (S x))) n.

Lemma bsearch'_correct : forall n p n0,
  (forall n, n <= n0 -> p n = true) ->
  (forall n, p n = true -> n <= n0) ->
  n0 <= n ->
  bsearch' p n = n0.
Proof.
  unfold bsearch'.
  intros ? ? n0 H H' ?.
  rewrite bsearch_correct with (n0 := n0); try omega.
  + intros n1 ?.
    remember (p (S n1)) as b.
    symmetry in Heqb.
    destruct b; simpl.
    - apply H' in Heqb.
      omega.
    - reflexivity.
  + intros n1 Hp.
    destruct (le_dec (S n1) n0) as [ Hle |].
    - apply H in Hle.
      rewrite Hle in Hp.
      simpl in Hp.
      congruence.
    - omega.
Qed.

(* sqrt 4 *)
Eval compute in
  (bsearch
    (fun n =>
      if le_dec 4 (n * n) then true
      else false) 10).

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive nat => int ["0" "succ"] "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".

Extract Constant plus => "( + )".
Extract Constant minus => "( - )".
Extract Constant div2 => "(fun x -> x / 2)".
Extract Constant negb => "not".
Extraction "bsearch.ml" bsearch bsearch'.
