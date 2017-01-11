Require Import Omega.

Lemma nat_eps (P : nat -> Prop) :
  (forall n, { P n } + { ~ P n }) ->
  (exists n, P n) ->
  { n | P n }.
Proof.
  intros HPdec Hex.
  refine (@Fix _
    (fun n m => S m = n /\ (forall m, m < n -> ~ P m)) _
    (fun n => (forall m, m < n -> ~ P m) -> { n | P n })
    (fun n eps HnP =>
      if HPdec n then exist _ n _
      else eps (S n) _ _) 0 _).
  - destruct Hex as [ n HP ].
    intros m.
    remember (n - m) as p.
    generalize dependent m.
    induction p as [ | p ]; intros m Heqp; constructor; intros ? [? HnP]; subst.
    + destruct (HnP n).
      * omega.
      * eauto.
    + apply IHp.
      omega.
  - assumption.
  - split.
    + reflexivity.
    + intros m ?.
      destruct (eq_nat_dec n m).
      * subst. assumption.
      * apply HnP. omega.
  - intros m ?.
    destruct (eq_nat_dec n m).
    + subst. assumption.
    + apply HnP. omega.
  - intros ? ?. omega.
Defined.

Theorem eps A (P : A -> Prop) (f : nat -> A) :
  (forall x, exists n, f n = x) ->
  (forall x, { P x } + { ~ P x }) ->
  (exists x, P x) ->
  { x | P x }.
Proof.
  intros Hsurj HPdec Hex.
  destruct (nat_eps (fun n => P (f n))).
  - intros ?.
    apply HPdec.
  - destruct Hex as [ x ].
    destruct (Hsurj x); subst.
    eauto.
  - eauto.
Defined.
