Require Import Arith MSets.

Module FSet.
  Include (MSetList.Make (Nat_as_OT)).

  Definition fresh s :=
    match max_elt s with
    | None => 0
    | Some n => S n
    end.

  Lemma fresh_spec : forall s, ~ In (fresh s) s.
  Proof.
    unfold fresh.
    intros s ?.
    remember (max_elt s) as m.
    symmetry in Heqm.
    destruct m.
    - eapply max_elt_spec2; eauto.
    - apply max_elt_spec3 in Heqm.
      destruct (Heqm _ H).
  Qed.
End FSet.
Module FSetProperties := WProperties (FSet).

Definition t := FSet.E.t.
Definition eq_dec := FSet.E.eq_dec.

Hint Extern 1 (FSet.In _ (FSet.union _ _)) =>
  apply FSet.union_spec.
Hint Extern 1 (FSet.In _ (FSet.singleton _)) =>
  apply FSet.singleton_spec.
