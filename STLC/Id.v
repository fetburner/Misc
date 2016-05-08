Require Import Arith MSets.

Module FSet := MSetList.Make (Nat_as_OT).
Module FSetProperties := WProperties (FSet).

Definition t := FSet.E.t.
Definition eq_dec := FSet.E.eq_dec.

Hint Extern 1 (FSet.In _ (FSet.union _ _)) =>
  apply FSet.union_spec.
Hint Extern 1 (FSet.In _ (FSet.singleton _)) =>
  apply FSet.singleton_spec.
