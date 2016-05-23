Require Import Arith Omega.

Theorem complete_ind : forall P, (forall n, (forall i, i < n -> P i) -> P n) -> forall n, P n.
Proof.
  intros ? IH m.
  assert (H : forall i, i <= m -> P i).
  - induction m; intros i ?.
    + apply IH.
      intros.
      omega.
    + destruct (eq_nat_dec i m);
        [| apply IH; intros ];
        apply IHm;
        omega.
  - apply H.
    omega.
Qed.
