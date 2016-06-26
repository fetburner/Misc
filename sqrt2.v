Require Import Arith Div2 Wf_nat Omega.

Hint Constructors Even.even Even.odd.

Lemma sqrt2 : forall n p, n * n = 2 * p * p -> p = 0.
Proof.
  intros n.
  induction n as [[| n] IHn] using (well_founded_induction lt_wf);
    intros p H.
  - destruct p; simpl in *; inversion H; auto.
  - destruct (Even.even_odd_dec (S n)).
    + replace (S n) with (double (div2 (S n))) in H
        by (rewrite even_double; eauto).
      rewrite NPeano.double_twice in *.
      apply f_equal with (f := div2) in H.
      repeat rewrite <- mult_assoc in H.
      repeat rewrite div2_double in H.
      replace (div2 (S n) * (2 * div2 (S n)))
        with (2 * div2 (S n) * div2 (S n)) in H by apply mult_comm.
      destruct (Even.even_odd_dec p).
      * { replace p with (double (div2 p)) in H
            by (rewrite even_double; eauto).
          rewrite NPeano.double_twice in *.
          replace (div2 (S n) * (2 * div2 (S n)))
            with (2 * div2 (S n) * div2 (S n)) in H by apply mult_comm.
          repeat rewrite <- mult_assoc in H.
          apply f_equal with (f := div2) in H.
          repeat rewrite div2_double in H.
          replace (div2 p * (2 * div2 p))
            with (2 * div2 p * div2 p) in H by apply mult_comm.
          assert (div2 p = 0).
          - eapply IHn.
            + apply lt_div2.
              omega.
            + eauto.
          - destruct p; eauto.
            rewrite even_div2 in H0 by eauto.
            simpl in *.
            congruence. }
      * exfalso.
        assert (Even.odd (p * p)) by (apply Even.odd_mult; eauto).
        assert (Even.even (2 * div2 (S n) * div2 (S n)))
          by (rewrite <- mult_assoc; apply Even.even_mult_l; eauto).
        rewrite H in *.
        eapply Even.not_even_and_odd; eauto.
    + exfalso.
      assert (Even.odd (S n * S n)) by (apply Even.odd_mult; eauto).
      assert (Even.even (2 * p * p)) by (rewrite <- mult_assoc; apply Even.even_mult_l; eauto).
      rewrite H in *.
      eapply Even.not_even_and_odd; eauto.
Qed.



      
            
