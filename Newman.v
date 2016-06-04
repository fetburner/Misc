Require Import Relations Program.

Definition locally_confluent A (R : relation A) := 
  forall a1 a2 a3,
  R a1 a2 ->
  R a1 a3 ->
  exists a4,
  clos_refl_trans _ R a2 a4 /\
  clos_refl_trans _ R a3 a4.

Definition confluent A (R : relation A) := 
  forall a1 a2 a3,
  clos_refl_trans _ R a1 a2 ->
  clos_refl_trans _ R a1 a3 ->
  exists a4,
  clos_refl_trans _ R a2 a4 /\
  clos_refl_trans _ R a3 a4.

Hint Constructors clos_refl_trans clos_refl_trans_1n.

Lemma Newman : forall A R,
  well_founded (flip R) ->
  locally_confluent A R ->
  confluent A R.
Proof.
  Hint Resolve clos_rt1n_rt.
  Hint Resolve clos_rt_rt1n.
  unfold flip.
  intros ? ? HSN HLC a1 a2 a3 HRs12 HRs13.
  apply clos_rt_rt1n in HRs12.
  apply clos_rt_rt1n in HRs13.
  generalize dependent a3.
  generalize dependent a2.
  induction a1 as [a1 IHa1] using (well_founded_induction HSN).
  intros ? HRs12 ? HRs13.
  inversion HRs12 as [| a1' ? HR11' HRs1'2 ];
    inversion HRs13 as [| a1'' ? HR11'' HRs1''3 ]; subst;
      eauto.
  destruct (HLC _ _ _ HR11' HR11'') as [? [HRs1'4]].
  apply clos_rt_rt1n in HRs1'4.
  destruct (IHa1 _ HR11' _ HRs1'2 _ HRs1'4) as [a5 []].
  assert (HRs1''5 : clos_refl_trans_1n _ R a1'' a5) by eauto.
  destruct (IHa1 _ HR11'' _ HRs1''3 _ HRs1''5) as [? []].
  eauto.
Qed.
