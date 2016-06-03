Require Import Arith Div2 List Orders Sorted Permutation Program.
Require Omega.

Module MergeSort (Import X : TotalTransitiveLeBool').
  Local Coercion is_true : bool >-> Sortclass.

  Local Hint Constructors Permutation StronglySorted.

  Definition merge : forall xs, StronglySorted leb xs ->
    forall ys, StronglySorted leb ys ->
    { zs | StronglySorted leb zs /\ Permutation zs (xs ++ ys) }.
  Proof.
    refine (fix merge xs :=
      match xs as xs0 return
        StronglySorted leb xs0 ->
        forall ys, StronglySorted leb ys ->
        { zs | StronglySorted leb zs
            /\ Permutation zs (xs0 ++ ys) } with
      | [] => fun _ ys _ => exist _ ys _
      | x :: xs' => fun _ =>
          fix merge' ys :=
            match ys with
            | [] => fun _ => exist _ (x :: xs') _
            | y :: ys' => fun _ => 
                (if x <=? y as b return
                  x <=? y = b ->
                  { zs | StronglySorted leb zs
                      /\ Permutation zs (x :: xs' ++ y :: ys') }
                then fun _ =>
                  let (zs, _) := merge xs' _ (y :: ys') _ in
                  exist _ (x :: zs) _
                else fun _ =>
                  let (zs, _) := merge' ys' _ in
                  exist _ (y :: zs) _) eq_refl
            end
      end);
      simpl in *;
      try clear merge';
      repeat rewrite app_nil_r in *;
      repeat match goal with
      | H : StronglySorted _ (_ :: _) |- _ =>
          inversion H; clear H; subst
      | H : _ /\ _ |- _ => destruct H
      end;
      repeat split;
      repeat apply SSorted_cons;
      eauto;
      repeat match goal with
      | H : Forall ?P ?l |- _ =>
          assert (forall x, In x l -> P x)
            by (apply Forall_forall; eauto);
          clear H
      | |- Forall _ _ =>
          apply Forall_forall; intros
      end.
    - apply (Permutation_in _ H0) in H2.
      apply in_app_iff in H2.
      destruct H2 as [| HIn]; eauto.
      inversion HIn; subst; eauto.
      eapply leb_trans; eauto.
    - destruct (leb_total x y); [ congruence |].
      apply (Permutation_in _ H0) in H2.
      apply in_app_iff with (l := x :: xs') in H2.
      destruct H2 as [HIn |]; eauto.
      inversion HIn; subst; eauto.
      eapply leb_trans; eauto.
    - apply Permutation_cons_app with (l1 := x :: xs').
      eauto.
  Defined.

  Definition meld : forall xss,
    Forall (StronglySorted leb) xss ->
    { xss' | length xss' = div2 (S (length xss))
        /\ Forall (StronglySorted leb) xss'
        /\ Permutation (fold_right (@app _) [] xss') (fold_right (@app _) [] xss) }.
  Proof.
    refine (fix meld xss :=
      match xss with
      | [] => fun _ => exist _ [] _
      | [xs] => fun _ => exist _ [xs] _
      | xs :: xs' :: xss' => fun _ =>
          let (ys, _) := merge xs _ xs' _ in
          let (yss, _) := meld xss' _ in
          exist _ (ys :: yss) _
      end);
      simpl in *; clear meld;
      repeat rewrite app_nil_r in *;
      repeat match goal with
      | H : Forall _ (_ :: _) |- _ =>
          inversion H; clear H; subst
      | H : _ /\ _ |- _ => destruct H
      end;
      repeat split; eauto.
    rewrite app_assoc.
    apply Permutation_app; eauto.
  Defined.

  Definition merge_sort xs :
    { xs' | StronglySorted leb xs' /\ Permutation xs' xs }.
  Proof.
    refine (let (xs', _) := Fix
        (well_founded_ltof _ (@length _))
        (fun xss =>
          Forall (StronglySorted leb) xss ->
          Permutation (fold_right (@app _) [] xss) xs ->
          { xs' | StronglySorted leb xs' /\ Permutation xs' xs })
        (fun xss =>
          match xss with
          | [] => fun _ _ _ => exist _ [] _
          | [xs] => fun _ _ _ => exist _ xs _
          | xs :: ys :: xss => fun iter_meld _ _ =>
              let (xss', _) := meld (xs :: ys :: xss) _ in
              iter_meld xss' _ _ _
          end)
        (map (fun x => [x]) xs) _ _ in
      exist _ xs' _);
      simpl in *;
      repeat rewrite app_nil_r in *;
      repeat match goal with
      | H : Forall _ (_ :: _) |- _ =>
          inversion H; clear H; subst
      | H : _ /\ _ |- _ => destruct H
      end;
      repeat split;
      eauto.
    - unfold ltof.
      simpl in *.
      destruct (length xss0).
      + omega.
      + rewrite H.
        apply le_n_S.
        apply lt_div2 with (n := S (S n)).
        omega.
    - apply Forall_forall.
      intros ? HIn.
      apply in_map_iff in HIn.
      destruct HIn as [? []].
      subst.
      eauto.
    - induction xs; simpl; eauto.
  Defined.
End MergeSort.

Module Nat_as_TTLB <: TotalTransitiveLeBool.
  Let t := nat.

  Definition leb m n :=
    if le_dec m n then true
    else false.

  Definition leb_total m n :
    leb m n = true \/ leb n m = true.
  Proof.
    unfold leb.
    destruct (le_dec m n);
      destruct (le_dec n m);
        solve [ eauto | omega ].
  Qed.

  Definition leb_trans l m n :
    leb l m = true ->
    leb m n = true ->
    leb l n = true.
  Proof.
    unfold leb.
    intros.
    destruct (le_dec l m);
      destruct (le_dec m n);
        destruct (le_dec l n);
          solve [ congruence | omega ].
  Qed.
End Nat_as_TTLB.

Module NatSort := MergeSort Nat_as_TTLB.

(* FUCKIN' HEAVY COMPUTATION *)
(* Eval compute in NatSort.merge_sort [1; 1; 4; 5; 1; 4]. *)
