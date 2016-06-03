Require Import Arith Div2 List Orders Sorted Permutation Program.

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
        { zs | StronglySorted leb zs /\ Permutation zs (xs0 ++ ys) } with
      | [] => fun _ ys _ => exist _ ys _
      | x :: xs' => fun _ =>
          fix merge' ys :=
            match ys with
            | [] => fun _ => exist _ (x :: xs') _
            | y :: ys' => fun _ => 
                match (x <=? y) as b return
                  x <=? y = b ->
                  { zs | StronglySorted leb zs /\ Permutation zs (x :: xs' ++ y :: ys') }
                with
                | true => fun _ =>
                    let (zs, _) := merge xs' _ (y :: ys') _ in
                    exist _ (x :: zs) _
                | false => fun _ =>
                    let (zs, _) := merge' ys' _ in
                    exist _ (y :: zs) _
                end eq_refl
            end
      end);
      simpl in *;
      try clear merge';
      repeat rewrite app_nil_r in *;
      repeat split;
      repeat apply SSorted_cons;
      repeat match goal with
      | H : StronglySorted _ (_ :: _) |- _ =>
          inversion H; clear H; subst
      | H : _ /\ _ |- _ => destruct H
      end; eauto;
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
      repeat split; eauto;
      repeat match goal with
      | H : Forall _ (_ :: _) |- _ =>
          inversion H; clear H; subst
      | H : _ /\ _ |- _ => destruct H
      end; eauto.
    rewrite app_assoc.
    apply Permutation_app; eauto.
  Defined.
End MergeSort.
