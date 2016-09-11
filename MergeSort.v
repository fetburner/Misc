Require Import Arith Div2 List Orders Sorted Permutation Program.
Require Omega.

Local Hint Constructors StronglySorted.

Lemma Forall_app_iff A (P : A -> Prop) xs ys :
  Forall P (xs ++ ys) <-> (Forall P xs /\ Forall P ys).
Proof.
  split;
    [ intros; split | intros [ ? ? ] ];
    apply Forall_forall;
    intros;
    repeat match goal with
    | H : In _ (_ ++ _) |- _ => apply in_app_or in H; destruct H
    | |- In _ (_ ++ _) => apply in_or_app
    | HIn : In _ ?xs, HForall : Forall _ ?xs |- _ => eapply Forall_forall in HForall; [| clear HForall ]
    | HIn : In _ ?ys, HForall : Forall _ (_ ++ ?ys) |- _ => eapply Forall_forall in HForall; [| clear HForall ]
    | HIn : In _ ?xs, HForall : Forall _ (?xs ++ _) |- _ => eapply Forall_forall in HForall; [| clear HForall ]
    end; eauto.
Qed.

Corollary Forall_rev_iff A (P : A -> Prop) xs :
  Forall P (rev xs) <-> Forall P xs.
Proof.
  split;
    intros HForall;
    apply Forall_forall;
    intros ? HIn;
    apply in_rev in HIn;
    eapply Forall_forall in HForall;
    eauto.
Qed.

Definition Forall_rev_inv A P xs := proj1 (Forall_rev_iff A P xs).
Definition Forall_rev A P xs := proj2 (Forall_rev_iff A P xs).

Corollary Forall_map_iff A B P (f : A -> B) xs :
  Forall P (map f xs) <-> Forall (fun x => P (f x)) xs.
Proof.
  split;
    intros HForall;
    apply Forall_forall;
    intros ? HIn;
    [ eapply in_map in HIn
    | apply in_map_iff in HIn; destruct HIn as [? []]; subst ];
    eapply Forall_forall in HForall;
    eauto.
Qed.

Definition Forall_map_inv A B P f xs := proj1 (Forall_map_iff A B P f xs).
Definition Forall_map A B P f xs := proj2 (Forall_map_iff A B P f xs).

Lemma StronglySorted_app A le (xs : list A) ys :
  StronglySorted le xs ->
  StronglySorted le ys ->
  Forall (fun x => Forall (le x) ys) xs ->
  StronglySorted le (xs ++ ys).
Proof.
  induction 1; simpl; intros ? HForall.
  - eauto.
  - inversion HForall; subst.
    constructor; eauto.
    apply Forall_app_iff.
    eauto.
Qed.

Lemma StronglySorted_rev A le (xs : list A) :
  StronglySorted (fun x y => le y x) xs ->
  StronglySorted le (rev xs).
Proof.
  induction 1 as [| ? ? ? ? HForall ]; simpl.
  - constructor.
  - apply StronglySorted_app; eauto.
    apply Forall_rev_iff.
    eapply Forall_impl; [| apply HForall ].
    eauto.
Qed.

Lemma StronglySorted_rev_inv A le (xs : list A) :
  StronglySorted (fun x y => le y x) (rev xs) ->
  StronglySorted le xs.
Proof.
  intros.
  rewrite <- rev_involutive.
  apply StronglySorted_rev.
  assumption.
Qed.

Fact Permutation_fold_right A xss : forall ys ys',
  Permutation ys ys' ->
  Permutation (ys ++ fold_right (@app A) [] xss) (fold_right (@app A) ys' (rev (map (@rev A) xss))).
Proof.
  induction xss; simpl in *; intros ? ? HPermutation.
  - rewrite app_nil_r.
    eauto.
  - rewrite app_assoc.
    rewrite fold_right_app.
    simpl.
    apply IHxss.
    eapply Permutation_trans.
    + apply Permutation_app_comm.
    + apply Permutation_app; eauto.
      apply Permutation_rev.
Qed.

Module MergeSort.
  Local Coercion is_true : bool >-> Sortclass.

  Local Hint Constructors Permutation.

  Section Tools.
    Variable t : Set.
    Variable leb : t -> t -> bool.
    Hypothesis leb_total : forall x y, leb x y \/ leb y x.
    Hypothesis leb_trans : Transitive leb.
    Hint Resolve leb_trans.

    Definition merge :
      forall xs, StronglySorted leb xs ->
      forall ys, StronglySorted leb ys ->
      forall acc,
      { ws | exists zs, ws = rev zs ++ acc /\ StronglySorted leb zs /\ Permutation zs (xs ++ ys) }.
    Proof.
      refine (fix merge xs :=
        match xs as xs0 return
          StronglySorted leb xs0 ->
          forall ys, StronglySorted leb ys ->
          forall acc,
          { ws | exists zs, ws = rev zs ++ acc
              /\ StronglySorted leb zs
              /\ Permutation zs (xs0 ++ ys) } with
        | [] => fun _ ys _ acc => exist _ (rev_append ys acc) _
        | x :: xs' => fun _ =>
            fix merge' ys :=
              match ys with
              | [] => fun _ acc => exist _ (rev_append xs' (x :: acc)) _
              | y :: ys' => fun _ acc => 
                  if Sumbool.sumbool_of_bool (leb x y) then
                    let (zs, H) := merge xs' _ (y :: ys') _ (x :: acc) in
                    exist _ zs _
                  else
                    let (zs, _) := merge' ys' _ (y :: acc) in
                    exist _ zs _
              end
        end); try clear merge';
        try match goal with
        | H : exists _, _ |- _ => destruct H
        end;
        [ exists ys | exists (x :: xs') | | | exists (x :: x0) | | exists (y :: x0) ];
        repeat (simpl in *; match goal with
        | H : StronglySorted _ (_ :: _) |- _ => inversion H; clear H; subst
        | H : _ /\ _ |- _ => destruct H
        | _ => rewrite app_nil_r in *
        | _ => rewrite rev_append_rev in *
        | _ => rewrite <- app_assoc
        | _ => split
        | _ => apply SSorted_cons
        end; subst);
        eauto;
        repeat match goal with
        | H : Forall ?P ?l |- _ =>
            assert (forall x, In x l -> P x)
              by (apply Forall_forall; eauto);
            clear H
        | |- Forall _ _ =>
            apply Forall_forall; intros
        end.
      - apply (Permutation_in _ H0) in H3.
        apply in_app_iff in H3.
        destruct H3 as [| HIn]; eauto.
        inversion HIn; subst; eauto.
      - destruct (leb_total x y); [ congruence |].
        apply (Permutation_in _ H0) in H3.
        apply in_app_iff with (l := x :: xs') in H3.
        destruct H3 as [HIn |]; eauto.
        inversion HIn; subst; eauto.
      - apply Permutation_cons_app with (l1 := x :: xs').
        eauto.
    Defined.

    Definition meld : forall xss,
      Forall (StronglySorted leb) xss ->
      forall acc,
      { zss | exists xss', zss = rev (map (@rev t) xss') ++ acc /\ length xss' = div2 (S (length xss))
          /\ Forall (StronglySorted leb) xss'
          /\ Permutation (fold_right (@app _) [] xss') (fold_right (@app _) [] xss) }.
    Proof.
      refine (fix meld xss :=
        match xss with
        | [] => fun _ acc => exist _ acc _
        | [xs] => fun _ acc => exist _ (rev xs :: acc) _
        | xs :: xs' :: xss' => fun _ acc =>
            let (ys, _) := merge xs _ xs' _ [] in
            let (yss, _) := meld xss' _ (ys :: acc) in
            exist _ yss _
        end); clear meld;
        repeat match goal with
        | H : exists _, _ |- _ => destruct H
        end;
        [ exists (@nil (list t)) | exists [xs] | | | | exists (x0 :: x) ];
        repeat (simpl in *; match goal with
        | _ => rewrite app_nil_r in *
        | _ => rewrite rev_involutive in *
        | H : Forall _ (_ :: _) |- _ =>
            inversion H; clear H; subst
        | H : _ /\ _ |- _ => destruct H
        | _ => rewrite <- app_assoc
        | _ => split
        end; subst); eauto.
      rewrite app_assoc.
      apply Permutation_app; eauto.
    Defined.
  End Tools.

  Definition merge_sort (t : Set) (leb : t -> t -> bool)
    (leb_total : forall x y, leb x y \/ leb y x)
    (leb_trans : Transitive leb) xs :
    { xs' | StronglySorted leb xs' /\ Permutation xs' xs }.
  Proof.
    refine (let (xs', _) := Fix
        (well_founded_ltof _ (@length _))
        (fun xss =>
          forall is_rev : bool,
          Forall (StronglySorted (if is_rev then fun x y => leb y x else leb)) xss ->
          Permutation (fold_right (@app _) [] xss) xs ->
          { xs' | StronglySorted leb xs' /\ Permutation xs' xs })
        (fun xss =>
          match xss with
          | [] => fun _ _ _ _ => exist _ [] _
          | [xs] => fun _ is_rev _ _ =>
              if Sumbool.sumbool_of_bool is_rev then exist _ (rev xs) _
              else exist _ xs _
          | xs :: ys :: xss => fun iter_meld is_rev _ _ =>
              if Sumbool.sumbool_of_bool is_rev then
                let (xss', _) :=
                  meld _ (fun x y => leb y x) _ _ (xs :: ys :: xss) _ [] in
                  iter_meld xss' _ (negb is_rev) _ _
              else
                let (xss', _) := meld _ leb _ _ (xs :: ys :: xss) _ [] in
                iter_meld xss' _ (negb is_rev) _ _
          end)
        (map (fun x => [x]) xs) false _ _ in
      exist _ xs' _);
      repeat (simpl in *; match goal with
      | _ => rewrite app_nil_r in *
      | _ => apply StronglySorted_rev
      | _ => apply Forall_rev
      | _ => apply Forall_map
      | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
      | H : Forall _ (_ ++ _) |- _ => apply Forall_app_iff in H
      | H : _ /\ _ |- _ => destruct H
      | H : exists _, _ |- _ => destruct H
      | _ => split
      | H : context [if ?b then _ else _] |- _ => destruct b
      | H : Forall _ ?l |- Forall _ ?l => eapply Forall_impl; [| apply H ]
      end; subst);
      eauto.
    - eapply Permutation_trans.
      + apply Permutation_rev.
      + rewrite rev_involutive.
        eauto.
    - unfold ltof.
      simpl in *.
      rewrite rev_length.
      rewrite map_length.
      destruct (length xss0).
      + omega.
      + rewrite H.
        apply le_n_S.
        apply lt_div2 with (n := S (S n)).
        omega.
    - apply Permutation_sym.
      eapply Permutation_trans.
      + apply Permutation_sym.
        eauto.
      + eapply Permutation_trans.
        * apply Permutation_sym.
          eauto.
        * apply Permutation_fold_right with (A := t) (ys := []).
          eauto.
    - unfold ltof.
      simpl in *.
      rewrite rev_length.
      rewrite map_length.
      destruct (length xss0).
      + omega.
      + rewrite H.
        apply le_n_S.
        apply lt_div2 with (n := S (S n)).
        omega.
    - apply Permutation_sym.
      eapply Permutation_trans.
      + apply Permutation_sym.
        eauto.
      + eapply Permutation_trans.
        * apply Permutation_sym.
          eauto.
        * apply Permutation_fold_right with (A := t) (ys := []).
          eauto.
    - apply Forall_forall.
      eauto.
    - induction xs; simpl; eauto.
  Defined.
End MergeSort.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Constant map => "List.map".
Extract Constant app => "( @ )".
Extract Constant rev => "List.rev".
Extract Constant rev_append => "List.rev_append".
Extract Constant Sumbool.sumbool_of_bool => "(fun b => b)".
Extract Constant negb => "not".
Extraction (* "mergeSort.ml" *) MergeSort.

(* FUCKIN' HEAVY COMPUTATION *)
(* Eval compute in NatSort.merge_sort [1; 1; 4; 5; 1; 4]. *)
