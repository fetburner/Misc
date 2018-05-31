Require Import List Orders Sorted Permutation Program.
Require Omega.

Definition Forall_forall' A P xs := proj1 (@Forall_forall A P xs).
Definition Forall_forall_inv A P xs := proj2 (@Forall_forall A P xs).
Hint Resolve Forall_forall_inv.

Lemma Forall_app A P xs ys : @Forall A P xs -> Forall P ys -> Forall P (xs ++ ys).
Proof.
  intros Hxs Hys. apply Forall_forall. intros ? HIn.
  destruct (in_app_or _ _ _ HIn); [ clear Hys | clear Hxs ]; eapply Forall_forall; eauto.
Qed.

Lemma Forall_rev A P xs : @Forall A P xs -> Forall P (rev xs).
Proof.
  intros. apply Forall_forall. intros. eapply Forall_forall; eauto. apply in_rev. eauto.
Qed.

Hint Resolve Forall_app Forall_rev.

Hint Constructors StronglySorted.

Section StronglySorted.
  Lemma StronglySorted_app A le xs ys :
    StronglySorted le ys ->
    StronglySorted le xs ->
    @Forall A (fun x => Forall (le x) ys) xs ->
    StronglySorted le (xs ++ ys).
  Proof.
    induction 2; inversion 1; subst; simpl; eauto.
  Qed.

  Lemma StronglySorted_rev A le (xs : list A) :
    StronglySorted le xs ->
    StronglySorted (fun x y => le y x) (rev xs).
  Proof.
    induction 1; simpl; eauto.
    apply StronglySorted_app; eauto.
    eapply Forall_rev, Forall_impl; [ | eassumption ]. eauto.
  Qed.
End StronglySorted.

Hint Resolve StronglySorted_rev.

Section RevMerge.
  Variable t : Set.
  Variable le1 : t -> t -> Prop.
  Hypotheses le1_total : forall x y, { le1 x y } + { ~ le1 x y /\ le1 y x }.

  Fixpoint rev_merge' xs :=
    match xs with
    | [] => @rev_append _
    | x :: xs => fix rev_merge'_inner ys :=
        match ys with
        | [] => rev_append (x :: xs)
        | y :: ys => fun acc =>
            if le1_total x y
            then rev_merge' xs (y :: ys) (x :: acc)
            else rev_merge'_inner ys (y :: acc)
        end
    end.

  Definition rev_merge xs ys := rev_merge' xs ys [].

  Variable le2 : t -> t -> Prop.
  Hypotheses le1_trans : forall x y z, le1 x y -> le1 y z -> le1 x z.
  Hypotheses le2_trans : forall x y z, le2 x y -> le2 y z -> le2 x z.

  Definition lexord x y := le1 x y /\ (le1 y x -> le2 x y).

  Lemma lexord_trans x y z : lexord x y -> lexord y z -> lexord x z.
  Proof. intros [ ] [ ]. split; eauto 6. Qed.

  Local Hint Constructors Forall Permutation.

  Lemma rev_merge'_perm xs : forall ys acc, Permutation (rev_merge' xs ys acc) (xs ++ ys ++ acc).
  Proof.
    induction xs as [ | x xs IHxs ]; simpl.
    - intros. rewrite rev_append_rev, <- Permutation_rev. reflexivity.
    - intros ys. induction ys as [ | y ys IHys ]; simpl; intros acc.
      + replace (rev_append xs (x :: acc)) with (rev (x :: xs) ++ acc)
        by (symmetry; apply rev_append_rev with (l := x :: xs)).
        rewrite <- Permutation_rev. reflexivity.
      + destruct (le1_total x y); [ rewrite IHxs | rewrite IHys ]; simpl; repeat rewrite <- Permutation_middle; eauto.
  Qed.

  Lemma rev_merge'_sorted :
    forall xs, StronglySorted lexord xs ->
    forall ys, StronglySorted lexord ys ->
    forall acc, StronglySorted (fun x y => lexord y x) acc ->
    (forall x y, List.In x xs -> List.In y ys -> le2 x y) ->
    (forall x a, List.In x xs -> List.In a acc -> lexord a x) ->
    (forall y a, List.In y ys -> List.In a acc -> lexord a y) ->
    StronglySorted (fun x y => lexord y x) (rev_merge' xs ys acc).
  Proof.
    unfold lexord.
    induction 1 as [ | x xs ? IHxs Hxs ]; simpl.
    - intros ys ? ? ? ? ? ?. rewrite rev_append_rev.
      apply StronglySorted_app; eauto.
    - generalize (Forall_forall' _ _ _ Hxs).
      induction 2 as [ | y ys ? IHys Hys ]; simpl in *; intros acc ? ? ? ?.
      + replace (rev_append xs (x :: acc)) with (rev (x :: xs) ++ acc)
        by (symmetry; apply rev_append_rev with (l := x :: xs)).
        apply StronglySorted_app; eauto.
      + generalize (Forall_forall' _ _ _ Hys). intros.
        destruct (le1_total x y) as [ | [ ] ]; [ apply IHxs | apply IHys ]; simpl in *; eauto.
        * intros ? ? ? [ ? | ? ]; subst; eauto.
        * intros ? ? [ ? | ? ] [ ? | ? ]; subst; eauto.
          apply lexord_trans with (y := y); unfold lexord; eauto.
        * { intros ? ? [ ? | ? ] [ ? | ? ]; subst; eauto.
            - split; eauto. intros. exfalso. eauto.
            - apply lexord_trans with (y := x); unfold lexord; eauto.
              split; eauto. intros. exfalso. eauto. }
      + intros ? ? ? [ ? | ? ]; subst; eauto.
  Qed.

  Corollary rev_merge_perm xs ys : Permutation (rev_merge xs ys) (xs ++ ys).
  Proof. unfold rev_merge. rewrite rev_merge'_perm, app_nil_r. reflexivity. Qed.

  Corollary rev_merge_sorted xs ys :
    StronglySorted lexord xs ->
    StronglySorted lexord ys ->
    (forall x y, List.In x xs -> List.In y ys -> le2 x y) ->
    StronglySorted (fun x y => lexord y x) (rev_merge xs ys).
  Proof.
    intros. apply rev_merge'_sorted; simpl; eauto; intros ? ? ? [].
  Qed.
End RevMerge.

Section MergeSort.
  Variable t : Set.
  Variable le1 : t -> t -> Prop.
  Hypotheses le1_total : forall x y, { le1 x y } + { ~ le1 x y /\ le1 y x }.

  Fixpoint add (b : bool) xs xss :=
    match xss with
    | [] => [Some xs]
    | None :: xss => Some xs :: xss
    | Some ys :: xss =>
        None ::
          if b then
            add false (rev_merge _ _ le1_total ys xs) xss
          else
            add true (rev_merge _ _ (fun x y => le1_total y x) xs ys) xss
    end.

  Fixpoint sort (b : bool) xs xss :=
    match xss with
    | [] => if b then xs else rev xs
    | [None] => if b then xs else rev xs
    | Some ys :: xss =>
        if b then
          sort false (rev_merge _ _ le1_total ys xs) xss
        else
          sort true (rev_merge _ _ (fun x y => le1_total y x) xs ys) xss
    | None :: None :: xss => sort b xs xss
    | None :: Some ys :: xss =>
        if b then
          sort true (rev_merge _ _ (fun x y => le1_total y x) (rev xs) ys) xss
        else
          sort false (rev_merge _ _ le1_total ys (rev xs)) xss
    end.

  Fixpoint flatten (xss : list (option (list t))) :=
    match xss with
    | [] => []
    | None :: xss => flatten xss
    | Some xs :: xss => flatten xss ++ xs
    end.

  Hint Resolve Permutation_app_head Permutation_app_comm Permutation_rev in_or_app.

  Lemma add_perm xss : forall b xs, Permutation (flatten xss ++ xs) (flatten (add b xs xss)).
  Proof.
    induction xss as [ | [ ? | ] ? ]; simpl; eauto.
    intros [] ?; rewrite <- IHxss, <- app_assoc, rev_merge_perm; eauto.
  Qed.

  Lemma sort_perm : forall xss b xs, Permutation (flatten xss ++ xs) (sort b xs xss).
  Proof.
    Local Hint Resolve Permutation_rev.
    fix 1. intros [].
    - intros []; simpl; eauto.
    - intros [ ? | ]; [ intros ? [] ? | intros [ | [ ? | ] ? ] [] ? ]; simpl; eauto;
        rewrite <- sort_perm, <- app_assoc, rev_merge_perm;
        repeat rewrite <- Permutation_rev; eauto.
  Qed.

  Variable le2 : t -> t -> Prop.
  Hypotheses le1_trans : forall x y z, le1 x y -> le1 y z -> le1 x z.
  Hypotheses le2_trans : forall x y z, le2 x y -> le2 y z -> le2 x z.

  Fixpoint Sortable b xss :=
    match xss with
    | [] => True
    | None :: xss => Sortable (negb b) xss
    | Some xs :: xss =>
        Sortable (negb b) xss /\
        StronglySorted (if b then lexord _ le1 le2 else fun x y => lexord _ le1 le2 y x) xs /\
        forall x y, List.In x xs -> List.In y (flatten xss) -> le2 y x
  end.

  Lemma add_Sortable xss : forall b xs,
    Sortable b xss ->
    (forall x y, List.In x xs -> List.In y (flatten xss) -> le2 y x) ->
    StronglySorted (if b then lexord _ le1 le2 else fun x y => lexord _ le1 le2 y x) xs ->
    Sortable b (add b xs xss).
  Proof.
    induction xss as [ | [ | ] ]; simpl; eauto.
    intros [] ? [ ? [ ? ? ] ] ? ?; apply IHxss; simpl in *; eauto;
      try apply rev_merge_sorted;
      try (intros ? ? HIn ?; eapply Permutation_in in HIn; [ | eapply rev_merge_perm ];
        destruct (in_app_or _ _ _ HIn)); eauto.
  Qed.

  Lemma sort_sorted : forall xss (b : bool) xs,
    (forall x y, List.In x xs -> List.In y (flatten xss) -> le2 y x) ->
    StronglySorted (if b then lexord _ le1 le2 else fun x y => lexord _ le1 le2 y x) xs ->
    Sortable b xss ->
    StronglySorted (lexord _ le1 le2) (sort b xs xss).
  Proof.
    fix 1. intros [ ].
    - intros []; simpl; eauto.
    - intros [ ? | ]; [ intros ? [] ? ? ? ? | intros [ | [ ? | ] ? ] [] ? ? ? ? ]; simpl in *; eauto; apply sort_sorted;
        try apply rev_merge_sorted;
        try (intros ? ? HIn ?; eapply Permutation_in in HIn; [ | apply rev_merge_perm ];
            destruct (in_app_or _ _ _ HIn)); intros;
            repeat match goal with
            | H : _ /\ _ |- _ => destruct H
            | H : List.In _ (rev _) |- _ => apply in_rev in H
            end; eauto.
  Qed.

  Fixpoint merge_sort' xss xs :=
    match xs with
    | [] => sort true [] xss
    | [x] => sort true [x] xss
    | x :: y :: xs =>
        if le1_total x y then
          (fix cut_non_decreasing ys y xs :=
            match xs with
            | [] => sort true (rev (y :: ys)) xss
            | (x :: xs) as l =>
                if le1_total y x then
                  cut_non_decreasing (y :: ys) x xs
                else
                  merge_sort' (add true (rev (y :: ys)) xss) l
            end) [x] y xs
        else
          (fix cut_decreasing ys y xs :=
            match xs with
            | [] => sort true (y :: ys) xss
            | (x :: xs) as l =>
                if le1_total y x then
                  merge_sort' (add true (y :: ys) xss) l
                else
                  cut_decreasing (y :: ys) x xs
            end) [x] y xs
    end.

  Definition merge_sort := merge_sort' [].

  Lemma merge_sort'_perm : forall xs xss, Permutation (flatten xss ++ xs) (merge_sort' xss xs).
  Proof.
    fix 1. intros [ | x [ | y xs ] ] ?; simpl.
    - rewrite <- sort_perm. reflexivity.
    - rewrite <- sort_perm. reflexivity.
    - destruct (le1_total x y) as [ | [ ] ].
      + assert (Hnd : forall xs y ys xss, Permutation (flatten xss ++ rev ys ++ y :: xs)
          ((fix cut_non_decreasing ys y xs :=
            match xs with
            | [] => sort true (rev (y :: ys)) xss
            | (x :: xs) as l =>
                if le1_total y x then
                  cut_non_decreasing (y :: ys) x xs
                else
                  merge_sort' (add true (rev (y :: ys)) xss) l
            end) ys y xs)).
        { fix 1. intros xs_ y_ ? xss_. specialize (merge_sort'_perm xs_). destruct xs_ as [ | x_ xs_ ].
          - apply sort_perm.
          - destruct (le1_total y_ x_) as [ | [ ] ].
            + rewrite <- merge_sort'_perm0 with (xss := xss_). simpl. rewrite <- app_assoc. reflexivity.
            + rewrite <- merge_sort'_perm, <- add_perm. simpl. repeat rewrite <- app_assoc. reflexivity. }
        rewrite <- Hnd with (xss := xss), <- Permutation_rev. reflexivity.
      + assert (Hd : forall xs y ys xss, Permutation (flatten xss ++ rev ys ++ y :: xs)
          ((fix cut_decreasing ys y xs :=
            match xs with
            | [] => sort true (y :: ys) xss
            | (x :: xs) as l =>
                if le1_total y x then
                  merge_sort' (add true (y :: ys) xss) l
                else
                  cut_decreasing (y :: ys) x xs
            end) ys y xs)).
        { fix 1. intros xs_ y_ ? xss_. specialize (merge_sort'_perm xs_). destruct xs_ as [ | x_ xs_ ].
          - rewrite <- sort_perm, <- Permutation_rev with (l := y_ :: ys). reflexivity.
          - destruct (le1_total y_ x_) as [ | [ ] ].
            + rewrite <- merge_sort'_perm, <- add_perm, Permutation_rev with (l := y_ :: ys). simpl.
              repeat rewrite <- app_assoc. reflexivity.
            + rewrite <- merge_sort'_perm0 with (xss := xss_). simpl.
              rewrite <- app_assoc. reflexivity. }
        rewrite <- Hd with (xss := xss). reflexivity.
  Qed.

  Lemma merge_sort'_sorted : forall xs xss,
    StronglySorted le2 xs ->
    (forall x y, List.In x xs -> List.In y (flatten xss) -> le2 y x) ->
    Sortable true xss ->
    StronglySorted (lexord _ le1 le2) (merge_sort' xss xs).
  Proof.
    fix 1. intros [ | x [ | y xs ] ] ? ? ? ?; simpl.
    - apply sort_sorted; eauto.
    - apply sort_sorted; eauto.
    - repeat match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
      | H : StronglySorted _ (_ :: _) |- _ => inversion H; clear H; subst
      end.
      repeat match goal with
      | H : Forall _ _ |- _ => generalize (Forall_forall' _ _ _ H); intros ?; clear H
      end.
      destruct (le1_total x y) as [ | [ ] ].
      + assert (Hnd : forall xs y ys xss,
          Sortable true xss ->
          (forall x y', List.In x xs -> List.In y' (y :: ys) -> le2 y' x) ->
          (forall y', List.In y' ys -> lexord _ le1 le2 y' y) ->
          StronglySorted (fun x y => lexord _ le1 le2 y x) ys ->
          (forall x y', List.In x (flatten xss) -> List.In y' (y :: ys) -> le2 x y') ->
          StronglySorted le2 xs ->
          StronglySorted (lexord _ le1 le2)
            ((fix cut_non_decreasing ys y xs :=
              match xs with
              | [] => sort true (rev (y :: ys)) xss
              | (x :: xs) as l =>
                  if le1_total y x then
                    cut_non_decreasing (y :: ys) x xs
                  else
                    merge_sort' (add true (rev (y :: ys)) xss) l
              end) ys y xs)).
        { unfold lexord. fix 1. intros xs_ y_ ys xss_ ? ? ? ? ?. specialize (merge_sort'_sorted xs_).
          destruct xs_ as [ | x_ xs_ ]; inversion 1; subst.
          - apply sort_sorted; unfold lexord; eauto.
            intros ? ? HIn. apply in_rev in HIn. eauto.
          - generalize (Forall_forall' _ _ _ H14). intros. simpl in *.
            destruct (le1_total y_ x_) as [ | [ ] ].
            + apply merge_sort'_sorted0 with (xss := xss_); eauto.
              * intros ? ? ? [ ? | [ ? | ? ] ]; subst; eauto.
              * intros ? [ ? | ? ]; subst; eauto.
                apply lexord_trans with (y := y_); unfold lexord; eauto.
              * intros ? ? ? [ ? | [ ? | ? ] ]; subst; eauto.
                apply le2_trans with (y := y_); eauto.
            + apply merge_sort'_sorted; eauto.
              * intros ? ? ? HIn.
                apply Permutation_in with (l' := flatten xss_ ++ y_ :: ys) in HIn;
                [ | rewrite <- add_perm, <- Permutation_rev with (l := y_ :: ys); reflexivity ].
                apply in_app_or in HIn. destruct HIn; eauto.
                apply le2_trans with (y := y_); eauto.
              * { apply add_Sortable; eauto.
          - intros ? ? HIn. apply in_rev with (l := y_ :: ys) in HIn. eauto.
          - apply StronglySorted_rev with (xs := y_ :: ys). eauto. } }
        apply Hnd with (xss := xss); eauto.
        * intros ? ? ? [ ? | [ ? | [] ] ]; subst; eauto.
        * unfold lexord. intros ? [ ? | [ ] ]; subst; eauto.
        * simpl in *. intros ? ? ? [ ? | [ ? | [] ] ]; subst; eauto.
      + assert (Hd : forall xs y ys xss,
          Sortable true xss ->
          (forall x y', List.In x xs -> List.In y' (y :: ys) -> le2 y' x) ->
          (forall y', List.In y' ys -> lexord _ le1 le2 y y') ->
          StronglySorted (lexord _ le1 le2) ys ->
          (forall x y', List.In x (flatten xss) -> List.In y' (y :: ys) -> le2 x y') ->
          StronglySorted le2 xs ->
          StronglySorted (lexord _ le1 le2)
          ((fix cut_decreasing ys y xs :=
            match xs with
            | [] => sort true (y :: ys) xss
            | (x :: xs) as l =>
                if le1_total y x then
                  merge_sort' (add true (y :: ys) xss) l
                else
                  cut_decreasing (y :: ys) x xs
            end) ys y xs)).
        { unfold lexord. fix 1. intros xs_ y_ ys xss_ ? ? ? ? ?. specialize (merge_sort'_sorted xs_).
          destruct xs_ as [ | x_ xs_ ]; inversion 1; subst.
          - apply sort_sorted; unfold lexord; eauto.
          - generalize (Forall_forall' _ _ _ H16). intros. simpl in *.
            destruct (le1_total y_ x_) as [ | [ ] ].
            + apply merge_sort'_sorted; eauto.
              * intros ? ? ? HIn.
                eapply Permutation_in in HIn; [ | symmetry; apply add_perm ].
                apply in_app_or in HIn. destruct HIn; eauto.
                apply le2_trans with (y := y_); eauto.
              * apply add_Sortable; eauto.
            + apply merge_sort'_sorted0 with (xss := xss_); eauto.
              * intros ? ? ? [ ? | [ ? | ? ] ]; subst; eauto.
              * { intros ? [ ? | ? ]; subst; eauto.
                  - split; eauto. intros. exfalso. eauto.
                  - apply lexord_trans with (y := y_); unfold lexord; eauto.
                    split; eauto. intros. exfalso. eauto. }
              * intros ? ? ? [ ? | [ ? | ? ] ]; subst; eauto.
                apply le2_trans with (y := y_); eauto. }
        apply Hd with (xss := xss); eauto.
        * intros ? ? ? [ ? | [ ? | [] ] ]; subst; eauto.
        * unfold lexord. intros ? [ ? | [ ] ]; subst; eauto.
          split; eauto. intros. exfalso. eauto.
        * simpl in *. intros ? ? ? [ ? | [ ? | [] ] ]; subst; eauto.
  Qed.

  Corollary merge_sort_perm xs : Permutation xs (merge_sort xs).
  Proof. apply merge_sort'_perm with (xss := []). Qed.

  Corollary merge_sort_sorted xs :
    StronglySorted le2 xs ->
    StronglySorted (lexord _ le1 le2) (merge_sort xs).
  Proof.
    intros ?. apply merge_sort'_sorted; simpl; eauto.
    intros ? ? ? [].
  Qed.
End MergeSort.

Require Import ExtrOcamlBasic ExtrOcamlNatInt Mergesort.
Extract Constant map => "List.map".
Extract Constant app => "( @ )".
Extract Constant rev => "List.rev".
Extract Constant rev_append => "List.rev_append".
Extract Constant negb => "not".
Extract Constant NatOrder.leb => "( <= )".
Extraction "merge_sort.ml" NatSort merge_sort.
