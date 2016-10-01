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

Definition concat A := fold_right (@app A) [].

Lemma concat_app A xs ys :
  concat A (xs ++ ys) = concat _ xs ++ concat A ys.
Proof.
  induction xs; simpl in *;
    repeat rewrite <- app_assoc;
    congruence.
Qed.

Lemma concat_rev A xs :
  concat A (rev (map (@rev _) xs)) = rev (concat _ xs).
Proof.
  induction xs; simpl in *;
    repeat ((rewrite concat_app || rewrite app_nil_r || rewrite rev_app_distr); simpl in *);
    congruence.
Qed.

Section MergeSort.
  Local Coercion is_true : bool >-> Sortclass.

  Local Hint Constructors Permutation.

  Section Tools.
    Variable t : Set.
    Variable leb : t -> t -> bool.
    Hypothesis leb_total : forall x y, leb x y \/ leb y x.
    Hypothesis leb_trans : Transitive leb.
    Hint Resolve leb_trans.

    Definition rev_merge :
      forall xs, StronglySorted leb xs ->
      forall ys, StronglySorted leb ys ->
      forall acc,
      { ws | exists zs, ws = rev zs ++ acc /\ StronglySorted leb zs /\ Permutation zs (xs ++ ys) }.
    Proof.
      refine (fix rev_merge xs :=
        match xs as xs0 return StronglySorted leb xs0 ->
          forall ys, StronglySorted leb ys ->
          forall acc,
          { ws | exists zs, ws = rev zs ++ acc
              /\ StronglySorted leb zs
              /\ Permutation zs (xs0 ++ ys) } with
        | [] => fun _ ys _ acc => exist _ (rev_append ys acc) (ex_intro _ ys _)
        | x :: xs' => fun _ =>
            fix rev_merge' ys :=
              match ys as ys0 return StronglySorted leb ys0 ->
                forall acc,
                { ws | exists zs, ws = rev zs ++ acc
                    /\ StronglySorted leb zs
                    /\ Permutation zs (x :: xs' ++ ys0) }
              with
              | [] => fun _ acc => exist _ (rev_append xs' (x :: acc)) (ex_intro _ (x :: xs') _)
              | y :: ys' => fun _ acc => 
                  if Sumbool.sumbool_of_bool (leb x y) then
                    let (zs, H) := rev_merge xs' _ (y :: ys') _ (x :: acc) in
                    exist _ zs (let (x0, _) := H in ex_intro _ (x :: x0) _)
                  else
                    let (zs, H) := rev_merge' ys' _ (y :: acc) in
                    exist _ zs (let (x0, _) := H in ex_intro _ (y :: x0) _)
              end
        end); try clear rev_merge';
        repeat (simpl in *;
            ( rewrite app_nil_r in *
           || rewrite rev_append_rev in *
           || rewrite <- app_assoc
           || match goal with
              | H : StronglySorted _ (_ :: _) |- _ => inversion H; clear H; subst
              | H : _ /\ _ |- _ => destruct H
              | H : leb ?x ?y = false |- _ => destruct (leb_total x y); [ congruence | clear H ]
              end
           || split
           || apply SSorted_cons); subst);
        eauto;
        repeat match goal with
        | H : Forall ?P ?l |- _ =>
            assert (forall x, In x l -> P x)
              by (apply Forall_forall; eauto);
            clear H
        | |- Forall _ _ =>
            apply Forall_forall; intros
        end.
      - apply (Permutation_in _ H1) in H3.
        apply in_app_iff in H3.
        destruct H3 as [ | [ ] ]; subst; eauto.
      - apply (Permutation_in _ H1) in H3.
        apply in_app_iff with (l := x :: xs') in H3.
        destruct H3 as [ [ ] | ]; subst; eauto.
      - apply Permutation_cons_app with (l1 := x :: xs').
        eauto.
    Defined.

    Definition meld : forall xss,
      Forall (StronglySorted leb) xss ->
      forall acc,
      { zss | exists xss', zss = rev (map (@rev t) xss') ++ acc /\ length xss' = div2 (S (length xss))
          /\ Forall (StronglySorted leb) xss'
          /\ Permutation (concat _ xss') (concat _ xss) }.
    Proof.
      refine (fix meld xss :=
        match xss as xss0 return
          Forall (StronglySorted leb) xss0 ->
          forall acc,
          { zss | exists xss', zss = rev (map (@rev t) xss') ++ acc /\ length xss' = div2 (S (length xss0))
              /\ Forall (StronglySorted leb) xss'
              /\ Permutation (concat _ xss') (concat _ xss0) }
        with
        | [] => fun _ acc => exist _ acc (ex_intro _ [] _)
        | [xs] => fun _ acc => exist _ (rev xs :: acc) (ex_intro _ [xs] _)
        | xs :: xs' :: xss' => fun _ acc =>
            let (ys, H1) := rev_merge xs _ xs' _ [] in
            let (yss, H2) := meld xss' _ (ys :: acc) in
            exist _ yss (let (zs, _) := H1 in let (zss, _) := H2 in ex_intro _ (zs :: zss) _)
        end);
        repeat (simpl in *;
           ( rewrite app_nil_r in *
          || rewrite rev_involutive in *
          || rewrite <- app_assoc
          || match goal with
             | H : Forall _ (_ :: _) |- _ => inversion H; clear H
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             end
          || split); subst); eauto.
      rewrite app_assoc.
      apply Permutation_app; eauto.
    Defined.

    Definition splitting : forall xs acc prev,
      Forall (StronglySorted leb) acc ->
      { xss | Permutation (concat _ xss) (rev (concat _ acc) ++ prev :: xs)
           /\ Forall (StronglySorted leb) xss }.
    Proof.
      refine (fix neutral xs :=
        match xs as xs0 return
          forall acc prev,
          Forall (StronglySorted leb) acc ->
          { xss | Permutation (concat _ xss) (rev (concat _ acc) ++ prev :: xs0)
               /\ Forall (StronglySorted leb) xss }
        with 
        | [] => fun acc prev _ => exist _ ([prev] :: acc) _
        | x :: xs => fun acc prev _ =>
            if Sumbool.sumbool_of_bool (leb prev x) then _
            else _
        end
      with incr xs :=
        match xs as xs0 return
          forall acc curr prev,
          Forall (StronglySorted leb) acc ->
          StronglySorted (fun x y => leb y x) (prev :: curr) ->
          { xss | Permutation (concat _ xss) (rev (concat _ acc) ++ rev curr ++ prev :: xs0)
               /\ Forall (StronglySorted leb) xss }
        with
        | [] => fun acc curr prev _ _ => exist _ (rev_append curr [prev] :: acc) _
        | x :: xs => fun acc curr prev _ _ =>
            if Sumbool.sumbool_of_bool (leb prev x) then _
            else _
        end
      with decr xs :=
        match xs as xs0 return
          forall acc curr prev,
          Forall (StronglySorted leb) acc ->
          StronglySorted leb (prev :: curr) ->
          { xss | Permutation (concat _ xss) (rev (concat _ acc) ++ prev :: curr ++ xs0)
               /\ Forall (StronglySorted leb) xss }
        with
        | [] => fun acc curr prev _ _ => exist _ ((prev :: curr) :: acc) _
        | x :: xs => fun acc curr prev _ _ =>
            if Sumbool.sumbool_of_bool (leb x prev) then _
            else _
        end
      for neutral);
      [
      | refine (let (xs, _) := incr xs0 acc [prev] x _ _ in exist _ xs _)
      | refine (let (xs, _) := decr xs0 acc [prev] x _ _ in exist _ xs _)
      | 
      | refine (let (xs, _) := incr xs0 acc (prev :: curr) x _ _ in exist _ xs _)
      | refine (let (xs, _) := neutral xs0 (rev_append curr [prev] :: acc) x _ in exist _ xs _)
      | 
      | refine (let (xs, _) := decr xs0 acc (prev :: curr) x _ _ in exist _ xs _)
      | refine (let (xs, _) := neutral xs0 ((prev :: curr) :: acc) x _ in exist _ xs _) ];
      repeat
        (( rewrite app_nil_r in *
        || rewrite <- app_assoc in *
        || rewrite rev_app_distr in *
        || rewrite rev_involutive in *
        || rewrite rev_append_rev in *
        || apply Forall_rev
        || apply StronglySorted_app
        || apply StronglySorted_rev
        || match goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : leb ?x ?y = false |- _ => destruct (leb_total x y); [ congruence | clear H ]
           | H : Forall _ ?l |- Forall _ ?l => eapply Forall_impl; [| apply H ]; intros
           | H : StronglySorted _ (_ :: _) |- _ => inversion H; subst; clear H
           | |- Forall _ (_ :: _) => constructor
           | |- StronglySorted _ (_ :: _) => constructor
           | _ => split
           end
        || split); subst; simpl in *);
      eauto.
    - apply Permutation_rev with (l := prev :: concat t acc).
    - etransitivity.
      + eassumption.
      + eapply Permutation_app_head.
        eauto.
    - etransitivity.
      + eapply Permutation_app_comm.
      + simpl.
        etransitivity.
        * apply Permutation_cons_append.
        * rewrite <- app_assoc.
          apply Permutation_app_tail.
          apply Permutation_rev.
    - etransitivity.
      + eassumption.
      + apply Permutation_app_head.
        etransitivity.
        * apply Permutation_middle.
        * apply Permutation_app_tail.
          apply Permutation_rev.
    - etransitivity.
      + apply Permutation_app_comm with (l := prev :: curr).
      + apply Permutation_app_tail.
        apply Permutation_rev.
    - etransitivity.
      + eassumption.
      + apply Permutation_app_head.
        apply Permutation_middle with (l1 := prev :: curr).
    - etransitivity.
      + eassumption.
      + apply Permutation_app_head.
        symmetry.
        etransitivity.
        * apply Permutation_middle.
        * apply Permutation_app_tail.
          apply Permutation_rev.
    Defined.
  End Tools.

  Arguments ltof A f a b /.

  Definition merge_sort (t : Set) (leb : t -> t -> bool)
    (leb_total : forall x y, leb x y \/ leb y x)
    (leb_trans : Transitive leb) xs :
    { xs' | StronglySorted leb xs' /\ Permutation xs' xs }.
  Proof.
    refine (match xs as xs0 return { xs' | StronglySorted leb xs' /\ Permutation xs' xs0 } with
      | [] => exist _ [] _
      | x :: xs =>
          let (xss, _) := splitting _ leb _ _ xs [] x _ in
          (fix iter_meld xss (Hwf : Acc (ltof _ (@length _)) xss) { struct Hwf } :=
            match xss as xss0 return
              Acc (ltof _ (@length _)) xss0 ->
              Forall (StronglySorted leb) xss0 ->
              Permutation (concat _ xss0) (x :: xs) ->
              { xs' | StronglySorted leb xs' /\ Permutation xs' (x :: xs) }
            with
            | [] => fun _ _ _ => exist _ [] _
            | [xs] => fun _ _ _ => exist _ xs _
            | xs :: xs' :: xss => fun Hwf _ _ =>
                let (xss', _) := meld _ leb _ _ (xs :: xs' :: xss) _ [] in
                match Hwf with
                | Acc_intro Hwf' => _
                end
            end Hwf
          with iter_meld_rev xss (Hwf : Acc (ltof _ (@length _)) xss) { struct Hwf } :=
            match xss as xss0 return
              Acc (ltof _ (@length _)) xss0 ->
              Forall (StronglySorted (fun x y => leb y x)) xss0 ->
              Permutation (concat _ xss0) (x :: xs) ->
              { xs' | StronglySorted leb xs' /\ Permutation xs' (x :: xs) }
            with
            | [] => fun _ _ _ => exist _ [] _
            | [xs] => fun _ _ _ => exist _ (rev xs) _
            | xs :: xs' :: xss => fun Hwf _ _ =>
                let (xss', _) := meld _ (fun x y => leb y x) _ _ (xs :: xs' :: xss) _ [] in
                match Hwf with
                | Acc_intro Hwf' => _
                end
            end Hwf
          for iter_meld) xss (well_founded_ltof _ (@length _) _) _ _
    end);
    [ | | | | | | | refine (iter_meld_rev xss' (Hwf' _ _) _ _) | | | | | | refine (iter_meld xss' (Hwf' _ _) _ _) | | ];
      repeat (simpl in *;
         ( rewrite app_nil_r in *
        || rewrite rev_length in *
        || rewrite map_length in *
        || rewrite concat_rev in *
        || match goal with
           | H : Forall _ (_ ++ _) |- _ => apply Forall_app_iff in H
           | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : Forall _ ?l |- Forall _ ?l => eapply Forall_impl; [| apply H ]
           | |- Permutation (rev ?xs) _ =>
               apply Permutation_trans with (l' := rev (rev xs));
               [ apply Permutation_rev
               | rewrite rev_involutive ]
           end
        || apply Forall_rev
        || apply Forall_map
        || apply StronglySorted_rev
        || split); subst);
      eauto.
    - destruct (length xss1).
      + omega.
      + rewrite H2.
        apply le_n_S.
        apply lt_div2 with (n := S (S n)).
        omega.
    - destruct (length xss1).
      + omega.
      + rewrite H2.
        apply le_n_S.
        apply lt_div2 with (n := S (S n)).
        omega.
  Defined.
End MergeSort.

Require Import ExtrOcamlBasic ExtrOcamlNatInt Mergesort.
Extract Constant map => "List.map".
Extract Constant app => "( @ )".
Extract Constant rev => "List.rev".
Extract Constant rev_append => "List.rev_append".
Extract Constant Sumbool.sumbool_of_bool => "(fun b -> b)".
Extract Constant negb => "not".
Extract Constant NatOrder.leb => "( <= )".
Extraction "merge_sort.ml" NatSort merge_sort.

(* FUCKIN' HEAVY COMPUTATION *)
(* Eval compute in NatSort.merge_sort [1; 1; 4; 5; 1; 4]. *)
