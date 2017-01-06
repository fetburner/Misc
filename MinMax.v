Require Import List Relations ZArith Omega Program.

Section Maximum.
  Variable A : Set.
  Variable max : A -> A -> A.
  Definition maximum := fold_right max.

  Hypothesis max_select : forall x y, max x y = x \/ max x y = y.

  Theorem maximum_select y xs : y = maximum y xs \/ In (maximum y xs) xs.
  Proof.
    induction xs as [ | x xs ]; simpl.
    - eauto.
    - destruct (max_select x (maximum y xs)) as [ Heq | Heq ];
        rewrite Heq;
        destruct IHxs;
        eauto.
  Qed.

  Variable le : relation A.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis max_join : forall x y, le x (max x y) /\ le y (max x y).

  Theorem maximum_join x xs : forall y, x = y \/ In y xs -> le y (maximum x xs).
  Proof.
    induction xs as [ | x' xs ]; simpl in *.
    - intros ? [ ? | [] ]; subst; eauto.
    - destruct (max_join x' (maximum x xs)).
      intros ? [ ? | [ ? | HIn ] ];
        subst;
        [ specialize (IHxs _ (or_introl eq_refl)) | | specialize (IHxs _ (or_intror HIn)) ];
        eauto.
  Qed.

  Definition maximum_spec x xs := conj (maximum_select x xs) (maximum_join x xs).

  Definition maximum_concrete
    (Hassoc : forall x y z, max x (max y z) = max (max x y) z)
    (Hcomm : forall x y, max x y = max y x) x xs :
    fold_left max xs x = maximum x xs := fold_symmetric _ Hassoc Hcomm x xs.
End Maximum.

Section ZMaximum.
  Local Open Scope Z_scope.

  Definition Zmaximum := maximum _ Z.max.
  Definition Zminimum := maximum _ Z.min.

  Corollary Zmaximum_spec : forall x xs,
    (x = Zmaximum x xs \/ In (Zmaximum x xs) xs) /\
    (forall y, x = y \/ In y xs -> y <= Zmaximum x xs).
  Proof.
    apply maximum_spec; try (intros; omega).
    - intros x y.
      destruct (Zmax_spec x y) as [[]|[]]; omega. 
    - intros x y.
      destruct (Zmax_spec x y) as [[]|[]]; omega.
  Qed.

  Corollary Zminimum_spec : forall x xs,
    (x = Zminimum x xs \/ In (Zminimum x xs) xs) /\
    (forall y, x = y \/ In y xs -> y >= Zminimum x xs).
  Proof.
    apply maximum_spec; try (intros; omega).
    - intros x y.
      destruct (Zmin_spec x y) as [[]|[]]; omega. 
    - intros x y.
      destruct (Zmin_spec x y) as [[]|[]]; omega.
  Qed.

  Theorem neg_Zmaximum_distr x xs :
    - Zmaximum x xs = Zminimum (- x) (map Z.opp xs).
  Proof.
    (destruct (Zmaximum_spec x xs) as [ [ ? | ? ] Hmax ];
      assert (HIn1 : - x = - Zmaximum x xs \/ In (- Zmaximum x xs) (map Z.opp xs));
      [ left;
        omega | 
      | right; 
        apply in_map;
        eauto | ]);
    (destruct (Zminimum_spec (- x) (map Z.opp xs)) as [ [ ? | HIn0 ] Hmin ];
      assert (HIn2 : x = - Zminimum (- x) (map Z.opp xs) \/ In (- Zminimum (- x) (map Z.opp xs)) xs);
      [ left;
        omega | 
      | right;
        apply in_map_iff in HIn0;
        destruct HIn0 as [ ? [ Heq ? ]];
        rewrite <- Heq;
        rewrite Z.opp_involutive;
        eauto | ]);
    specialize (Hmax _ HIn2);
    specialize (Hmin _ HIn1);
    omega.
  Qed.

  Corollary neg_Zminimum_distr x xs :
    - Zminimum x xs = Zmaximum (- x) (map Z.opp xs).
  Proof.
    replace (Zminimum x xs) with (Zminimum (- - x) (map Z.opp (map Z.opp xs))).
    - rewrite <- neg_Zmaximum_distr.
      omega.
    - f_equal.
      + omega.
      + rewrite <- map_id.
        repeat rewrite map_map.
        apply map_ext.
        intros ?.
        omega.
  Qed.

  Corollary Zmaximum_concrete : forall x xs,
    fold_left Z.max xs x = Zmaximum x xs.
  Proof.
    apply maximum_concrete.
    - apply Z.max_assoc.
    - apply Z.max_comm.
  Qed.
End ZMaximum.

Section MinMax.
  Local Open Scope Z_scope.

  Variable board : Set.
  Variable succ : board -> list board.
  Variable eval : board -> Z.

  Fixpoint minimax b n :=
    match n with
    | O => eval b
    | S n =>
        match succ b with
        | [] => eval b
        | b :: bs =>
            Zmaximum 
              (minimax' b n)
              (map (fun b => minimax' b n) bs)
        end
    end
  with minimax' b n :=
    match n with
    | O => eval b
    | S n =>
        match succ b with
        | [] => eval b
        | b :: bs =>
            Zminimum
              (minimax b n)
              (map (fun b => minimax b n) bs)
        end
    end.

  Fixpoint negmax (turn : bool) b n :=
    match n with
    | O =>
        if turn then eval b
        else - eval b
    | S n =>
        match succ b with
        | [] =>
            if turn then eval b
            else - eval b
        | b :: bs =>
            Zmaximum
              (- negmax (negb turn) b n)
              (map Z.opp (map (fun b => negmax (negb turn) b n) bs))
        end
    end.

  Theorem negmax_corresponds_minimax : forall n b,
    minimax b n = negmax true b n /\
    negmax false b n = - minimax' b n.
  Proof.
    intros n.
    induction n as [ | n ]; intros b0; simpl.
    - eauto.
    - destruct (succ b0) as [ | b bs ].
      + eauto.
      + split.
        * rewrite map_map.
          f_equal; [ | apply map_ext; intros ? ];
            rewrite (proj2 (IHn _));
            omega.
        * rewrite <- neg_Zminimum_distr.
          do 2 f_equal; [ | apply map_ext; intros ? ];
            rewrite (proj1 (IHn _));
            omega.
  Qed.

  Definition Zmaximum_with_alpha {A} alphabeta alpha beta := (fix Zmaximum_with_alpha alpha (xs : list A) :=
    match xs with
    | nil => alpha
    | x :: xs =>
        let value := alphabeta alpha x in
        if Z_le_dec beta value then value
        else Zmaximum_with_alpha (Z.max alpha value) xs
    end) alpha.

  Lemma Zmaximum_with_alpha_spec_aux A minimax alphabeta beta xs :
    (forall alpha (x : A),
      alpha < beta ->
      minimax x <= alpha /\ alphabeta alpha x <= alpha \/
      alpha <= minimax x /\ minimax x = alphabeta alpha x /\ minimax x < beta \/
      beta <= minimax x /\ beta <= alphabeta alpha x) ->
    forall alpha,
    alpha < beta ->
    fold_left Z.max (map minimax xs) alpha = Zmaximum_with_alpha alphabeta alpha beta xs /\
    fold_left Z.max (map minimax xs) alpha < beta \/
    beta <= fold_left Z.max (map minimax xs) alpha /\ beta <= Zmaximum_with_alpha alphabeta alpha beta xs.
  Proof.
    intros Halphabeta_spec.
    induction xs as [ | x xs ]; simpl; intros alpha Halphabeta.
    - omega.
    - destruct (Halphabeta_spec alpha x Halphabeta) as [ [ ] | [ [ ? [ Heq ] ] | [ ] ]].
      + destruct (Z_le_dec beta (alphabeta alpha x)); [ omega | ].
        repeat rewrite Z.max_l by assumption.
        apply IHxs; assumption.
      + rewrite <- Heq.
        destruct (Z_le_dec beta (minimax x)); [ omega | ].
        rewrite Z.max_r by omega.
        apply IHxs; assumption.
      + right.
        destruct (Z_le_dec beta (alphabeta alpha x)); [ | omega ].
        rewrite Z.max_r by omega.
        split.
        * rewrite Zmaximum_concrete.
          specialize (proj2 (Zmaximum_spec (minimax x) (map minimax xs)) _ (or_introl eq_refl)).
          omega.
        * assumption.
  Qed.

  Corollary Zmaximum_with_alpha_spec A minimax alphabeta alpha beta xs :
    alpha < beta ->
    (forall alpha (x : A),
      alpha < beta ->
      minimax x <= alpha /\ alphabeta alpha x <= alpha \/
      alpha <= minimax x /\ minimax x = alphabeta alpha x /\ minimax x < beta \/
      beta <= minimax x /\ beta <= alphabeta alpha x) ->
    alpha <= fold_left Z.max (map minimax xs) alpha /\
    fold_left Z.max (map minimax xs) alpha = Zmaximum_with_alpha alphabeta alpha beta xs /\
    fold_left Z.max (map minimax xs) alpha < beta \/
    beta <= fold_left Z.max (map minimax xs) alpha /\ beta <= Zmaximum_with_alpha alphabeta alpha beta xs.
  Proof.
    intros Halphabeta Halphabeta_spec.
    destruct (Zmaximum_with_alpha_spec_aux _ _ _ _ xs Halphabeta_spec _ Halphabeta) as [ [ ] | [ ] ];
      [ left | right ];
      repeat split; eauto.
    rewrite Zmaximum_concrete.
    apply (proj2 (Zmaximum_spec _ _)).
    eauto.
  Qed.

  Fixpoint alphabeta (turn : bool) alpha beta b n :=
    match n with
    | O => 
        if turn then eval b
        else - eval b
    | S n =>
        match succ b with
        | [] => 
            if turn then eval b
            else - eval b
        | bs =>
            Zmaximum_with_alpha
              (fun alpha b => - alphabeta (negb turn) (- beta) (- alpha) b n)
              alpha beta bs
        end
    end.

  Theorem alphabeta_corresponds_negmax : forall n b beta turn alpha,
    alpha < beta ->
    negmax turn b n <= alpha /\ alphabeta turn alpha beta b n <= alpha \/
    alpha <= negmax turn b n /\
    negmax turn b n = alphabeta turn alpha beta b n /\
    negmax turn b n < beta \/
    beta <= negmax turn b n /\ beta <= alphabeta turn alpha beta b n.
  Proof.
    intros n.
    induction n as [ | n ]; simpl; intros b beta.
    - intros; omega.
    - destruct (succ b) as [ | b_ bs ]; intros turn alpha Halphabeta.
      + omega.
      + rewrite map_map.
        destruct (Z_lt_dec alpha (Zmaximum (- negmax (negb turn) b_ n)
          (map (fun b => - negmax (negb turn) b n) bs))) as [ | ].
        * right.
          replace (Zmaximum (- negmax (negb turn) b_ n) (map (fun x => - negmax (negb turn) x n) bs))
             with (Zmaximum alpha (map (fun x => - negmax (negb turn) x n) (b_ :: bs))).
          { rewrite <- Zmaximum_concrete.
            apply (Zmaximum_with_alpha_spec _ _
              (fun alpha b => - alphabeta (negb turn) (- beta) (- alpha) b n) _ beta (b_ :: bs) Halphabeta).
            intros alpha0 b0 ?.
            assert (Halphabeta0 : -beta < -alpha0) by omega.
            destruct (IHn b0 (- alpha0) (negb turn) (- beta) Halphabeta0) as [ [] | [ [ ? [] ] | [ ] ] ]; omega. }
          { destruct (Zmaximum_spec (- negmax (negb turn) b_ n) (map (fun b => - negmax (negb turn) b n) bs)) as [ HIn1 Hmax1 ].
            destruct (Zmaximum_spec alpha (map (fun b => - negmax (negb turn) b n) (b_ :: bs))) as [ [ | HIn2 ] Hmax2 ];
              specialize (Hmax2 _ (or_intror HIn1)).
            - omega.
            - specialize (Hmax1 _ HIn2).
              omega. }
        * left.
          assert (fold_left Z.max (map (fun b => - negmax (negb turn) b n) (b_ :: bs)) alpha = alpha).
          { rewrite Zmaximum_concrete.
            destruct (Zmaximum_spec (- negmax (negb turn) b_ n) (map (fun b => - negmax (negb turn) b n) bs)) as [ HIn1 Hmax1 ].
            destruct (Zmaximum_spec alpha (map (fun b => - negmax (negb turn) b n) (b_ :: bs))) as [ [ | HIn2 ] Hmax2 ].
            - omega.
            - generalize (Hmax2 _ (or_intror HIn1)). intros ?.
              specialize (Hmax2 _ (or_introl eq_refl)).
              specialize (Hmax1 _ HIn2).
              omega. }
          destruct (Zmaximum_with_alpha_spec _
            (fun b => - negmax (negb turn) b n)
            (fun alpha b => - alphabeta (negb turn) (- beta) (- alpha) b n) alpha beta (b_ :: bs) Halphabeta) as [ [ ? [ ] ] | [ ] ]; simpl in *; try omega.
          intros alpha0 b0 ?.
          assert (Halphabeta0 : -beta < -alpha0) by omega.
          destruct (IHn b0 (- alpha0) (negb turn) (- beta) Halphabeta0) as [ [] | [ [ ? [] ] | [ ] ] ]; omega.
  Qed.
End MinMax.
