Require Import List Relations ZArith Lia Program ssreflect.

Section Maximum.
  Variable A : Set.
  Variable max : A -> A -> A.
  Definition maximum x xs := fold_left max xs x.

  Hypothesis max_select : forall x y, max x y = x \/ max x y = y.

  Theorem maximum_select : forall xs x, In (maximum x xs) (x :: xs).
  Proof.
    elim => /= [ | x ? IH x' ]; eauto.
    case (max_select x' x) => ->; [ case (IH x') | case (IH x) ]; eauto.
  Qed.

  Variable le : relation A.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis max_left : forall x y, le x (max x y).
  Hypothesis max_right : forall x y, le y (max x y).

  Theorem maximum_join : forall xs x y, In y (x :: xs) -> le y (maximum x xs).
  Proof.
    elim => /= [ ? ? [ -> | [ ] ] | x xs IHxs x' y [ -> | [ -> | ] ] ]; eauto.
  Qed.

  Definition maximum_spec x xs := conj (maximum_select xs x) (maximum_join xs x).

  Definition maximum_concrete x xs :
    fold_left max xs x = maximum x xs := eq_refl.
End Maximum.

Section ZMaximum.
  Local Open Scope Z_scope.

  Definition Zmaximum := maximum _ Z.max.
  Definition Zminimum := maximum _ Z.min.

  Corollary Zmaximum_spec : forall x xs,
    (In (Zmaximum x xs) (x :: xs)) /\
    (forall y, In y (x :: xs) -> y <= Zmaximum x xs).
  Proof. by apply /maximum_spec; lia. Qed.

  Corollary Zminimum_spec : forall x xs,
    In (Zminimum x xs) (x :: xs) /\
    (forall y, In y (x :: xs) -> y >= Zminimum x xs).
  Proof. by apply /maximum_spec; lia. Qed.

  Corollary neg_Zmaximum_distr x xs :
    - Zmaximum x xs = Zminimum (- x) (map Z.opp xs).
  Proof.
    case (Zmaximum_spec x xs) => HmaxIn Hmax.
    case (Zminimum_spec (- x) (map Z.opp xs)) => HminIn Hmin.
    have /Hmin : In (- Zmaximum x xs) (map Z.opp (x :: xs)) by apply /in_map.
    have : In (- Zminimum (- x) (map Z.opp xs)) (map Z.opp (map Z.opp (x :: xs))) by apply /in_map.
    rewrite map_map (map_ext (fun x => - - x) id) /id ?map_id => [ | /Hmax ]; lia.
  Qed.

  Corollary neg_Zminimum_distr x xs :
    - Zminimum x xs = Zmaximum (- x) (map Z.opp xs).
  Proof.
    have -> : Zminimum x xs = Zminimum (- - x) (map Z.opp (map Z.opp xs)).
    { congr (Zminimum _ _).
      - by lia.
      - rewrite map_map -(map_ext id) ?map_id // /id. by lia. }
    rewrite -neg_Zmaximum_distr. by lia.
  Qed.

  Corollary Zmaximum_concrete : forall x xs,
    fold_left Z.max xs x = Zmaximum x xs.
  Proof. exact /maximum_concrete. Qed.
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
        | nil => eval b
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
        | nil => eval b
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
        | nil =>
            if turn then eval b
            else - eval b
        | b :: bs =>
            Zmaximum
              (- negmax (negb turn) b n)
              (map Z.opp (map (fun b => negmax (negb turn) b n) bs))
        end
    end.

  Theorem negmax_corresponds_minimax : forall n b turn,
    negmax turn b n = if turn then minimax b n else - minimax' b n.
  Proof.
    elim => /= [ ? [ ] | ? IH b [ ] ] //; case (succ b) => // ? ?.
    - rewrite map_map.
      congr (Zmaximum _ _); [ | apply /map_ext => ? ]; rewrite IH /=; by lia.
    - rewrite -neg_Zminimum_distr.
      congr (- Zminimum _ _); [ | apply /map_ext => ? ]; rewrite IH /=; by lia.
  Qed.

  Definition Zmaximum_with_alpha {A} alphabeta alpha beta := (fix Zmaximum_with_alpha alpha (xs : list A) :=
    match xs with
    | nil => alpha
    | x :: xs =>
        let value := alphabeta alpha x in
        match Z_le_dec beta value with
        | left _ => value
        | right _ => Zmaximum_with_alpha (Z.max alpha value) xs
        end
    end) alpha.

  Lemma Zmaximum_with_alpha_spec_aux A minimax alphabeta beta
    (Halphabeta_spec : forall alpha (x : A),
      alpha < beta ->
      minimax x <= alpha /\ alphabeta alpha x <= alpha \/
      alpha <= minimax x /\ minimax x = alphabeta alpha x /\ minimax x < beta \/
      beta <= minimax x /\ beta <= alphabeta alpha x) :
    forall xs alpha,
    alpha < beta ->
    fold_left Z.max (map minimax xs) alpha = Zmaximum_with_alpha alphabeta alpha beta xs /\
    fold_left Z.max (map minimax xs) alpha < beta \/
    beta <= fold_left Z.max (map minimax xs) alpha /\ beta <= Zmaximum_with_alpha alphabeta alpha beta xs.
  Proof.
    elim => /= [ | x xs IH alpha ? ].
    - lia.
    - case (Halphabeta_spec alpha x) => //= [ [ ? ? ] | [ [ ? [ <- ? ] ] | [ ? ? ] ] ].
      + case (Z_le_dec beta (alphabeta alpha x)) => ?; try lia.
        rewrite !Z.max_l; try lia.
        exact /IH.
      + case (Z_le_dec beta (minimax x)) => ?; try lia.
        rewrite !Z.max_r; try lia.
        exact /IH.
      + case (Z_le_dec beta (alphabeta alpha x)) => ?; try lia.
        rewrite Zmaximum_concrete !Z.max_r; try lia.
        move: (proj2 (Zmaximum_spec (minimax x) (map minimax xs)) _ (or_introl eq_refl)).
        lia.
  Qed.

  Corollary Zmaximum_with_alpha_spec A minimax alphabeta alpha beta xs
    (Halphabeta : alpha < beta)
    (Halphabeta_spec : forall alpha (x : A),
      alpha < beta ->
      minimax x <= alpha /\ alphabeta alpha x <= alpha \/
      alpha <= minimax x /\ minimax x = alphabeta alpha x /\ minimax x < beta \/
      beta <= minimax x /\ beta <= alphabeta alpha x) :
    alpha <= Zmaximum alpha (map minimax xs) /\
    Zmaximum alpha (map minimax xs) = Zmaximum_with_alpha alphabeta alpha beta xs /\
    Zmaximum alpha (map minimax xs) < beta \/
    beta <= Zmaximum alpha (map minimax xs) /\ beta <= Zmaximum_with_alpha alphabeta alpha beta xs.
  Proof.
    rewrite -Zmaximum_concrete.
    move: (Zmaximum_with_alpha_spec_aux _ _ _ _ Halphabeta_spec xs _ Halphabeta) => [ ] [ ? ? ]; [ left | right ]; repeat split; eauto.
    rewrite Zmaximum_concrete.
    apply /(proj2 (Zmaximum_spec _ _)). by left.
  Qed.

  Fixpoint alphabeta (turn : bool) alpha beta b n :=
    match n with
    | O =>
        if turn then eval b
        else - eval b
    | S n =>
        match succ b with
        | nil =>
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
    elim => /= [ | n IHn b beta ]; try lia.
    case (succ b) => [ | b_ bs ] turn alpha ?; try lia.
    rewrite map_map.
    case (Z_lt_dec alpha (Zmaximum (- negmax (negb turn) b_ n) (map (fun b => - negmax (negb turn) b n) bs))) => ?.
    - right.
      have -> : Zmaximum (- negmax (negb turn) b_ n) (map (fun x => - negmax (negb turn) x n) bs) = Zmaximum alpha (map (fun x => - negmax (negb turn) x n) (b_ :: bs)).
      { case (Zmaximum_spec (- negmax (negb turn) b_ n) (map (fun b => - negmax (negb turn) b n) bs)) => HIn1 Hmax1.
        case (Zmaximum_spec alpha (map (fun b => - negmax (negb turn) b n) (b_ :: bs))) => [ [ ? | HIn2 ] Hmax2 ]; have := Hmax2 _ (or_intror HIn1); [ | have := (Hmax1 _ HIn2) ]; lia. }
      { apply /(Zmaximum_with_alpha_spec _ _ (fun alpha b => - alphabeta (negb turn) (- beta) (- alpha) b n) _ beta (b_ :: bs)) => // alpha0 b0 ?.
        case (IHn b0 (- alpha0) (negb turn) (- beta)) => [ | [ ] | [ [ ? [ ] ] | [ ] ] ]; lia. }
    - left.
      have : Zmaximum alpha (map (fun b => - negmax (negb turn) b n) (b_ :: bs)) = alpha.
      { case (Zmaximum_spec (- negmax (negb turn) b_ n) (map (fun b => - negmax (negb turn) b n) bs)) => HIn1 Hmax1.
        case (Zmaximum_spec alpha (map (fun b => - negmax (negb turn) b n) (b_ :: bs))) => [ [ | HIn2 ] Hmax2 ];
        [ | move: (Hmax2 _ (or_intror HIn1)) (Hmax2 _ (or_introl eq_refl)) (Hmax1 _ HIn2) ]; lia. }
      case (Zmaximum_with_alpha_spec _
        (fun b => - negmax (negb turn) b n)
        (fun alpha b => - alphabeta (negb turn) (- beta) (- alpha) b n) alpha beta (b_ :: bs)) => /= [ | alpha0 b0 ? | | ]; try lia.
      case (IHn b0 (- alpha0) (negb turn) (- beta)) => [ | [ ] | [ [ ? [ ] ] | [ ] ] ]; lia.
  Qed.
End MinMax.
