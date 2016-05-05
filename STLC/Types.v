Require Id.

Inductive t :=
  | Bool
  | Fun : t -> t -> t
  | Var : Id.t -> t.
