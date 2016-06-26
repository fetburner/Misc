Require Id Types Exp.
Require Import List.

Module Value.
  Inductive t :=
    | Bool : bool -> t
    | Clos : list t -> Exp.t -> t.
End Value.

Inductive evalto : list Value.t -> Exp.t -> Value.t -> Prop :=
  | E_Var : forall env x v,
      nth x (map Some env) None = Some v ->
      evalto env (Exp.Var x) v
  | E_Abs : forall env e t,
      evalto env (Exp.Abs t e) (Value.Clos env e)
  | E_App : forall env e1 e2 env0 e v2 v,
      evalto env e1 (Value.Clos env0 e) ->
      evalto env e2 v2 ->
      evalto (v2 :: env0) e v ->
      evalto env (Exp.App e1 e2) v
  | E_Bool : forall env b,
      evalto env (Exp.Bool b) (Value.Bool b).
Hint Constructors evalto.
