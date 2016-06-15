datatype form = True
              | False
              | Var of int
              | Neg of form
              | Imp of form * form
              | And of form * form
              | Or of form * form

fun interp v True = true
  | interp v False = false
  | interp v (Var x) = List.nth (v, x)
  | interp v (Neg f) = not (interp v f)
  | interp v (Imp (f1, f2)) = not (interp v f1) orelse interp v f2
  | interp v (And (f1, f2)) = interp v f1 andalso interp v f2
  | interp v (Or (f1, f2)) = interp v f1 orelse interp v f2

fun closed True = 0
  | closed False = 0
  | closed (Var x) = x + 1
  | closed (Neg f) = closed f
  | closed (Imp (f1, f2)) = Int.max (closed f1, closed f2)
  | closed (And (f1, f2)) = Int.max (closed f1, closed f2)
  | closed (Or (f1, f2)) = Int.max (closed f1, closed f2)

fun isTaut f =
  List.all (fn v => interp v f)
    (foldl (fn (bs, vs) =>
      List.concat (map (fn b => map (fn v => b :: v) vs) bs)) [[]]
      (List.tabulate (closed f, fn _ => [true, false])));

isTaut (Imp (Var 0, Var 0));
isTaut (Imp (Var 0, Imp (Var 1, Var 0)));
isTaut (Or (Var 0, Neg (Var 0)));
