let warshall_floyd ( + ) min loop n d =
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      for k = 0 to n - 1 do
        d.(j).(k) <- min d.(j).(k) (d.(j).(i) + loop d.(i).(i) + d.(i).(k))
      done
    done
  done

let graph = 
  let inf = infinity in
  Array.mapi (fun i row ->
    Array.mapi (fun j w -> (w, if i = j then [] else [(i, j)])) row)
  [| [| 0.;  4.;  inf; inf; 3.  |];
     [| 4.;  0.;  2.;  inf; inf |];
     [| inf; 2.;  0.;  3.;  2.  |];
     [| inf; inf; 3.;  0.;  7.  |];
     [| 3.;  inf; 2.;  7.;  0.  |] |];;
warshall_floyd
  (fun (n1, r1) (n2, r2) -> (n1 +. n2, r1 @ r2))
  (fun ((n1, _) as w1) ((n2, _) as w2) ->
    if n1 <= n2 then w1
    else w2)
  (fun x -> (0., [])) 5 graph;;
graph;;

let graph = 
  let inf = infinity in
  [| [| 0.;  4.;  inf; inf; 3.  |];
     [| 4.;  0.;  2.;  inf; inf |];
     [| inf; 2.;  0.;  3.;  2.  |];
     [| inf; inf; 3.;  0.;  7.  |];
     [| 3.;  inf; 2.;  7.;  0.  |] |];;
warshall_floyd ( +. ) min (fun x -> 0.) 5 graph;;
graph;;

type regexp =
  (* 文字*)
  | Lit of string
  (* ε *)
  | Eps
  (* 何も受理しない *)
  | Delta
  (* 連接 *)
  | Seq of regexp * regexp
  (* | *)
  | Sum of regexp * regexp
  (* * *)
  | Repeat of regexp

(* 見づらいので簡約する *)
let sum s1 s2 =
  match s1, s2 with
  | Delta, _ -> s2
  | _, Delta -> s1
  | _, _ ->
      if s1 = s2 then s1
      else Sum (s1, s2)

let seq s1 s2 =
  match s1, s2 with
  | Delta, _ -> Delta
  | _, Delta -> Delta
  | Eps, _ -> s2
  | _, Eps -> s1
  | _, _ -> Seq (s1, s2)

let repeat = function
  | Eps -> Eps
  | Delta -> Eps
  | (Repeat _) as s -> s
  | s -> Repeat s

let automata =
  [| [| Delta; Lit "wa"; Delta;    Delta;    Delta;   Delta    |];
     [| Delta; Delta;    Lit "ka"; Delta;    Delta;   Delta    |];
     [| Delta; Delta;    Lit "ba"; Lit "ga"; Delta;   Delta    |];
     [| Delta; Delta;    Delta;    Delta;    Lit "-"; Delta    |];
     [| Delta; Delta;    Delta;    Delta;    Delta;   Lit "ru" |];
     [| Delta; Delta;    Delta;    Delta;    Delta;   Delta    |] |];;
warshall_floyd seq sum repeat 6 automata;;

(* わかば*ガール *)
automata.(0).(5);;
