(* quite naive implementation *)
let rec dikjstra ( +. ) q edge d =
  match q with
  | [] -> ()
  | u :: q ->
      let u, q = 
        List.fold_left (fun (u, q') u' ->
          if d.(u) < d.(u') then (u, u' :: q') else (u', u :: q')) (u, []) q in
      List.iter (fun (v, c) ->
        d.(v) <- min d.(v) (d.(u) +. c)) (edge u);
      dikjstra ( +. ) q edge d


let d = Array.make 6 infinity;;
d.(0) <- 0.;;
dikjstra ( +. ) [0; 1; 2; 3; 4; 5] (function
  | 0 -> [ (1, 7.); (2, 9.); (5, 14.) ]
  | 1 -> [ (0, 7.); (2, 10.); (3, 15.) ]
  | 2 -> [ (0, 9.); (1, 10.); (3, 11.); (5, 2.) ]
  | 3 -> [ (1, 15.); (2, 11.); (4, 6.) ]
  | 4 -> [ (3, 6.); (5, 9.) ]
  | 5 -> [ (0, 14.); (2, 2.); (4, 9.) ]) d;;
d;;
