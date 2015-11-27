module type WEIGHT = sig
  type weight
  val ( + ) : weight -> weight -> weight
  val min : weight -> weight -> weight
end

module type WARSHALL_FLOYD = sig
  type weight
  type vertex = int
  type edge_set = vertex -> vertex -> weight
  val warshall_floyd : int -> edge_set -> edge_set
end

module WarshallFloyd (W : WEIGHT) :
  WARSHALL_FLOYD
  with type weight = W.weight
= struct
  type weight = W.weight
  type vertex = int
  type edge_set = vertex -> vertex -> weight
  let warshall_floyd n edge =
    let d =
      Array.init n (fun v ->
        Array.init n (edge v)) in
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        for k = 0 to n - 1 do
          let open W in
          d.(j).(k) <- min d.(j).(k) (d.(j).(i) + d.(i).(k))
        done
      done
    done;
    fun u v -> d.(u).(v)
end

module RoutedWeight = struct
  type weight = float * (int * int) list
  let ( + ) (n1, r1) (n2, r2) = (n1 +. n2, r1 @ r2)

  let min ((n1, r1) as w1) ((n2, r2) as w2) =
    if n1 < n2 || n1 = n2 && List.length r1 < List.length r2 then w1
    else w2
end

module RWWarshallFloyd = WarshallFloyd (RoutedWeight)

let graph = 
  let inf = infinity in
  Array.mapi (fun i row ->
    Array.mapi (fun j w -> (w, [(i, j)])) row)
  [| [| 0.;  4.;  inf; inf; 3.  |];
     [| 4.;  0.;  2.;  inf; inf |];
     [| inf; 2.;  0.;  3.;  2.  |];
     [| inf; inf; 3.;  0.;  7.  |];
     [| 3.;  inf; 2.;  7.;  0.  |] |]

RWWarshallFloyd.warshall_floyd 5 (fun i j -> graph.(i).(j)) 0 3;;
