module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

type z = Z_
type 'n s = S_ : 'n -> 'n s
type _ nat =
  | Z : z nat
  | S : 'n nat -> 'n s nat

type (_, _) le =
  | LeEq : ('n, 'n) le
  | LeS : ('n, 'm) le -> ('n, 'm s) le

let rec le_n_s : type n m. (n, m) le -> (n s, m s) le = function
  | LeEq -> LeEq
  | LeS hle -> LeS (le_n_s hle)

let rec le_0_n : type n. n nat -> (z, n) le = function
  | Z -> LeEq
  | S n -> LeS (le_0_n n)

let rec le_ge_dec : type n m. n nat -> m nat -> [ `InL of (n, m) le | `InR of (m, n) le ] =
  fun n m ->
    match n, m with
    | Z, _ -> `InL (le_0_n m)
    | _, Z -> `InR (le_0_n n)
    | S n', S m' ->
        begin match le_ge_dec n' m' with
        | `InL hle -> `InL (le_n_s hle)
        | `InR hge -> `InR (le_n_s hge)
        end

module type HEAP = sig
  type elt
  type t

  val empty : t
  val singleton : elt -> t
  val merge : t -> t -> t
  val insert : elt -> t -> t
  val find_min : t -> elt option
  val delete_min : t -> t option
end

module BinomialHeap (O : OrderedType) : HEAP with type elt = O.t = struct
  type elt = O.t

  type 'n tree = Node of elt * 'n tree_vector
  and _ tree_vector =
    | TNil : z tree_vector
    | TCons : 'n tree * 'n tree_vector -> 'n s tree_vector

  type _ tree_opt_vector =
    | TONil : z tree_opt_vector
    | TOCons : 'n tree option * 'n tree_opt_vector -> 'n s tree_opt_vector

  type t = T : 'n nat * 'n tree_opt_vector -> t

  let rec tree_opt_vector_of_tree_vector : type n. n tree_vector -> n tree_opt_vector = function
    | TNil -> TONil
    | TCons (t, tv) -> TOCons (Some t, tree_opt_vector_of_tree_vector tv)

  let merge_tree (Node (e1, ts1) as t1) (Node (e2, ts2) as t2) =
    if O.compare e1 e2 < 0 then Node (e1, TCons (t2, ts1))
    else Node (e2, TCons (t1, ts2))

  let rec merge_tree_opt_vector : type n. n tree_opt_vector -> n tree_opt_vector -> n tree_opt_vector * n tree option = fun tov1 tov2 ->
    match tov1, tov2 with
    | TONil, TONil -> (TONil, None)
    | TOCons (to1, tov1'), TOCons (to2, tov2') ->
        let (tov12, to3) = merge_tree_opt_vector tov1' tov2' in
        begin match to1, to2, to3 with
        | _, None, None -> (TOCons (to1, tov12), None)
        | None, _, None -> (TOCons (to2, tov12), None)
        | None, None, _ -> (TOCons (to3, tov12), None)
        | _, Some t2, Some t3 -> (TOCons (to1, tov12), Some (merge_tree t2 t3))
        | Some t1, _, Some t3 -> (TOCons (to2, tov12), Some (merge_tree t1 t3))
        | Some t1, Some t2, _ -> (TOCons (to3, tov12), Some (merge_tree t1 t2))
        end

  let delete_min_tree_opt_vector_aux1 tov = function
    | None -> None
    | Some (Node (e, tv)) -> 
        Some (e, fun () ->
          let (tov', to0) = merge_tree_opt_vector tov (tree_opt_vector_of_tree_vector tv) in
          TOCons (to0, tov'))

  let delete_min_tree_opt_vector_aux2 to0 = function
    | None -> None
    | Some (e, tov) -> Some (e, fun () -> TOCons (to0, tov ()))

  let rec delete_min_tree_opt_vector : type n. n tree_opt_vector -> (elt * (unit -> n tree_opt_vector)) option = function
    | TONil -> None
    | TOCons (to0, tov) ->
        begin match delete_min_tree_opt_vector_aux1 tov to0, delete_min_tree_opt_vector_aux2 to0 (delete_min_tree_opt_vector tov) with
        | None, None -> None
        | (Some _ as result1), None -> result1
        | None, (Some _ as result2) -> result2
        | (Some (e1, _) as result1), (Some (e2, _) as result2) ->
            if O.compare e1 e2 < 0 then result1
            else result2
        end

  let rec padding : type n m. n tree_opt_vector -> (n, m) le -> m tree_opt_vector = fun t hle ->
    match hle with
    | LeEq -> t
    | LeS hle' -> TOCons (None, padding t hle')

  let empty = T (Z, TONil)
  let singleton e = T (S Z, TOCons (Some (Node (e, TNil)), TONil))

  let merge (T (n1, tov1)) (T (n2, tov2)) =
    match le_ge_dec n1 n2 with
    | `InL hle ->
        begin match merge_tree_opt_vector (padding tov1 hle) tov2 with
        | tov', None -> T (n2, tov')
        | tov', (Some _ as to0) -> T (S n2, TOCons (to0, tov'))
        end
    | `InR hgt ->
        begin match merge_tree_opt_vector tov1 (padding tov2 hgt) with
        | tov', None -> T (n1, tov')
        | tov', (Some _ as to0) -> T (S n1, TOCons (to0, tov'))
        end

  let insert e t = merge (singleton e) t

  let find_min (T (_, tov)) =
    match delete_min_tree_opt_vector tov with
    | None -> None
    | Some (e, _) -> Some e

  let delete_min (T (n, tov)) =
    match delete_min_tree_opt_vector tov with
    | None -> None
    | Some (_, tov') ->
        begin match n, tov' () with
        | S n', TOCons (None, tov'') -> Some (T (n', tov''))
        | _, tov'' -> Some (T (n, tov''))
        end
end

module Int = struct
  type t = int
  let compare = compare
end

module IntBinomialHeap = BinomialHeap (Int)

let heap = List.fold_right IntBinomialHeap.insert [1; 1; 4; 5; 1; 4; 8; 10] IntBinomialHeap.empty
let rec dump heap =
  match IntBinomialHeap.find_min heap with
  | None -> ()
  | Some e ->
      Printf.printf "%d\n" e;
      begin match IntBinomialHeap.delete_min heap with
      | None -> ()
      | Some heap' -> dump heap'
      end

let () = dump heap
