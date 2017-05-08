module type OrderedType = sig
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

let rec le_ge_dec : type n m. n nat -> m nat -> ((n, m) le, (m, n) le) result =
  fun n m ->
    match n, m with
    | Z, _ -> Ok (le_0_n m)
    | _, Z -> Error (le_0_n n)
    | S n', S m' ->
        begin match le_ge_dec n' m' with
        | Ok hle -> Ok (le_n_s hle)
        | Error hge -> Error (le_n_s hge)
        end

module type HEAP = sig
  type elt
  type t

  val empty : t
  val merge : t -> t -> t
  val insert : elt -> t -> t
  val find_min : t -> elt option
  val delete_min : t -> t option
end

module LeftistHeap (O : OrderedType) : HEAP with type elt = O.t = struct
  type elt = O.t

  type _ tree =
    | Empty : z tree
    | Node : ('r s) nat * ('r, 'l) le * 'l tree * elt * 'r tree -> ('r s) tree
  type t = Exists : 'r tree -> t

  let rank : type r. r tree -> r nat = function
    | Empty -> Z
    | Node (r, _, _, _, _) -> r

  let make_node (Exists a) x (Exists b) =
    let n = rank a in
    let m = rank b in
    match le_ge_dec n m with
    | Ok hle -> Exists (Node (S n, hle, b, x, a))
    | Error hle -> Exists (Node (S m, hle, a, x, b))

  let empty = Exists Empty

  let rec merge h1 h2 =
    match h1, h2 with
    | Exists Empty, _ -> h2
    | _, Exists Empty -> h1
    | Exists (Node (_, _, a1, x, b1)), Exists (Node (_, _, a2, y, b2)) ->
        if O.compare x y <= 0 then make_node (Exists a1) x (merge (Exists b1) h2)
        else make_node (Exists a2) y (merge h1 (Exists b2))

  let insert x = merge (Exists (Node (S Z, LeEq, Empty, x, Empty)))

  let find_min = function
    | Exists Empty -> None
    | Exists (Node (_, _, _, x, _)) -> Some x

  let delete_min = function
    | Exists Empty -> None
    | Exists (Node (_, _, l, _, r)) -> Some (merge (Exists l) (Exists r))
end

module Int = struct
  type t = int
  let compare = compare
end

module IntLeftistHeap = LeftistHeap (Int)

let heap = List.fold_right IntLeftistHeap.insert [1; 1; 4; 5; 1; 4; 8; 10] IntLeftistHeap.empty
let rec dump heap =
  match IntLeftistHeap.find_min heap with
  | None -> ()
  | Some e ->
      Printf.printf "%d\n" e;
      begin match IntLeftistHeap.delete_min heap with
      | None -> ()
      | Some heap' -> dump heap'
      end

let () = dump heap
