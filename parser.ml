(* binary operator parser *)

module type SEQUENCE = sig
  type id
  type exp
  type operator
  type sequence
  type token =
    | Id of id
    | BinOp of operator
    | EOI

  val less_priority : operator -> operator -> bool
  val reduce_id : id -> exp
  val reduce_operator : operator -> exp -> exp -> exp
  val get_token : sequence -> token * sequence
end

module type PARSER = sig
  exception SyntaxError

  type exp
  type sequence

  val parse : sequence -> exp
end

module Parser (Seq : SEQUENCE) : (PARSER with
  type exp = Seq.exp and
  type sequence = Seq.sequence) =
struct
  exception SyntaxError

  type exp = Seq.exp
  type sequence = Seq.sequence

  (* state monad *)
  let return x s = (x, s)
  let ( >>= ) f g s =
    let (a, s') = f s in
    g a s'
  let ( >> ) f g = f >>= (fun _ -> g)

  let rec parse' e1 op1 =
    Seq.get_token >>= (function
      | Seq.EOI | Seq.BinOp _ -> raise SyntaxError
      | Seq.Id x2 ->
          let e2 = Seq.reduce_id x2 in
          Seq.get_token >>= (function
            | Seq.EOI -> return (Seq.reduce_operator op1 e1 e2)
            | Seq.Id _ -> raise SyntaxError
            | Seq.BinOp op2 ->
                if Seq.less_priority op1 op2 then
                  parse' e2 op2 >>= (fun e -> return (Seq.reduce_operator op1 e1 e))
                else
                  parse' (Seq.reduce_operator op1 e1 e2) op2))

  let parse s =
    (Seq.get_token >>= (function
      | Seq.EOI | Seq.BinOp _ -> raise SyntaxError
      | Seq.Id x1 ->
          let e1 = Seq.reduce_id x1 in
          Seq.get_token >>= (function
            | Seq.Id _ -> raise SyntaxError
            | Seq.EOI -> return e1
            | Seq.BinOp op1 -> parse' e1 op1))) s
    |> fst
end

module TestSeq = struct
  exception InconsistentPriority

  type id = string
  type operator = string
  type exp =
    [ `Id of string
    | `Plus of exp * exp
    | `Minus of exp * exp
    | `Times of exp * exp
    | `Power of exp * exp ]
  type token =
    | Id of id
    | BinOp of operator
    | EOI
  type sequence = token list

  type assoc = LeftAssoc | RightAssoc

  let operators =
    [("+", ((fun e1 e2 -> `Plus (e1, e2)), 0, LeftAssoc));
     ("-", ((fun e1 e2 -> `Minus (e1, e2)), 0, LeftAssoc));
     ("*", ((fun e1 e2 -> `Times (e1, e2)), 1, LeftAssoc));
     ("**", ((fun e1 e2 -> `Power (e1, e2)), 2, RightAssoc))]

  let less_priority op1 op2 =
    let (_, prio1, assoc1) = List.assoc op1 operators in
    let (_, prio2, assoc2) = List.assoc op2 operators in
    if prio1 = prio2 && assoc1 <> assoc2 then raise InconsistentPriority
    else prio1 < prio2 || prio1 = prio2 && assoc1 = RightAssoc

  let reduce_id x = `Id x
  let reduce_operator op =
    let (reduce, _, _) = List.assoc op operators in
    reduce

  let get_token = function
    | [] -> (EOI, [])
    | (x :: xs) -> (x, xs)
end

module TestParser = Parser (TestSeq)

(*
open TestSeq;;
open TestParser;;
parse [Id "x"];;
parse [Id "x"; BinOp "+"; Id "y"; BinOp "*"; Id "z"];;
parse [Id "x"; BinOp "+"; Id "y"; BinOp "+"; Id "z"];;
parse [Id "x"; BinOp "+"; Id "y"; BinOp "-"; Id "z"];;
parse [Id "x"; BinOp "**"; Id "y"; BinOp "**"; Id "z"];;
*)
