(* binary operator parser *)

module type SEQUENCE = sig
  type exp
  type sequence
  type assoc = LeftAssoc | RightAssoc
  type token =
    | Id of exp
    | BinOp of ((exp -> exp -> exp) * int * assoc)
    | EOI

  val get_token : sequence -> token * sequence
end

module type PARSER = sig
  exception InconsistentPriority
  exception SyntaxError

  type exp
  type sequence

  val parse : sequence -> exp
end

module Parser (Seq : SEQUENCE) : (PARSER with
  type exp = Seq.exp and
  type sequence = Seq.sequence) =
struct
  exception InconsistentPriority
  exception SyntaxError

  type exp = Seq.exp
  type sequence = Seq.sequence

  (* state monad *)
  let return x s = (x, s)
  let ( >>= ) f g s =
    let (a, s') = f s in
    g a s'
  let ( >> ) f g = f >>= (fun _ -> g)

  let rec parse' e1 (reduce1, prio1, assoc1) =
    Seq.get_token >>= (function
      | Seq.EOI | Seq.BinOp _ -> raise SyntaxError
      | Seq.Id e2 ->
          Seq.get_token >>= (function
            | Seq.EOI -> return (reduce1 e1 e2)
            | Seq.Id _ -> raise SyntaxError
            | Seq.BinOp ((_, prio2, assoc2) as op2) ->
                if prio1 = prio2 && assoc1 <> assoc2 then
                  raise InconsistentPriority
                else if prio1 < prio2 || prio1 = prio2 && assoc1 = Seq.RightAssoc then
                  parse' e2 op2 >>= (fun e -> return (reduce1 e1 e))
                else
                  parse' (reduce1 e1 e2) op2))
  let parse s =
    (Seq.get_token >>= (function
      | Seq.EOI | Seq.BinOp _ -> raise SyntaxError
      | Seq.Id e1 ->
          Seq.get_token >>= (function
            | Seq.Id _ -> raise SyntaxError
            | Seq.EOI -> return e1
            | Seq.BinOp op1 -> parse' e1 op1))) s
    |> fst
end


module TestSeq = struct
  type exp =
    [ `Id of string
    | `Plus of exp * exp
    | `Minus of exp * exp
    | `Times of exp * exp
    | `Power of exp * exp ]
  type token' =
    [ `Id of string
    | `BinOp of string ]
  type sequence = token' list
  type assoc = LeftAssoc | RightAssoc
  type token =
    | Id of exp
    | BinOp of ((exp -> exp -> exp) * int * assoc)
    | EOI

  let operators =
    [("+", ((fun e1 e2 -> `Plus (e1, e2)), 0, LeftAssoc));
     ("-", ((fun e1 e2 -> `Minus (e1, e2)), 0, LeftAssoc));
     ("*", ((fun e1 e2 -> `Times (e1, e2)), 1, LeftAssoc));
     ("**", ((fun e1 e2 -> `Power (e1, e2)), 2, RightAssoc))]

  let get_token = function
    | [] -> (EOI, [])
    | (`Id x :: xs) -> (Id (`Id x), xs)
    | (`BinOp x :: xs) -> (BinOp (List.assoc x operators), xs)
end

module TestParser = Parser (TestSeq)

TestParser.parse [`Id "x"]
TestParser.parse [`Id "x"; `BinOp "+"; `Id "y"; `BinOp "*"; `Id "z"]
TestParser.parse [`Id "x"; `BinOp "+"; `Id "y"; `BinOp "+"; `Id "z"]
TestParser.parse [`Id "x"; `BinOp "+"; `Id "y"; `BinOp "-"; `Id "z"]
TestParser.parse [`Id "x"; `BinOp "**"; `Id "y"; `BinOp "**"; `Id "z"]
