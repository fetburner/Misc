(* 命題論理式 *)
datatype prop = PVAR of string
              | ~~ of prop
              | /\ of prop * prop
              | \/ of prop * prop
              | --> of prop * prop

infix 5 /\
infix 4 \/
infixr 3 -->

(* 正論理か負論理か *)
datatype polarity = POSITIVE | NEGATIVE

(* 否定標準形 *)
datatype nnf = NNFVAR of polarity * string
             | /\~ of nnf * nnf
             | \/~ of nnf * nnf

infix 5 /\~
infix 4 \/~

type cnf = (polarity * string) list list

(* nnfOfProp POSITIVE p は命題論理式 p  の否定標準形を，
 * nnfOfProp NEGATIVE p は命題論理式 ~~P の否定標準形を求める． *)
fun nnfOfProp polar (PVAR x) = NNFVAR (polar, x)
  | nnfOfProp POSITIVE (~~ p) = nnfOfProp NEGATIVE p
  (* ~~ ~~ P = P *)
  | nnfOfProp NEGATIVE (~~ p) = nnfOfProp POSITIVE p
  | nnfOfProp POSITIVE (p /\ q) =
      nnfOfProp POSITIVE p /\~ nnfOfProp POSITIVE q
  (* ~~(P /\ Q) = ~~P \/ ~~Q *)
  | nnfOfProp NEGATIVE (p /\ q) =
      nnfOfProp NEGATIVE p \/~ nnfOfProp NEGATIVE q
  | nnfOfProp POSITIVE (p \/ q) =
      nnfOfProp POSITIVE p \/~ nnfOfProp POSITIVE q
  (* ~~(P \/ Q) = ~~P /\ ~~Q *)
  | nnfOfProp NEGATIVE (p \/ q) =
      nnfOfProp NEGATIVE p /\~ nnfOfProp NEGATIVE q
  (* P --> Q = ~~P \/ Q *)
  | nnfOfProp POSITIVE (p --> q) =
      nnfOfProp NEGATIVE p \/~ nnfOfProp POSITIVE q
  (* ~~(P --> Q) = P /\ ~Q *)
  | nnfOfProp NEGATIVE (p --> q) =
      nnfOfProp POSITIVE p /\~ nnfOfProp NEGATIVE q
(* どうせPOSITIVEの場合しか使わないのでshadowing *)
val nnfOfProp = nnfOfProp POSITIVE

(* cnfOfNnf p は否定標準形 p の連言標準形を求める *)
fun cnfOfNnf (NNFVAR (polar, x)) = [[(polar, x)]] : cnf
  | cnfOfNnf (p /\~ q) = cnfOfNnf p @ cnfOfNnf q
  | cnfOfNnf (p \/~ q) =
      let
        val p' = cnfOfNnf p
        val q' = cnfOfNnf q
      in
        List.concat
          (map (fn c =>
             map (fn d => c @ d) p') q')
      end

(* 与えられた連言標準形が恒真であるか判定する *)
val isCnfTautology =
  let
    (*
     * 与えられた節が恒真であるか判定する
     * uniqueSortにより重複は除去されており，負論理な変数が前に来ると期待される
     *)
    fun isClauseTautology [] = false
      | isClauseTautology (hd :: tl) =
          #1 (foldl (fn ((polar, x : string), (b, (polar', y))) =>
            (b orelse
              polar = POSITIVE andalso
              polar' = NEGATIVE andalso
              x = y, (polar, x))) (false, hd) tl)
  in
    (* 全ての節が恒真であるか判定 *)
    List.all (fn c =>
      isClauseTautology (ListMergeSort.uniqueSort (fn ((polar, x), (polar', y)) =>
        (* 負論理な変数が前に来て，重複が除去されるように辞書順を与えてやる *)
        case String.compare (x, y) of
             LESS => LESS
           | GREATER => GREATER
           | EQUAL =>
               case (polar, polar') of
                    (NEGATIVE, NEGATIVE) => EQUAL
                  | (NEGATIVE, POSITIVE) => LESS
                  | (POSITIVE, NEGATIVE) => GREATER
                  | (POSITIVE, POSITIVE) => EQUAL) c))
  end

(* 命題論理式を連言標準形に変換して恒真か判定する *)
val isTautology = isCnfTautology o cnfOfNnf o nnfOfProp;

isTautology (~~ (PVAR "P") \/ PVAR "P");
isTautology (((PVAR "P" --> PVAR "Q") --> PVAR "P") --> PVAR "P");
isTautology (~~ (PVAR "P") \/ ~~ (PVAR "Q") \/ ~~ (PVAR "R"));
isTautology (PVAR "P" \/ PVAR "Q" \/ PVAR "R");
