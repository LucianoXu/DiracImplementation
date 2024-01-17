functor FoTrsLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : FoTrs_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(* file: fotrs.yacc *)
(* description: parser generator for TRS format *)
(* author: Takahito Aoto *)

local 
    structure U = Util
in
open Term;
type vars = string list
type funs = (string * int) list
type rules = (term * term) list
datatype decl = VAR of vars | SIG of funs | RULES of rules
type result = vars * funs * rules

exception Error

(* それぞれのパートの union をとる *)
fun getCategory f xss = let val yss = List.mapPartial f xss in U.mapAppend (fn x=>x) yss end
val getVAR = getCategory (fn top => case top of VAR xs => SOME xs | _ => NONE) 
val getSIG = getCategory (fn top => case top of SIG xs => SOME xs | _ => NONE) 
val getRULES = getCategory (fn top => case top of RULES xs => SOME xs | _ => NONE)

fun getDecl decls = (getVAR decls, getSIG decls, getRULES decls)

end 
(* ユーザ定義部 *)

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\008\000\007\000\007\000\008\000\006\000\009\000\005\000\000\000\
\\001\000\001\000\012\000\000\000\
\\001\000\001\000\012\000\004\000\044\000\000\000\
\\001\000\001\000\034\000\000\000\
\\001\000\001\000\046\000\000\000\
\\001\000\004\000\030\000\000\000\
\\001\000\004\000\033\000\000\000\
\\001\000\004\000\035\000\000\000\
\\001\000\004\000\038\000\000\000\
\\001\000\004\000\049\000\000\000\
\\001\000\004\000\051\000\000\000\
\\001\000\004\000\052\000\000\000\
\\001\000\006\000\028\000\000\000\
\\001\000\010\000\000\000\000\000\
\\055\000\000\000\
\\056\000\000\000\
\\057\000\000\000\
\\058\000\000\000\
\\059\000\000\000\
\\060\000\003\000\004\000\000\000\
\\061\000\000\000\
\\062\000\003\000\015\000\000\000\
\\063\000\000\000\
\\064\000\000\000\
\\065\000\001\000\017\000\000\000\
\\066\000\000\000\
\\067\000\001\000\012\000\000\000\
\\068\000\000\000\
\\069\000\003\000\031\000\000\000\
\\070\000\000\000\
\\071\000\000\000\
\\072\000\000\000\
\\073\000\005\000\050\000\000\000\
\\074\000\000\000\
\\075\000\001\000\027\000\002\000\026\000\003\000\025\000\005\000\024\000\
\\006\000\023\000\007\000\022\000\008\000\021\000\009\000\020\000\000\000\
\\076\000\000\000\
\\077\000\000\000\
\\078\000\000\000\
\\079\000\000\000\
\\080\000\000\000\
\\081\000\000\000\
\\082\000\000\000\
\\083\000\000\000\
\"
val actionRowNumbers =
"\019\000\014\000\000\000\026\000\
\\021\000\024\000\034\000\012\000\
\\026\000\005\000\028\000\021\000\
\\006\000\003\000\007\000\024\000\
\\034\000\008\000\042\000\040\000\
\\041\000\038\000\039\000\034\000\
\\036\000\035\000\001\000\025\000\
\\019\000\002\000\020\000\019\000\
\\004\000\019\000\023\000\033\000\
\\019\000\009\000\027\000\017\000\
\\032\000\010\000\029\000\016\000\
\\011\000\015\000\018\000\037\000\
\\001\000\030\000\022\000\031\000\
\\013\000"
val gotoT =
"\
\\001\000\052\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\006\000\009\000\007\000\008\000\009\000\007\000\000\000\
\\003\000\012\000\004\000\011\000\000\000\
\\005\000\014\000\000\000\
\\010\000\017\000\011\000\016\000\000\000\
\\000\000\
\\006\000\027\000\007\000\008\000\009\000\007\000\000\000\
\\000\000\
\\000\000\
\\003\000\030\000\004\000\011\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\034\000\000\000\
\\010\000\035\000\011\000\016\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\037\000\011\000\016\000\000\000\
\\000\000\
\\000\000\
\\009\000\038\000\000\000\
\\000\000\
\\002\000\039\000\000\000\
\\008\000\041\000\009\000\040\000\000\000\
\\000\000\
\\002\000\043\000\000\000\
\\000\000\
\\002\000\045\000\000\000\
\\000\000\
\\000\000\
\\002\000\046\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\051\000\009\000\040\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 53
val numrules = 29
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | STR of unit ->  (string) | ID of unit ->  (string)
 | XanyX of unit ->  (unit) | XanylistX of unit ->  (unit)
 | XtermX of unit ->  (term) | XtermlistX of unit ->  (term list)
 | XruleX of unit ->  (term*term)
 | XrulelistX of unit ->  ( ( term * term )  list)
 | XidlistX of unit ->  (string list) | XfunX of unit ->  (string*int)
 | XfunlistX of unit ->  (funs) | XspecX of unit ->  (decl list)
 | XstartX of unit ->  (result)
end
type svalue = MlyValue.svalue
type result = result
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 9) => true | _ => false
val showTerminal =
fn (T 0) => "ID"
  | (T 1) => "STR"
  | (T 2) => "LPAREN"
  | (T 3) => "RPAREN"
  | (T 4) => "COMMA"
  | (T 5) => "ARROW"
  | (T 6) => "VAR"
  | (T 7) => "SIG"
  | (T 8) => "RULES"
  | (T 9) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 
2)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.XspecX XspecX1, XspecX1left, XspecX1right))
 :: rest671)) => let val  result = MlyValue.XstartX (fn _ => let val 
 (XspecX as XspecX1) = XspecX1 ()
 in (getDecl XspecX)
end)
 in ( LrTable.NT 0, ( result, XspecX1left, XspecX1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.XspecX XspecX1, _, XspecX1right)) :: _ :: (
 _, ( MlyValue.XidlistX XidlistX1, _, _)) :: _ :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.XspecX (fn
 _ => let val  (XidlistX as XidlistX1) = XidlistX1 ()
 val  (XspecX as XspecX1) = XspecX1 ()
 in (VAR XidlistX::XspecX)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, XspecX1right), rest671)
end
|  ( 2, ( ( _, ( MlyValue.XspecX XspecX1, _, XspecX1right)) :: _ :: (
 _, ( MlyValue.XfunlistX XfunlistX1, _, _)) :: _ :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.XspecX (fn
 _ => let val  (XfunlistX as XfunlistX1) = XfunlistX1 ()
 val  (XspecX as XspecX1) = XspecX1 ()
 in (SIG XfunlistX::XspecX)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, XspecX1right), rest671)
end
|  ( 3, ( ( _, ( MlyValue.XspecX XspecX1, _, XspecX1right)) :: _ :: (
 _, ( MlyValue.XrulelistX XrulelistX1, _, _)) :: _ :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.XspecX (fn
 _ => let val  (XrulelistX as XrulelistX1) = XrulelistX1 ()
 val  (XspecX as XspecX1) = XspecX1 ()
 in (RULES XrulelistX::XspecX)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, XspecX1right), rest671)
end
|  ( 4, ( ( _, ( MlyValue.XspecX XspecX1, _, XspecX1right)) :: _ :: (
 _, ( MlyValue.XanylistX XanylistX1, _, _)) :: ( _, ( MlyValue.ID ID1,
 _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.XspecX (fn _ => let val  ID1 = ID1 ()
 val  XanylistX1 = XanylistX1 ()
 val  (XspecX as XspecX1) = XspecX1 ()
 in (XspecX)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, XspecX1right), rest671)
end
|  ( 5, ( rest671)) => let val  result = MlyValue.XspecX (fn _ => ([])
)
 in ( LrTable.NT 1, ( result, defaultPos, defaultPos), rest671)
end
|  ( 6, ( ( _, ( MlyValue.XfunlistX XfunlistX1, _, XfunlistX1right))
 :: ( _, ( MlyValue.XfunX XfunX1, XfunX1left, _)) :: rest671)) => let
 val  result = MlyValue.XfunlistX (fn _ => let val  (XfunX as XfunX1)
 = XfunX1 ()
 val  (XfunlistX as XfunlistX1) = XfunlistX1 ()
 in (XfunX::XfunlistX)
end)
 in ( LrTable.NT 2, ( result, XfunX1left, XfunlistX1right), rest671)

end
|  ( 7, ( rest671)) => let val  result = MlyValue.XfunlistX (fn _ => (
[]))
 in ( LrTable.NT 2, ( result, defaultPos, defaultPos), rest671)
end
|  ( 8, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.ID ID2, _, _)
) :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: 
rest671)) => let val  result = MlyValue.XfunX (fn _ => let val  ID1 = 
ID1 ()
 val  ID2 = ID2 ()
 in (
(ID1, case Int.fromString ID2 of SOME n => n 
					     | NONE => (print ("Error: integer expected " ^  ID2 ^ "\n"); raise Error))
)
end)
 in ( LrTable.NT 3, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.XidlistX XidlistX1, _, XidlistX1right)) :: (
 _, ( MlyValue.ID ID1, ID1left, _)) :: rest671)) => let val  result = 
MlyValue.XidlistX (fn _ => let val  (ID as ID1) = ID1 ()
 val  (XidlistX as XidlistX1) = XidlistX1 ()
 in (ID::XidlistX)
end)
 in ( LrTable.NT 4, ( result, ID1left, XidlistX1right), rest671)
end
|  ( 10, ( rest671)) => let val  result = MlyValue.XidlistX (fn _ => (
[]))
 in ( LrTable.NT 4, ( result, defaultPos, defaultPos), rest671)
end
|  ( 11, ( ( _, ( MlyValue.XrulelistX XrulelistX1, _, XrulelistX1right
)) :: ( _, ( MlyValue.XruleX XruleX1, XruleX1left, _)) :: rest671)) =>
 let val  result = MlyValue.XrulelistX (fn _ => let val  (XruleX as 
XruleX1) = XruleX1 ()
 val  (XrulelistX as XrulelistX1) = XrulelistX1 ()
 in (XruleX::XrulelistX)
end)
 in ( LrTable.NT 5, ( result, XruleX1left, XrulelistX1right), rest671)

end
|  ( 12, ( rest671)) => let val  result = MlyValue.XrulelistX (fn _ =>
 ([]))
 in ( LrTable.NT 5, ( result, defaultPos, defaultPos), rest671)
end
|  ( 13, ( ( _, ( MlyValue.XtermX XtermX2, _, XtermX2right)) :: _ :: (
 _, ( MlyValue.XtermX XtermX1, XtermX1left, _)) :: rest671)) => let
 val  result = MlyValue.XruleX (fn _ => let val  XtermX1 = XtermX1 ()
 val  XtermX2 = XtermX2 ()
 in ((XtermX1,XtermX2))
end)
 in ( LrTable.NT 6, ( result, XtermX1left, XtermX2right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.ID ID1, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.XtermX (fn _ => let val  (ID as ID1) = ID1
 ()
 in (Fun (ID,[]))
end)
 in ( LrTable.NT 8, ( result, ID1left, ID1right), rest671)
end
|  ( 15, ( ( _, ( _, _, RPAREN1right)) :: _ :: ( _, ( MlyValue.ID ID1,
 ID1left, _)) :: rest671)) => let val  result = MlyValue.XtermX (fn _
 => let val  (ID as ID1) = ID1 ()
 in (Fun (ID,[]))
end)
 in ( LrTable.NT 8, ( result, ID1left, RPAREN1right), rest671)
end
|  ( 16, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.XtermlistX 
XtermlistX1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, ID1left, _)) :: 
rest671)) => let val  result = MlyValue.XtermX (fn _ => let val  (ID
 as ID1) = ID1 ()
 val  (XtermlistX as XtermlistX1) = XtermlistX1 ()
 in (Fun (ID,XtermlistX))
end)
 in ( LrTable.NT 8, ( result, ID1left, RPAREN1right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.XtermlistX XtermlistX1, _, XtermlistX1right
)) :: _ :: ( _, ( MlyValue.XtermX XtermX1, XtermX1left, _)) :: rest671
)) => let val  result = MlyValue.XtermlistX (fn _ => let val  (XtermX
 as XtermX1) = XtermX1 ()
 val  (XtermlistX as XtermlistX1) = XtermlistX1 ()
 in (XtermX::XtermlistX)
end)
 in ( LrTable.NT 7, ( result, XtermX1left, XtermlistX1right), rest671)

end
|  ( 18, ( ( _, ( MlyValue.XtermX XtermX1, XtermX1left, XtermX1right))
 :: rest671)) => let val  result = MlyValue.XtermlistX (fn _ => let
 val  (XtermX as XtermX1) = XtermX1 ()
 in ([XtermX])
end)
 in ( LrTable.NT 7, ( result, XtermX1left, XtermX1right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.XanylistX XanylistX1, _, XanylistX1right))
 :: ( _, ( MlyValue.XanyX XanyX1, XanyX1left, _)) :: rest671)) => let
 val  result = MlyValue.XanylistX (fn _ => let val  XanyX1 = XanyX1 ()
 val  XanylistX1 = XanylistX1 ()
 in ()
end)
 in ( LrTable.NT 9, ( result, XanyX1left, XanylistX1right), rest671)

end
|  ( 20, ( rest671)) => let val  result = MlyValue.XanylistX (fn _ =>
 ())
 in ( LrTable.NT 9, ( result, defaultPos, defaultPos), rest671)
end
|  ( 21, ( ( _, ( MlyValue.ID ID1, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.XanyX (fn _ => let val  ID1 = ID1 ()
 in ()
end)
 in ( LrTable.NT 10, ( result, ID1left, ID1right), rest671)
end
|  ( 22, ( ( _, ( MlyValue.STR STR1, STR1left, STR1right)) :: rest671)
) => let val  result = MlyValue.XanyX (fn _ => let val  STR1 = STR1 ()
 in ()
end)
 in ( LrTable.NT 10, ( result, STR1left, STR1right), rest671)
end
|  ( 23, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.XanylistX 
XanylistX1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.XanyX (fn _ => let val  XanylistX1 = 
XanylistX1 ()
 in ()
end)
 in ( LrTable.NT 10, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 24, ( ( _, ( _, ARROW1left, ARROW1right)) :: rest671)) => let
 val  result = MlyValue.XanyX (fn _ => ())
 in ( LrTable.NT 10, ( result, ARROW1left, ARROW1right), rest671)
end
|  ( 25, ( ( _, ( _, COMMA1left, COMMA1right)) :: rest671)) => let
 val  result = MlyValue.XanyX (fn _ => ())
 in ( LrTable.NT 10, ( result, COMMA1left, COMMA1right), rest671)
end
|  ( 26, ( ( _, ( _, SIG1left, SIG1right)) :: rest671)) => let val  
result = MlyValue.XanyX (fn _ => ())
 in ( LrTable.NT 10, ( result, SIG1left, SIG1right), rest671)
end
|  ( 27, ( ( _, ( _, VAR1left, VAR1right)) :: rest671)) => let val  
result = MlyValue.XanyX (fn _ => ())
 in ( LrTable.NT 10, ( result, VAR1left, VAR1right), rest671)
end
|  ( 28, ( ( _, ( _, RULES1left, RULES1right)) :: rest671)) => let
 val  result = MlyValue.XanyX (fn _ => ())
 in ( LrTable.NT 10, ( result, RULES1left, RULES1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.XstartX x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : FoTrs_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun STR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.STR (fn () => i),p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun VAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun SIG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun RULES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
end
end
