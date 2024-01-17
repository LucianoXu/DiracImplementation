functor MsTrsLexFun (structure Tokens: MsTrs_TOKENS)=
   struct
    structure UserDeclarations =
      struct
(* file: mstrs.lex *)
(* description: lexer generator for MSTRS format *)
(* author: Takahito Aoto *)

type pos = int;
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult  = (svalue,pos) token

val text = ref (nil: string list)
val addText = fn s => (text := s::(!text))
val lin = ref 1;
val col = ref 0; 
fun error (msg,line,col) = print ("[line "^Int.toString line^", char "^Int.toString col^"] "^msg^"\n");
val eof = fn _ => (if not (null (!text)) then error ("the file ends without closing dquote",!lin,!col) else ();
		    Tokens.EOF(!lin,!col))
val eolpos = ref 0;
end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [ 
 (0, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1, 
"\000\000\000\000\000\000\000\000\000\007\000\000\000\007\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (3, 
"\008\008\008\008\008\008\008\008\008\017\020\008\008\019\008\008\
\\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\
\\017\009\016\009\009\009\009\009\015\014\009\009\013\011\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\008\
\\008"
),
 (5, 
"\021\021\021\021\021\021\021\021\021\021\024\021\021\023\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\022\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021"
),
 (9, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\010\000\010\010\010\010\010\000\000\010\010\000\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\000\
\\000"
),
 (11, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\010\000\010\010\010\010\010\000\000\010\010\000\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\012\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\000\
\\000"
),
 (17, 
"\000\000\000\000\000\000\000\000\000\018\000\000\000\018\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\018\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (19, 
"\000\000\000\000\000\000\000\000\000\018\020\000\000\018\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\018\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (21, 
"\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\000\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021"
),
 (23, 
"\021\021\021\021\021\021\021\021\021\021\024\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\000\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021"
),
(0, "")]
fun f x = x 
val s = List.map f (List.rev (tl (List.rev s))) 
exception LexHackingError 
fun look ((j,x)::r, i: int) = if i = j then x else look(r, i) 
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)} 
in Vector.fromList(List.map g 
[{fin = [], trans = 0},
{fin = [(N 1)], trans = 1},
{fin = [(N 1)], trans = 1},
{fin = [], trans = 3},
{fin = [], trans = 3},
{fin = [], trans = 5},
{fin = [], trans = 5},
{fin = [(N 1)], trans = 1},
{fin = [(N 39)], trans = 0},
{fin = [(N 37),(N 39)], trans = 9},
{fin = [(N 37)], trans = 9},
{fin = [(N 37),(N 39)], trans = 11},
{fin = [(N 12),(N 37)], trans = 9},
{fin = [(N 18),(N 39)], trans = 0},
{fin = [(N 16),(N 39)], trans = 0},
{fin = [(N 14),(N 39)], trans = 0},
{fin = [(N 20),(N 39)], trans = 0},
{fin = [(N 4),(N 39)], trans = 17},
{fin = [(N 4)], trans = 17},
{fin = [(N 4),(N 9),(N 39)], trans = 19},
{fin = [(N 9)], trans = 0},
{fin = [(N 49)], trans = 21},
{fin = [(N 41)], trans = 0},
{fin = [(N 46),(N 49)], trans = 23},
{fin = [(N 46),(N 49)], trans = 21}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val INITIAL = STARTSTATE 1;
val MAIN = STARTSTATE 3;
val STRING = STARTSTATE 5;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

fun makeLexer yyinput =
let	val yygone0=1
	val yyb = ref "\n" 		(* buffer *)
	val yybl = ref 1		(*buffer length *)
	val yybufpos = ref 1		(* location of next character to use *)
	val yygone = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex () : Internal.result =
let fun continue() = lex() in
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0) =
	let fun action (i,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let fun yymktext() = String.substring(!yyb,i0,i-i0)
			     val yypos = i0+ !yygone
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  1 => (lin:=1; eolpos:=0; YYBEGIN MAIN; continue())
| 12 => (col:=yypos-(!eolpos); Tokens.ARROW(!lin,!col))
| 14 => (col:=yypos-(!eolpos); Tokens.LPAREN(!lin,!col))
| 16 => (col:=yypos-(!eolpos); Tokens.RPAREN(!lin,!col))
| 18 => (col:=yypos-(!eolpos); Tokens.COMMA(!lin,!col))
| 20 => let val yytext=yymktext() in col:=yypos-(!eolpos); addText yytext; YYBEGIN STRING; continue() end
| 37 => let val yytext=yymktext() in col:=yypos-(!eolpos); 
                          case yytext of 
                               "SIG" => Tokens.SIG(!lin,!col)
                             | "RULES" => Tokens.RULES(!lin,!col) 
                             | _ => Tokens.ID (yytext,!lin,!col)
                           end
| 39 => let val yytext=yymktext() in col:=yypos-(!eolpos); error ("ignoring illegal character" ^ yytext,!lin,!col); lex() end
| 4 => (lex ())
| 41 => let val yytext=yymktext() in addText yytext; YYBEGIN MAIN; 
                          let val str = String.concat (List.rev (!text))
                              val _ = text := nil 
                          in Tokens.STR (str,!lin,!col)
                          end end
| 46 => let val yytext=yymktext() in addText yytext; lin:=(!lin)+1; eolpos:=yypos+size yytext; lex () end
| 49 => let val yytext=yymktext() in addText yytext; lex() end
| 9 => let val yytext=yymktext() in lin:=(!lin)+1; eolpos:=yypos+size yytext; lex () end
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Unsafe.Vector.sub(Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (String.size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof ()
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := String.substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := String.size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord(Unsafe.CharVector.sub(!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord(Unsafe.CharVector.sub(trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if String.substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
end
  in lex
  end
end
