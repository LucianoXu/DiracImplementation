(* file: fotrs.lex *)
(* description: lexer generator for TRS format  *)
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
%%
%header (functor FoTrsLexFun (structure Tokens: FoTrs_TOKENS));
%s MAIN STRING;
alphanum = [a-zA-Z0-9];
symbol = [!|#*$%&+/;:<=>?@^_`{}~]|\-|\.|\]|\[|\\;
dash = "'";
idchar={alphanum}|{symbol}|{dash};
eol = ("\013\010"|"\010"|"\013");
ws = [\ \t\r];
%%
<INITIAL>{ws}*        => (lin:=1; eolpos:=0; YYBEGIN MAIN; continue());
<MAIN>{ws}+           => (lex ());
<MAIN>{eol}           => (lin:=(!lin)+1; eolpos:=yypos+size yytext; lex ());
<MAIN>"->"            => (col:=yypos-(!eolpos); Tokens.ARROW(!lin,!col));
<MAIN>"("             => (col:=yypos-(!eolpos); Tokens.LPAREN(!lin,!col));
<MAIN>")"             => (col:=yypos-(!eolpos); Tokens.RPAREN(!lin,!col));
<MAIN>","             => (col:=yypos-(!eolpos); Tokens.COMMA(!lin,!col));
<MAIN>"\""            => (col:=yypos-(!eolpos); addText yytext; YYBEGIN STRING; continue());
<MAIN>{idchar}+       => (col:=yypos-(!eolpos); 
                          case yytext of 
                               "VAR" => Tokens.VAR(!lin,!col)
                             | "SIG" => Tokens.SIG(!lin,!col) 
                             | "RULES" => Tokens.RULES(!lin,!col) 
                             | _ => Tokens.ID (yytext,!lin,!col)
                          );
<MAIN>.               => (col:=yypos-(!eolpos); error ("ignoring illegal character" ^ yytext,!lin,!col); lex());
<STRING>"\""          => (addText yytext; YYBEGIN MAIN; 
                          let val str = String.concat (List.rev (!text))
                              val _ = text := nil 
                          in Tokens.STR (str,!lin,!col)
                          end);
<STRING>{eol}         => (addText yytext; lin:=(!lin)+1; eolpos:=yypos+size yytext; lex ());
<STRING>[^"]+         => (addText yytext; lex());
