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
%%
%name		FoTrs
%term           ID of string
              | STR of string
              | LPAREN
              | RPAREN
              | COMMA
              | ARROW
              | VAR
              | SIG
              | RULES
              | EOF 

%nonterm	XstartX of result
              | XspecX of decl list
              | XfunlistX of funs
              | XfunX of  string * int
              | XidlistX of string list
              | XrulelistX of (term * term) list
              | XruleX of term * term 
              | XtermlistX of term list
              | XtermX of term
              | XanylistX of unit
              | XanyX of unit
%pos	   	int
%eop		EOF
%noshift	EOF

%%
XstartX:      XspecX                       (getDecl XspecX)
XspecX:       LPAREN VAR XidlistX RPAREN XspecX                (VAR XidlistX::XspecX)
            | LPAREN SIG XfunlistX RPAREN XspecX               (SIG XfunlistX::XspecX)
            | LPAREN RULES XrulelistX RPAREN XspecX            (RULES XrulelistX::XspecX)
            | LPAREN ID XanylistX RPAREN XspecX                (XspecX)
            |                              ([])
XfunlistX:    XfunX XfunlistX              (XfunX::XfunlistX)
            |                              ([])
XfunX:        LPAREN ID ID RPAREN          ((ID1, case Int.fromString ID2 of SOME n => n 
					     | NONE => (print ("Error: integer expected " ^  ID2 ^ "\n"); raise Error)))
XidlistX:     ID XidlistX                  (ID::XidlistX)
            |                              ([])
XrulelistX:    XruleX  XrulelistX          (XruleX::XrulelistX)
            |                              ([])
XruleX:       XtermX ARROW XtermX          ((XtermX1,XtermX2))
XtermX:       ID                           (Fun (ID,[]))
            | ID LPAREN RPAREN             (Fun (ID,[]))
            | ID LPAREN XtermlistX RPAREN  (Fun (ID,XtermlistX))
XtermlistX:   XtermX COMMA XtermlistX      (XtermX::XtermlistX)
            | XtermX 			   ([XtermX])
XanylistX:    XanyX XanylistX              ()
            |                              ()
XanyX:        ID                           ()
            | STR                          ()
            | LPAREN XanylistX RPAREN      ()
            | ARROW                        ()
            | COMMA                        ()
            | SIG                          ()
            | VAR                          ()
            | RULES                        ()
