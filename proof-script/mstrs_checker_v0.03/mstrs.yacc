(* file: mstrs.yacc *)
(* description: parser generator for MSTRS format *)
(* author: Takahito Aoto *)

local 
    structure U = Util
in
open Term;
type vars = string list
type funs = (string * (string list * string)) list
type rules = (term * term) list
datatype tpdb_decl = SIG of funs | RULES of rules
type tpdb_result = funs * rules

exception MsTrsError of string

(* それぞれのパートの union をとる *)
fun getCategory f xss = let val yss = List.mapPartial f xss in U.mapAppend (fn x=>x) yss end
val getSIG = getCategory (fn top => case top of SIG xs => SOME xs | _ => NONE) 
val getRULES = getCategory (fn top => case top of RULES xs => SOME xs | _ => NONE)

fun getDecl decls = (getSIG decls, getRULES decls)

end 
(* ユーザ定義部 *)
%%
%name		MsTrs
%term           ID of string
              | STR of string
              | LPAREN
              | RPAREN
              | COMMA
              | ARROW
              | SIG
              | RULES
              | EOF 

%nonterm	XstartX of tpdb_result
              | XspecX of tpdb_decl list
              | XfunlistX of funs
              | XfunX of  string * (string list * string)
              | XsortX of string list * string
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
XspecX:       LPAREN SIG XfunlistX RPAREN XspecX               (SIG XfunlistX::XspecX)
            | LPAREN RULES XrulelistX RPAREN XspecX            (RULES XrulelistX::XspecX)
            | LPAREN ID XanylistX RPAREN XspecX                    (XspecX)
            |                              ([])
XfunlistX:    XfunX XfunlistX              (XfunX::XfunlistX)
            |                              ([])
XfunX:        LPAREN ID XsortX RPAREN      ((ID, XsortX))
XsortX:       XidlistX ARROW ID            ((XidlistX,ID))
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
            | RULES                        ()
