(* file: main.sml *)
(* description: checker of many-sorted TRS in many-sorted TPDB format *)
(* author: Takahito Aoto *)

signature MAIN = 
sig
    val toolname: string
    val version: string
    val helpMsg: string
    val compile: string -> ((string * (string list * string)) list * (Term.term * Term.term) list)
    val main: string * string list -> OS.Process.status
end

structure Main = 
struct

local 
    structure L = List
    structure U = Util
in

val toolname = "mstrcsk"
val version = "0.03"
val helpMsg = 
    toolname ^ " v" ^ version ^ "\n"
    ^ "Usage: sml @SMLload=" ^ toolname ^ ".x86-linux [-t] [-tt] [-r] filename\n"

exception Error (* fatal error *)


local 
structure MsTrsLrVals = MsTrsLrValsFun (structure Token = LrParser.Token);
structure MsTrsLex = MsTrsLexFun (structure Tokens = MsTrsLrVals.Tokens);
structure MsTrsParser = Join (structure ParserData = MsTrsLrVals.ParserData;
                             structure Lex = MsTrsLex;
                             structure LrParser = LrParser);
in
fun compileMsTrs filename =
    let val istream = TextIO.openIn filename
	val lexer = MsTrsParser.makeLexer (fn n=>TextIO.inputN (istream, n));
	fun error (msg,line,col) = (print ("Error: " ^ msg ^ " at line " ^ (Int.toString line)
					   ^ ", char "^ Int.toString col ^"\n"); raise Error)
    in #1 (MsTrsParser.parse (15, lexer, error, ()))
    end
end

local 
structure FoTrsLrVals = FoTrsLrValsFun (structure Token = LrParser.Token);
structure FoTrsLex = FoTrsLexFun (structure Tokens = FoTrsLrVals.Tokens);
structure FoTrsParser = Join (structure ParserData = FoTrsLrVals.ParserData;
                             structure Lex = FoTrsLex;
                             structure LrParser = LrParser);
in
fun compileFoTrs filename =
    let val istream = TextIO.openIn filename
	val lexer = FoTrsParser.makeLexer (fn n=>TextIO.inputN (istream, n));
	fun error (msg,line,col) = (print ("Error: " ^ msg ^ " at line " ^ (Int.toString line)
					   ^ ", char "^ Int.toString col ^"\n"); raise Error)
    in #1 (FoTrsParser.parse (15, lexer, error, ()))
    end
end

fun checkArityDecl (syms,vars,arity) =
    let val funs = L.map (fn (f,ar) => f) arity
	val _ = case U.duplicatingElem funs of
		    SOME f => (print ("Error: duplicated records in SIG at function " ^ f ^ "\n"); raise Error)
		  | NONE => ()
	val vandf = vars @ funs
	val _ = case L.find (fn x => U.member x funs) vars of
		    SOME x => (print ("Error: vars and funs are not disjoint " ^ x ^ "\n"); raise Error)
		  | NONE => ()
	val _ = case L.find (fn s => not (U.member s vandf)) syms of
		    SOME s => (print ("Error: undeclared symbol " ^ s ^ "\n"); raise Error)
		  | NONE => ()
    in ()
    end

fun replaceVarByFuns funs (l,r) = (Term.replaceVarByFuns funs l, Term.replaceVarByFuns funs r)
fun replaceVarByVars vars (l,r) = (Term.replaceVarByVars vars l, Term.replaceVarByVars vars r)

fun getRulesByFuns funs rules = L.map (replaceVarByFuns funs) rules
fun getRulesByVars vars rules = L.map (replaceVarByVars vars) rules

fun main (name, args0) =
    let val (argT,args1) = L.partition (fn s => s = "-t") args0
	val optT = not (null argT)
	val (argT2,args2) = L.partition (fn s => s = "-tt") args1
	val optT2 = not (null argT2)
	val (argR,args) = L.partition (fn s => s = "-r") args2
	val optR = not (null argR)

	val option = case (optT,optT2,optR) of
			 (false,false,false) => Term.CheckUni
		       | (true,false,false) => Term.TransUni
		       | (false,true,false) => Term.TransAll
		       | (false,false,true) => Term.TransBack
		       | _ => (print ("Error: -t, -tt and -r can not be specified together\n");
			       raise Error)
    in
	if null args orelse length args > 1
	then (print helpMsg; OS.Process.failure)
	else let val filename = hd args
	     in if option = Term.TransBack
		then let val (vars,arity,prerules) = compileFoTrs filename
			 val _ = case U.duplicatingElem vars of
				     SOME x => (print ("Error: duplicated records in VAR at variable " ^ x ^ "\n"); raise Error)
				   | NONE => ()
			 val syms = L.foldr (fn ((l,r),xs) => (Term.symbols l) @ (Term.symbols r) @ xs) [] prerules
			 val _ = if null arity then () else checkArityDecl (syms,vars,arity)
         
			 val rules = getRulesByVars vars prerules
			 val _ = Term.checkRules rules

			 val terms = U.mapAppend (fn (l,r)=>[l,r]) rules
			 val _ = if null arity then () else Term.checkArity arity terms
			 val properArity = if null arity then Term.getArity [] terms
					   else arity

			 val types = L.map (fn (f,n) => (f,(L.tabulate(n,fn x=>"o"),"o"))) properArity
			 val _ = Term.prMsTrs types rules

		     in OS.Process.success
		     end
		else let val (types,prerules) = compileMsTrs filename
			 val funs = L.map (fn (f,ty) => f) types
			 val _ = case U.duplicatingElem funs of
				     SOME x => (print ("Error: duplicated records in SIG at function " ^ x ^ "\n"); raise Error)
				   | NONE => ()

			 val rules = getRulesByFuns funs prerules
			 val _ = Term.checkRules rules
			 val _ = if L.all (Term.checkSort types) rules
				 then ()
				 else (print ("Error: variable l.h.s.? \n"); raise Error)  (* should not come here *)

			 val _ = Term.checkUnisort option types rules

		     in OS.Process.success
		     end 
	     end
    end
    handle Error => OS.Process.failure
	 | Term.Error => OS.Process.failure
	     

end (* of local *)
end (* of struct *)
