(* file: term.sml *)
(* description: first-order terms *)
(* author: Takahito Aoto *)

signature TERM = 
sig 
    datatype term = Var of string | Fun of string * term list
    val toString : term -> string
    val prRule: term * term -> string
    val prRules: (term * term) list -> string

    val symbols : term -> string list
    val replaceVarByFuns: string list -> term -> term
    val replaceVarByVars: string list -> term -> term

    val checkRules: (term * term) list -> unit
    val checkSort : (string * (string list * string)) list -> term * term -> bool

    val getArity: (string * int) list -> term list -> (string * int) list
    val checkArity: (string * int) list -> term list -> unit


    val prFoTrs: (string * int) list -> (term * term) list -> unit
    val prMsTrs: (string * (string list * string)) list -> (term * term) list -> unit

    datatype option = CheckUni | TransUni | TransAll | TransBack
    val checkUnisort: option -> (string * (string list * string)) list -> (term * term) list -> unit
    exception Error
end

structure Term : TERM =
struct
local 
    structure L = List
    structure LP = ListPair
    structure U = Util
in

datatype term = Var of string | Fun of string * term list

fun toString (Var x) = x
  | toString (Fun (f,[])) = f
  | toString (Fun (f,ts)) =  f ^ (Util.toStringCommaRound toString ts)
						       
fun prRule (l,r) = (toString l) ^ " -> " ^ (toString r)
fun prRules rs = U.toStringCommaLnSquare prRule rs

exception Error

(*** replacing variables  ***)

fun symbols (Var x) = [x]
  | symbols (Fun (f,ts)) = f::(U.mapAppend symbols ts)

fun replaceVarByFuns funs (Var x) = Var x
  | replaceVarByFuns funs (Fun (f,ts)) = 
    if U.member f funs
    then let val ts2 = L.map (replaceVarByFuns funs) ts
	 in Fun (f,ts2)
	 end
    else if null ts 
    then Var f
    else (print ("Error: sort unspecified for function " ^ f ^ "\n"); raise Error)

fun replaceVarByVars vars (Var x) = Var x
  | replaceVarByVars vars (Fun (f,ts)) = 
    if U.member f vars
    then if null ts 
	 then Var f
	 else (print ("Error: arguments for a variable " ^ f^ "\n"); raise Error)
    else let val ts2 = L.map (replaceVarByVars vars) ts
	 in Fun (f,ts2)
	 end

(*** variable conditions ***)

fun vars (Var x) = [x]
  | vars (Fun (f,ts)) = U.mapAppend vars ts

fun isVar (Var _) = true
  | isVar (Fun _) = false

fun checkVarCond1 (Var _,r) = (print "Error: variable lhs\n"; raise Error)
 |  checkVarCond1 (Fun _,r) = true

fun checkVarCond2 (l,r) = 
    U.isSubseteq (vars r, vars l)
    orelse (print "Error: an extra variable in rhs\n"; raise Error)

fun checkRule (l,r) =
    let val _ = checkVarCond1 (l,r)
	val _ = checkVarCond2 (l,r)
    in ()
    end

fun checkRules rs = L.app checkRule rs 

(*** well-sortedness check ***)

fun decompose types [] = []
  | decompose types ((Var x,ty)::rest) = (x,ty) :: decompose types rest
  | decompose types ((t as Fun (f,ts), ty)::rest) =
    case U.find f types of 
	NONE => (print ("Error: sort unspecified for function symbol " ^ f ^ "\n"); raise Error)
      | SOME (args,ty2) => if ty = ty2 andalso length args = length ts
			   then decompose types (LP.zip (ts,args) @ rest)
			   else (print ("Error: ill-sorted\n"); raise Error)

fun checkAssig [] = true
 |  checkAssig ((x,ty)::rest) = 
    if L.exists (fn (x',ty') => x' = x andalso ty <> ty') rest
    then (print ("Error: ill-sorted\n"); raise Error)
    else checkAssig rest

fun checkSortCnstr types cnstr = checkAssig (decompose types cnstr)

fun checkSort types (Var _,r) = false (* not come here *)
  | checkSort types (t as Fun (f,ts),r) = 
    let val cnstr = case U.find f types of 
			NONE => (print ("Error: sort unspecified for function symbol" ^ f^ "\n"); raise Error)
		      | SOME (args,ty) => if length args = length ts
					  then LP.zip (ts,args) @ [(r,ty)]
					  else (print ("Error: ill-sorted\n"); raise Error)
    in checkSortCnstr types cnstr
    end

(*** arity check ***)

fun getArity arity [] = rev arity
  | getArity arity ((Var x)::ts) =  getArity arity ts
  | getArity arity ((Fun (f,args))::ts) = 
		    case U.find f arity of 
			NONE => getArity ((f,L.length args)::arity) (args @ ts)
		      | SOME n => if length args = n
				  then getArity arity (args @ ts)
				  else (print ("Error: number of arguments not fixed for " ^ f ^ "\n"); raise Error)

(* for extended case *)
fun checkArity arity [] = ()
  | checkArity arity ((Var _) ::ts) =  checkArity arity ts
  | checkArity arity ((Fun (f,args)) ::ts) = 
			    case U.find f arity of 
				NONE => (print ("Error: no arity declaration for " ^ f ^ "\n"); raise Error)
			      | SOME n => if length args = n
					  then checkArity arity (args @ ts)
					  else (print ("Error: number of arguments not fixed for " ^ f ^ "\n"); raise Error)


(*** printing ***)

fun prFoTrs arity rs = 
    let val funs = L.map (fn (f,ar) => f) arity
	val terms = U.mapAppend (fn (l,r) => [l,r]) rs
	fun getSyms [] syms = L.rev syms
	  | getSyms (t::ts) syms = case t of
				       Var x => getSyms ts (U.union [x] syms)
				     | Fun (f,us) => getSyms (us@ts) (U.union [f] syms)
	val syms = getSyms terms []

	val vars = L.filter (fn x=> not (U.member x funs)) syms
	val _ = print ("(VAR " ^ (U.toStringSpaceEmpty (fn x=>x) vars) ^ ")\n")

	fun prFunArity (f,ar) = "(" ^ f ^ " " ^ (Int.toString ar) ^")"
	val _ = if L.exists (fn x => not (U.member x syms)) funs
		then print ("(SIG " ^ (U.toStringSpaceEmpty prFunArity arity) ^ ")\n")
		else ()

	val _ = print "(RULES\n"
	val _ = L.app (fn lr => print ("   " ^ (prRule lr) ^ "\n")) rs
	val _ = print ")\n"
    in ()
    end

fun prMsTrs types rs = 
    let 
	val maxlen = L.foldr (fn ((f,ty),n) => Int.max(n,String.size f)) 0 types
	fun addSpace fname = let val len = String.size fname
			     in fname ^ (String.concat (L.tabulate ((maxlen + 3) - len,fn x => " ")))
			     end
	fun prFunSort (fname,(args,ty)) = "   (" ^ (addSpace fname) 
					  ^ (U.toStringSpaceEmpty (fn x=>x) args) 
					  ^ (if null args then "" else " ")
					  ^ "-> "  ^ ty ^ ")\n"

	val _ = print "(SIG\n"
	val _ = List.app (fn decl => print (prFunSort decl)) types
	val _ = print ")\n"


	val _ = print "(RULES\n"
	val _ = L.app (fn lr => print ("   " ^ (prRule lr) ^ "\n")) rs
	val _ = print ")\n"
    in ()
    end

datatype option = CheckUni | TransUni | TransAll | TransBack

fun checkUnisort optTrans types rs =
    let val sorts = U.mapAppend (fn (fname,(args,ty)) => ty::args) types
	val isUnisort = case sorts of [] => false | (s::ss) => L.all (fn u=>s=u) ss
	val arity = L.map (fn (f,(args,ty)) => (f, L.length args)) types
    in case optTrans of
	   CheckUni => if isUnisort then (print ("Error: there is only one sort\n"); raise Error) else ()
	 | TransUni => if isUnisort then prFoTrs arity rs else prMsTrs types rs
	 | TransAll => prFoTrs arity rs
	 | _ => (print ("Error: unkown error in checkUnisort\n"); raise Error)  (* should not come here *)
    end



end (* of local *)
end
