(* file: util.sml *)
(* description: utility functions *)
(* author: Takahito Aoto *)

signature UTIL = 
sig 
    val member: ''a  -> ''a list -> bool
    val isSubseteq: ''a  list *  ''a list -> bool
    val find: ''a -> (''a * 'b) list -> 'b option
    val mapAppend: ('a -> 'b list) -> 'a list -> 'b list
    val duplicatingElem: ''a list -> ''a option
    val elimDuplication: ''a list -> ''a list
    val union: ''a list -> ''a list -> ''a list
    val takeUntilWithRest : ('a -> bool) -> 'a list -> 'a list * 'a list
    val toStringCommaRound: ('a -> string) -> 'a list -> string
    val toStringCommaLnSquare: ('a -> string) -> 'a list -> string
    val toStringSpaceEmpty: ('a -> string) -> 'a list -> string
end

structure Util : UTIL =
struct 

local 
    structure L = List
in

fun member x ys = List.exists (fn y => x = y) ys
fun isSubseteq (xs,ys) = List.all (fn x => member x ys) xs
fun find x [] = NONE
  | find x ((k,v)::ys) = if x = k then SOME v else find x ys

fun mapAppend f [] =  []
  | mapAppend f (x::xs) =  (f x) @  (mapAppend f xs)
fun duplicatingElem [] = NONE
  | duplicatingElem (x::xs) = if member x xs then SOME x else duplicatingElem xs

fun union [] ys = ys
  | union (x::xs) ys = if member x ys
		       then union xs ys
		       else union xs (x::ys)

fun elimDuplication xs = 
    let fun elimDup [] ans = ans
	  | elimDup (x::xs) ans = if member x ans 
				  then elimDup xs ans
				  else elimDup xs (x::ans)
    in elimDup xs []
    end

fun toStringBuilt prElm (start,sep,stop) xs =
    let fun toStringSub [] = ""
	  | toStringSub [x] = (prElm x)
	  | toStringSub (x::xs)= (prElm x) ^ sep ^ (toStringSub xs)
    in  start ^ (toStringSub xs) ^ stop
    end

fun takeUntilWithRest pred [] = ([],[])
  | takeUntilWithRest pred (x::xs) = 
    if pred x then ([x],xs)
    else (fn (ys,zs) => (x::ys,zs)) (takeUntilWithRest pred xs)


fun toStringCommaRound prElm xs = toStringBuilt prElm  ("(",  ",",  ")") xs
fun toStringCommaLnSquare prElm xs = toStringBuilt prElm ("   [ ",  ",\n     ",  " ]\n") xs
fun toStringSpaceEmpty prElm xs = toStringBuilt prElm  ("",  " ",  "") xs

end (* of local *)

end
