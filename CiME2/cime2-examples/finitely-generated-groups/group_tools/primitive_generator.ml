(* Computation of a primitive generator of $(Z/nZ)*$ with $n=p^\nu$ *)
(* and $p>2$ a prime number. *) 

(* Redefinition of a small part of Set stdlib to provide add_if_not_present.*)
module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module Make(Ord: OrderedType) =
  struct
    type elt = Ord.t
    type t = Empty | Node of t * elt * t * int

    (* Sets are represented by balanced binary trees (the heights of the
       children differ by at most 2 *)

    let height = function
        Empty -> 0
      | Node(_, _, _, h) -> h

    (* Creates a new node with left son l, value x and right son r.
       l and r must be balanced and | height l - height r | <= 2.
       Inline expansion of height for better speed. *)

    let create l x r =
      let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
      Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

    (* Same as create, but performs one step of rebalancing if necessary.
       Assumes l and r balanced.
       Inline expansion of create for better speed in the most frequent case
       where no rebalancing is required. *)

    let bal l x r =
      let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Set.bal"
        | Node(ll, lv, lr, _) ->
            if height ll >= height lr then
              create ll lv (create lr x r)
            else begin
              match lr with
                Empty -> invalid_arg "Set.bal"
              | Node(lrl, lrv, lrr, _)->
                  create (create ll lv lrl) lrv (create lrr x r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Set.bal"
        | Node(rl, rv, rr, _) ->
            if height rr >= height rl then
              create (create l x rl) rv rr
            else begin
              match rl with
                Empty -> invalid_arg "Set.bal"
              | Node(rll, rlv, rlr, _) ->
                  create (create l x rll) rlv (create rlr rv rr)
            end
      end else
        Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

    (* Implementation of the set operations *)

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec mem x = function
        Empty -> false
      | Node(l, v, r, _) ->
          let c = Ord.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec add x = function
        Empty -> Node(Empty, x, Empty, 1)
      | Node(l, v, r, _) as t ->
          let c = Ord.compare x v in
          if c = 0 then t else
          if c < 0 then bal (add x l) v r else bal l v (add x r)

(* Same as add but if the element is present then raises [Present s]
    where [s] is the considered set.*) 
    exception Present of t 
    let add_if_not_present x tot = 
      let rec add_if_not_present_rec = function
          Empty -> Node(Empty, x, Empty, 1)
	| Node(l, v, r, _) as t ->
            let c = Ord.compare x v in
              if c = 0 then raise (Present tot) else
          if c < 0 then bal (add_if_not_present_rec l) v r 
	  else bal l v (add_if_not_present_rec r) in
	add_if_not_present_rec tot

    let rec iter f = function
        Empty -> ()
      | Node(l, v, r, _) -> iter f l; f v; iter f r

    let rec cardinal = function
        Empty -> 0
      | Node(l, v, r, _) -> cardinal l + 1 + cardinal r

  end

module IntSet = Make(struct type t = int let compare = compare end)

let print_intset s = 
  IntSet.iter (function x -> Printf.printf " %i ;" x) s

let rec puissance x = function
    0 -> 1
  | 1 -> x 
  | 2 -> x*x
  | n -> 
      let y = (puissance x (n/2)) in
	if (n mod 2)=0 
	then  y*y
	else  x*y*y

let rec puissance_mod m x = function
    0 -> 1
  | 1 -> x mod m
  | 2 -> ((x mod m)*(x mod m)) mod m
  | n -> 
      let y = (puissance_mod m x (n/2)) in
	if (n mod 2)=0 
	then  ((y mod m)*(y mod m)) mod m
	else  ((x mod m)*(y mod m)*(y mod m)) mod m


(* Computes the set of inversible elements in Z/p^nuZ. Unused.*)
let inversible_group p nu =
  let is_inversible x = (x mod p)<>0 in
  let rec build_inv = function 
      (0,accs) -> accs
    | (elt,accs) -> 
        if (is_inversible elt) then 
          build_inv (elt-1, IntSet.add elt accs)
        else
          build_inv (elt-1, accs)
  in 
    build_inv (puissance p nu, IntSet.empty)

(* Computes the orbite of an inversible integer x in the group Z/nZ *)
(* whith p^nu=n and p a prime number. If x is not inversible an empty *)
(* set is returned.*)
let orbite x p nu n = 

  if  (x mod p)<>0 then 
      let rec inter_orbit (acc,accs) =
	let next_puiss = (x*acc) mod n in
	    inter_orbit (next_puiss,IntSet.add_if_not_present next_puiss accs)
      in 
	try 
	  inter_orbit (1,IntSet.empty)
	with
	    IntSet.Present accs -> accs
    else IntSet.empty 


exception Primitive of int
exception Bad_group

(* Returns the smallest primitive generator of $Z/p^nuZ$ whith $inv\_card$ *)
(* the cardinal of the group of inversible elements and $card=p^nu$ *) 
let find_primitive_generator p nu inv_card card =
  try
    for elt=1 to card 
    do 
      if (IntSet.cardinal (orbite elt p nu card))=inv_card then raise (Primitive elt)
    done;   
 raise Bad_group
  with
      (Primitive elt) -> elt

let apply_symbol s t = s::t

let rec iter_apply_symbol s t n = match n with 
    0 -> t
  | n -> apply_symbol s (iter_apply_symbol s t (n-1))

let rec apply_symbol_list slist t = 
  match slist with 
      [] -> t
    | s::r -> apply_symbol s (apply_symbol_list r t)

let rec iter_symbol_list slist leaf = function 
    0 ->  leaf
  | n -> apply_symbol_list slist (iter_symbol_list slist leaf (n-1))

(* Gives the unique minimal non negative representant of x mod n.*)
let normalize_int_modulo x n = (x mod n + 2*n) mod n

let rec repeat_symbol_in_list eol s = function
    0 -> eol
  | n -> s::(repeat_symbol_in_list eol s (n-1))

let print_rule (l,r) = 
  List.iter (function x -> print_string x ; print_string " ") l;
  print_string "-> ";
  List.iter (function x -> print_string x ; print_string " ") r;
  print_string ";"

let print_all_rules l = 
  List.iter (function x -> print_rule x ; print_newline ()) l

let main () =
  let p = int_of_string (Sys.argv.(1)) in
  let nu = int_of_string (Sys.argv.(2)) in
  let cardinal = puissance p nu in
  let _ = Printf.printf "(* Cardinal of the group: %i\n" cardinal in
  let inversible_group_cardinal = (puissance p (nu-1))*(p-1) in
  let _ = Printf.printf " Cardinal of the group of inversibles: %i\n"
	    inversible_group_cardinal; flush stdout in 

  let primitive_generator = find_primitive_generator p nu 
			      inversible_group_cardinal cardinal in 
  let _ = Printf.printf " A primitive generator is: %i *)\n" primitive_generator
  in
  let kleins = [(["S";"S";"S";"S"],[]);(["S";"S";"T"],["T";"S";"S"]);
		(["S";"T";"S";"T";"S";"T"],["S";"S"])] in
  let p_kleins = [(["S";"S"],[]);(["S";"T";"S";"T";"S";"T"],[])] in
  let idempotent = ((iter_symbol_list ["T"] [] cardinal),[]) in
  let _ = print_string "\n(* Now the Ha relations*)\n" in
  let inv_primitive_generator = 
    puissance_mod cardinal primitive_generator (inversible_group_cardinal-1) in
  let opp_primitive_generator = 
    normalize_int_modulo (-primitive_generator) cardinal in
  let square_primitive_generator = 
    normalize_int_modulo (primitive_generator * primitive_generator) cardinal in
  let inv_square_primitive_generator =
    normalize_int_modulo (inv_primitive_generator * inv_primitive_generator) cardinal in
  let inv_opp_primitive_generator =
    normalize_int_modulo (-inv_primitive_generator) cardinal in
  let h_primitive_generator =  
    "S"::"S"::(repeat_symbol_in_list 
    ("S"::(repeat_symbol_in_list 
      ("S"::(repeat_symbol_in_list ["S"] "T" primitive_generator))
      "T" inv_primitive_generator))
      "T" primitive_generator) in
  let h_inv_primitive_generator =
    "S"::"S"::(repeat_symbol_in_list 
    ("S"::(repeat_symbol_in_list 
      ("S"::(repeat_symbol_in_list ["S"] "T" inv_primitive_generator))
      "T" primitive_generator))
      "T" inv_primitive_generator) in 
  let h_square_primitive_generator =  
    "S"::"S"::(repeat_symbol_in_list 
    ("S"::(repeat_symbol_in_list 
      ("S"::(repeat_symbol_in_list ["S"] "T" square_primitive_generator))
      "T" inv_square_primitive_generator))
      "T" square_primitive_generator) in
  let h_opp_primitive_generator =
  "S"::"S"::(repeat_symbol_in_list 
    ("S"::(repeat_symbol_in_list 
      ("S"::(repeat_symbol_in_list ["S"] "T" opp_primitive_generator))
      "T" inv_opp_primitive_generator))
      "T" opp_primitive_generator) in
  let r1 = 
    (h_primitive_generator @ ["T"]), 
    (iter_apply_symbol
       "T"
       (apply_symbol_list h_primitive_generator [])
       square_primitive_generator) 
  in
  let r2 = 
    h_primitive_generator @ ["S"] ,
    ( apply_symbol_list ("S"::h_inv_primitive_generator) [] ) 
  in
  let r3 = h_primitive_generator,h_opp_primitive_generator in
  let myname = "psl2z_p" ^ (Sys.argv.(1)) ^"_nu"^ (Sys.argv.(2)) in
    print_string "let F = word_signature \"S T\";\n";
    let _ = print_string 
	      "let order = multi_lex (word_precedence F \"S > T\");\n" in
    print_string ("let "^myname^" = SRS F \"\n ");
    print_all_rules p_kleins; (* or kleins *)
    print_rule idempotent ;
    print_newline();
    print_all_rules [r1;r2;r3];
    print_string "\";\n#time on ;\n";
    print_string 
      ("let completed_"^myname^" = word_completion order "^myname^" ;\n");
    print_string ("let order_of_completed_"^myname^" = word_counter completed_"^myname^" ;\n");
    print_string "#mem;\n"

let _ = 
try
    main ()
with      
    Invalid_argument("Array.get") -> print_string "Syntax error:\n\t primitive_generator p nu\n\t computes a primitive generator for (Z/(p^nu)Z)*.\n"   
  | Bad_group -> print_string "This group does not have a primitive generator. \nCheck that p is a prime number greater than 2.\n"
  | exc -> Printf.printf "Fatal error detected.\n Please mail to monate@lri.fr and report the error : %s\n" (Printexc.to_string exc )


let _ = flush stdout


