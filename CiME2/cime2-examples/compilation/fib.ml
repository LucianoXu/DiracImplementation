
type term = 
    ZERO
  | S of term
  | Plus of term * term
  | F of term
  | Normal of term
  | Not_a_term
  | NIL

let rec print_term  = function 
       ZERO -> print_string "0"
  | S(x) -> print_string "S("; print_term x ; print_string ")" 
  | Plus(x,y) -> (print_term x) ; (print_string "+");  print_term y 
  | F(x) -> print_string "F("; print_term x ; print_string ")" 
  | Normal(x) -> print_string "Normal("; print_term x ; print_string ")" 
  | Not_a_term -> print_string "NAT"
  | NIL -> print_string "NIL"



let try_kill t = 
  try Thread.kill t 
  with _ -> ()

let counter = ref(0)


exception Nf

let s_x = function x -> S x
let id = function x -> x
let one = function _ -> S ZERO

let rewrite_opt t =  
  match t with
    Plus (ZERO,x) -> (function y->x),Normal(Not_a_term) 
  | Plus (S(x),y) -> s_x,Plus(Normal(x),Normal(y))
  | F (ZERO) -> one,Normal(Not_a_term)
  | F (S(ZERO)) -> one,Normal(Not_a_term)
  | F (S(S(x))) -> id,Plus(F(Normal(S(x))),F(Normal(x)))
  | _ -> raise Nf


let rewrite t =  
  incr counter ;
  match t with
    Plus (ZERO,x) -> x 
  | Plus (S(x),y) -> S( Plus(x,y))
  | F (ZERO) -> (S ZERO)
  | F (S(ZERO)) -> (S ZERO)
  | F (S(S(x))) -> Plus(F(S(x)),F(x))
  | _ -> raise Nf



(* No optimization at all *)
let rec normalize = function 
    ZERO -> (* irreducible *) 
  begin try let
  r_ZERO = rewrite ZERO in normalize r_ZERO with Nf
  -> ZERO 
  end

  | S x -> (* ground irreducible *)
	(let x' = normalize x in
	  try
	    let r_S_x' = rewrite (S x') in
	      normalize r_S_x'
	  with Nf -> S x'
	)
  | Plus (x,y) ->
      begin
	let x' = normalize x 
	and y' = normalize y in
	  try
	    let red_term = rewrite (Plus (x',y')) in
	      (normalize red_term)
	  with Nf -> Plus (x',y')
      end
  | F x ->
      begin
	let x' = normalize x in
	  try
	    let red_term = rewrite (F x') in
	      (normalize red_term)
	  with Nf -> F x'
      end
  | _ -> assert false


let global_cache = Cache.create 100000


let cache_hit = ref(1)
let cache_miss = ref(1)
let print_cache_stat () = Printf.printf "Hit=%i/Miss=%i (Hit rate = %i%%)\n" !cache_hit !cache_miss (!cache_hit * 100  / (!cache_miss + !cache_hit)) 
let rewrite_counter = ref(0)
let rewriting_counter = ref (0)
(* Well optimized *)

let rec normalize_opt t = 
  let res = ref(NIL) in 

  let in_cache = Thread.create 
			(function t -> 
			   let result=Cache.find t global_cache  in
			      incr rewrite_counter ;res:=result )
			t  
  and 
    rewriting in_cache = 
    Thread.create (function t -> 
		     let new_nf = 
		       match t with   
			   ZERO -> (* irreducible *) 
			     (try_kill in_cache; res:=ZERO;incr rewriting_counter)
			 | S x -> (* ground irreducible *)
			       let x' = normalize_opt x in
				 (try_kill in_cache; res:=S(x');incr rewriting_counter)
			 | Plus (x,y) ->
			     begin
			       let x' = normalize_opt x 
			       and y' = normalize_opt y in
				 try
				   let nf_context,red_term = rewrite_opt (Plus (x',y')) in
				   let nf_subst = (normalize_opt red_term) in
				       (try_kill in_cache; res:= nf_context nf_subst;incr rewriting_counter)
				 with Nf -> (try_kill in_cache ; res:= Plus (x',y');incr rewriting_counter)
			     end
			 | F x ->
			     begin
			       let x' = normalize_opt x in
				   try
				     let nf_context,red_term = rewrite_opt (F x') in
				     let nf_subst = normalize_opt red_term in
				       (try_kill in_cache; res:= nf_context nf_subst;incr rewriting_counter)
				   with Nf -> (try_kill in_cache; res:=F x';incr rewriting_counter)
			     end
			 | Normal(x) -> (try_kill in_cache; res:=x;incr rewriting_counter)
			 | Not_a_term -> print_string "CANNOT" ; assert false		       
		     in
		       begin
			 Cache.add t  !res global_cache  ;
			 incr cache_miss;
			 new_nf
			 end
		  ) t 
  in 
  let t_1 = in_cache in  
  let t_2 = rewriting t_1 in 
    Thread.join t_1;
    Thread.join t_2;
    !res
      
      
let rec int_to_peano = function
    0 -> ZERO
  | n -> S (int_to_peano (pred n))

let rec peano_to_int = function
    ZERO -> 0
  | S(x) -> succ (peano_to_int x)
  | t -> print_term t ; assert false


let rec fib = function
    0 -> 1
  | 1 -> 1
  | n -> (fib (pred n)) + (fib (pred (pred n)))

let fib' n =
  let p_n = int_to_peano n in
  let f_p_n = normalize (F p_n) in
    peano_to_int f_p_n;;

let fib'_opt n =
  let p_n = int_to_peano n in
  let f_p_n = normalize_opt (F p_n) in
    peano_to_int f_p_n


let time f x =
  let time_before = Unix.times ()
  in
  let show_time () =
    let time_after = Unix.times ()
    in
      print_string "Execution time: ";
      print_float (time_after.Unix.tms_utime -. time_before.Unix.tms_utime);
      print_string " sec.";
      print_newline()
  in
    try
      let res = f x
      in show_time();res
    with e -> show_time();raise e      
;;


let x = time fib  10 in
let y = time fib'_opt 10 in
  print_cache_stat ();
  print_int y;
  print_newline ();
  print_int x;
  print_newline ()





