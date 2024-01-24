

let rec stream_filter filter = parser l 
    [< 'p ; q >] -> if (filter p) then [< 'p ; stream_filter filter q >] 
    else stream_filter filter q
  | [<>] -> [<>]

let rec q_is_a_power_of_p p q = 
  if q mod p = 0 then q_is_a_power_of_p p (q/p)
  else q = 1


let rec eras = parser l
    [< 'p ; q >] -> 
      [< 'p ; eras (stream_filter 
		      (fun q -> (q mod p <> 0) or (q_is_a_power_of_p p q)) q) 
      >]
  | [<>] -> [<>]
;;


let rec integers = function 
  | 1 | 0 | 2 -> [< '2 >]
  | i -> [< integers (i - 1) ; 'i >] 



let print_primes n = 
  let i = integers n in
  let p = eras i in
    try
      while true do
	Format.printf "%d\n" (Stream.next p);
	flush stdout
      done
    with Stream.Failure -> ()


let _ = 
  try 
    print_primes (int_of_string (Sys.argv.(1)))
  with 
      _ -> Format.printf "usage : [prime_number n] gives the primes and th powers of primes less than n.\n"
