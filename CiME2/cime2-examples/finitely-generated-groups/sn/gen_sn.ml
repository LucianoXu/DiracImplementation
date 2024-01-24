open Format
open Sys

let _ =
  try 
    let n = int_of_string argv.(1) in
    printf "(* $S_%d$ equational presentation *)\n\n" n;
    printf "let F = word_signature \"";
    for i = 1 to (n-1) do
      printf "a%d " i
    done;
    printf "\";\n";
    printf "let o = multi_lex (word_precedence F \n\"";
    for i = 1 to (n-2) do
      printf "a%d<" i
    done;
    printf "a%d\");\n" (n-1);
    printf "let R = SRS F \"\n";
    for i = 1 to (n-1) do
      printf "a%d ^ 2 -> ;\n" i
    done;
    for i = 1 to (n-2) do
      printf "(a%d a%d) ^ 3 -> ;\n" i (i+1)
    done;
    for j = 3 to (n-1) do
      for i = 1 to (j-2) do
	printf "a%d a%d -> a%d a%d ;\n"  i j j i
      done
    done;
    printf "\";\n#time;\nlet S%d = word_completion o R ;
#mem;
let n = word_counter S%d;
#mem;\n" n n;
  with
      _ -> printf 
	  "Usage : gen_sn <n> generates a CiME2 file for the group Sn\n"
