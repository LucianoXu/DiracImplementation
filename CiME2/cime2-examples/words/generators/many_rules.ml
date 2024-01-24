print_string "let S = word_signature \"a b\";
let R1 = SRS S \"\n";;

for i = 0 to 100000 do 
  print_string ("(a b)^"^(string_of_int i)^" -> a;\n") done ;;

print_string "\";
let o = length_lex ( word_precedence S \"a<b\" );
let w = word S \"a a\";
let n1 = word_normalize R1 w;\n";;

