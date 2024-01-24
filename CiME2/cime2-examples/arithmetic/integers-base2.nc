
operators

% constructors

  d : constant
  0,1 : unary

  P,M : constant

  int : binary

% operators

  +, * : AC

  ++, ** : AC
  -- : binary

% variables

  x,y : variable

axioms
  0(d) = d ;
  
  int(M,d) = int(P,d) ;

  x + d = x ;
  0(x) + 0(y) = 0(x+y) ;
  0(x) + 1(y) = 1(x+y) ;
  1(x) + 1(y) = 0(x+y+1(d)) ;
  
  int(P,x) ++ int(P,y) = int(P,x+y) ;
  int(M,x) ++ int(M,y) = int(M,x+y) ;
  int(P,x) ++ int(M,y) = sub(x,y) ;
  
  sub(x,d) = int(P,x) ;
  sub(d,x) = int(M,x) ;

  sub(0(x),0(y)) = 
  x * d = d ;
  x * 0(y) = 0(x*y) ;
  x * 1(y) = (0(x*y)) + x ;

order

  interactive

problems

% 89 * 77, ca doit donner 1(0(1(0(0(0(1(1(0(1(0(1(1(d)))))=6853

  reduce (1(0(0(1(1(0(1(d)))))))) * (1(0(1(1(0(0(1(d)))))))) ;

end
 
