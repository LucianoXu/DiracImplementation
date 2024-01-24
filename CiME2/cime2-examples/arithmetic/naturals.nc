
operators

% constructors

  d : constant
  0,1 : unary

% operators

  +, * : AC

% variables

  x,y : variable

axioms
  0(d) = d ;

  x + d = x ;
  0(x) + 0(y) = 0(x+y) ;
  0(x) + 1(y) = 1(x+y) ;
  1(x) + 1(y) = 0(x+y+1(d)) ;
  

  x * d = d ;
  x * 0(y) = 0(x*y) ;
  x * 1(y) = (0(x*y)) + x ;

order

  lexico(
    poly( [d] = 2; 
          [0](x) = x; 
          [1](x) = x+1; 
          [+](x,y) = x+y-2; 
          [*](x,y) = x.y );
    poly( [d] = 2; 
          [0](x) = x+1; 
          [1](x) = x+1; 
          [+](x,y) = x+y;
          [*](x,y) = x.y )
  )


problems

  reduce (1(1(1(d)))) * (1(1(d))) ;

end
 
Result:
{ [1] 0(d) -> d,
  [2] x+d -> x,
  [3] x*d -> d,
  [4] x*0(y) -> 0(x*y),
  [5] 0(x)+0(y) -> 0(x+y),
  [6] 0(x)+1(y) -> 1(x+y),
  [7] x*1(y) -> x+0(x*y),
  [8] 1(x)+1(y) -> 0(x+y+1(d)) } (8 rules)

Number of calls to AC matching      : 1542
Number of successful calls          : 102 (6%)
Number of calls to unification      : 39
Number of unifiers generated        : 75 (1.92 average)
Number of critical pairs considered : 52 (69%)
Number of rules produced            : 8
Number of rules retained            : 8

      times       |   user   |  system  |  total 
------------------+----------+----------+----------
Total times       |    1.490 |    0.720 |    2.210 
Unification times |    0.200 |    0.000 |    0.200 
Matching times    |    0.840 |    0.290 |    1.130 
Poly times        |    0.020 |    0.000 |    0.020 

