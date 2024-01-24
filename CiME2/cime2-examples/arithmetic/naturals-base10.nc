
operators

% constructors

  d : constant
  0,1,2,3,4,5,6,7,8,9 : unary

% operators

  +, * : AC
  mult0,mult1,mult2,mult3,mult4 : unary
  mult5,mult6,mult7,mult8,mult9 : unary

% variables

  x,y : variable

axioms
  0(d) = d ;

  x + d = x ;

  0(x) + 0(y) = 0(x+y) ;
  0(x) + 1(y) = 1(x+y) ;
  0(x) + 2(y) = 2(x+y) ;
  0(x) + 3(y) = 3(x+y) ;
  0(x) + 4(y) = 4(x+y) ;
  0(x) + 5(y) = 5(x+y) ;
  0(x) + 6(y) = 6(x+y) ;
  0(x) + 7(y) = 7(x+y) ;
  0(x) + 8(y) = 8(x+y) ;
  0(x) + 9(y) = 9(x+y) ;

  1(x) + 1(y) = 2(x+y) ;
  1(x) + 2(y) = 3(x+y) ;
  1(x) + 3(y) = 4(x+y) ;
  1(x) + 4(y) = 5(x+y) ;
  1(x) + 5(y) = 6(x+y) ;
  1(x) + 6(y) = 7(x+y) ;
  1(x) + 7(y) = 8(x+y) ;
  1(x) + 8(y) = 9(x+y) ;
  1(x) + 9(y) = 0(x+y+1(d)) ;

  2(x) + 2(y) = 4(x+y) ;
  2(x) + 3(y) = 5(x+y) ;
  2(x) + 4(y) = 6(x+y) ;
  2(x) + 5(y) = 7(x+y) ;
  2(x) + 6(y) = 8(x+y) ;
  2(x) + 7(y) = 9(x+y) ;
  2(x) + 8(y) = 0(x+y+1(d)) ;
  2(x) + 9(y) = 1(x+y+1(d)) ;

  3(x) + 3(y) = 6(x+y) ;
  3(x) + 4(y) = 7(x+y) ;
  3(x) + 5(y) = 8(x+y) ;
  3(x) + 6(y) = 9(x+y) ;
  3(x) + 7(y) = 0(x+y+1(d)) ;
  3(x) + 8(y) = 1(x+y+1(d)) ;
  3(x) + 9(y) = 2(x+y+1(d)) ;

  4(x) + 4(y) = 8(x+y) ;
  4(x) + 5(y) = 9(x+y) ;
  4(x) + 6(y) = 0(x+y+1(d)) ;
  4(x) + 7(y) = 1(x+y+1(d)) ;
  4(x) + 8(y) = 2(x+y+1(d)) ;
  4(x) + 9(y) = 3(x+y+1(d)) ;

  5(x) + 5(y) = 0(x+y+1(d)) ;
  5(x) + 6(y) = 1(x+y+1(d)) ;
  5(x) + 7(y) = 2(x+y+1(d)) ;
  5(x) + 8(y) = 3(x+y+1(d)) ;
  5(x) + 9(y) = 4(x+y+1(d)) ;

  6(x) + 6(y) = 2(x+y+1(d)) ;
  6(x) + 7(y) = 3(x+y+1(d)) ;
  6(x) + 8(y) = 4(x+y+1(d)) ;
  6(x) + 9(y) = 5(x+y+1(d)) ;

  7(x) + 7(y) = 4(x+y+1(d)) ;
  7(x) + 8(y) = 5(x+y+1(d)) ;
  7(x) + 9(y) = 6(x+y+1(d)) ;

  8(x) + 8(y) = 6(x+y+1(d)) ;
  8(x) + 9(y) = 7(x+y+1(d)) ;

  9(x) + 9(y) = 8(x+y+1(d)) ;

  mult0(x) = d ;

  mult1(x) = x ;

  mult2(d) = d ;
  mult2(0(x)) = 0(mult2(x)) ;
  mult2(1(x)) = 2(mult2(x)) ;
  mult2(2(x)) = 4(mult2(x)) ;
  mult2(3(x)) = 1(mult2(x)) ;
  mult2(4(x)) = 8(mult2(x)) ;
  mult2(5(x)) = 0(1(d)+mult2(x)) ;
  mult2(6(x)) = 2(1(d)+mult2(x)) ;
  mult2(7(x)) = 4(1(d)+mult2(x)) ;
  mult2(8(x)) = 6(1(d)+mult2(x)) ;
  mult2(9(x)) = 8(1(d)+mult2(x)) ;

  mult3(d) = d ;
  mult3(0(x)) = 0(mult3(x)) ;
  mult3(1(x)) = 3(mult3(x)) ;
  mult3(2(x)) = 6(mult3(x)) ;
  mult3(3(x)) = 9(mult3(x)) ;
  mult3(4(x)) = 2(1(d)+mult3(x)) ;
  mult3(5(x)) = 5(1(d)+mult3(x)) ;
  mult3(6(x)) = 8(1(d)+mult3(x)) ;
  mult3(7(x)) = 1(2(d)+mult3(x)) ;
  mult3(8(x)) = 4(2(d)+mult3(x)) ;
  mult3(9(x)) = 7(2(d)+mult3(x)) ;

  mult4(d) = d ;
  mult4(0(x)) = 0(mult4(x)) ;
  mult4(1(x)) = 4(mult4(x)) ;
  mult4(2(x)) = 8(mult4(x)) ;
  mult4(3(x)) = 2(1(d)+mult4(x)) ;
  mult4(4(x)) = 6(1(d)+mult4(x)) ;
  mult4(5(x)) = 0(2(d)+mult4(x)) ;
  mult4(6(x)) = 4(2(d)+mult4(x)) ;
  mult4(7(x)) = 8(2(d)+mult4(x)) ;
  mult4(8(x)) = 2(3(d)+mult4(x)) ;
  mult4(9(x)) = 6(3(d)+mult4(x)) ;

  mult5(d) = d ;
  mult5(0(x)) = 0(mult5(x)) ;
  mult5(1(x)) = 5(mult5(x)) ;
  mult5(2(x)) = 0(1(d)+mult5(x)) ;
  mult5(3(x)) = 5(1(d)+mult5(x)) ;
  mult5(4(x)) = 0(2(d)+mult5(x)) ;
  mult5(5(x)) = 5(2(d)+mult5(x)) ;
  mult5(6(x)) = 0(3(d)+mult5(x)) ;
  mult5(7(x)) = 5(3(d)+mult5(x)) ;
  mult5(8(x)) = 0(4(d)+mult5(x)) ;
  mult5(9(x)) = 5(4(d)+mult5(x)) ;

  mult6(d) = d ;
  mult6(0(x)) = 0(mult6(x)) ;
  mult6(1(x)) = 6(mult6(x)) ;
  mult6(2(x)) = 2(1(d)+mult6(x)) ;
  mult6(3(x)) = 8(1(d)+mult6(x)) ;
  mult6(4(x)) = 4(2(d)+mult6(x)) ;
  mult6(5(x)) = 0(3(d)+mult6(x)) ;
  mult6(6(x)) = 6(3(d)+mult6(x)) ;
  mult6(7(x)) = 2(4(d)+mult6(x)) ;
  mult6(8(x)) = 8(4(d)+mult6(x)) ;
  mult6(9(x)) = 4(5(d)+mult6(x)) ;

  mult7(d) = d ;
  mult7(0(x)) = 0(mult7(x)) ;
  mult7(1(x)) = 7(mult7(x)) ;
  mult7(2(x)) = 4(1(d)+mult7(x)) ;
  mult7(3(x)) = 1(2(d)+mult7(x)) ;
  mult7(4(x)) = 8(2(d)+mult7(x)) ;
  mult7(5(x)) = 5(3(d)+mult7(x)) ;
  mult7(6(x)) = 2(4(d)+mult7(x)) ;
  mult7(7(x)) = 9(4(d)+mult7(x)) ;
  mult7(8(x)) = 6(5(d)+mult7(x)) ;
  mult7(9(x)) = 3(6(d)+mult7(x)) ;

  mult8(d) = d ;
  mult8(0(x)) = 0(mult8(x)) ;
  mult8(1(x)) = 8(mult8(x)) ;
  mult8(2(x)) = 6(1(d)+mult8(x)) ;
  mult8(3(x)) = 4(2(d)+mult8(x)) ;
  mult8(4(x)) = 2(3(d)+mult8(x)) ;
  mult8(5(x)) = 0(4(d)+mult8(x)) ;
  mult8(6(x)) = 8(4(d)+mult8(x)) ;
  mult8(7(x)) = 6(5(d)+mult8(x)) ;
  mult8(8(x)) = 4(6(d)+mult8(x)) ;
  mult8(9(x)) = 2(7(d)+mult8(x)) ;

  mult9(d) = d ;
  mult9(0(x)) = 0(mult9(x)) ;
  mult9(1(x)) = 9(mult9(x)) ;
  mult9(2(x)) = 8(1(d)+mult9(x)) ;
  mult9(3(x)) = 7(2(d)+mult9(x)) ;
  mult9(4(x)) = 6(3(d)+mult9(x)) ;
  mult9(5(x)) = 5(4(d)+mult9(x)) ;
  mult9(6(x)) = 4(5(d)+mult9(x)) ;
  mult9(7(x)) = 3(6(d)+mult9(x)) ;
  mult9(8(x)) = 2(7(d)+mult9(x)) ;
  mult9(9(x)) = 1(8(d)+mult9(x)) ;

  x * d = d ;

  0(x) * y = 0(x*y) ;
  1(x) * y = 0(x*y) + y ;
  2(x) * y = 0(x*y) + mult2(y) ;
  3(x) * y = 0(x*y) + mult3(y) ;
  4(x) * y = 0(x*y) + mult4(y) ;
  5(x) * y = 0(x*y) + mult5(y) ;
  6(x) * y = 0(x*y) + mult6(y) ;
  7(x) * y = 0(x*y) + mult7(y) ;
  8(x) * y = 0(x*y) + mult8(y) ;
  9(x) * y = 0(x*y) + mult9(y) ;
  


order

  interactive

problems

  reduce (7(7(d))) * (9(8(d))) ;

end
 
