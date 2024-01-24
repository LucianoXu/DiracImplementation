let F = signature "
     # : constant;
     0,1,j : postfix unary;
     opp : unary;
     - : infix binary;
     +,* : AC;
     abs : unary ;
     test_abs_pos, test_abs_neg : binary;
     signe, test_signe_pos, test_signe_neg : unary;
     min,min',min'' : binary ;
     test_min_pos, test_min_neg : 3 ;
     f : binary ;
     rat, irred : binary ;
     +_Q : infix commutative ;
     *_Q : infix commutative ;
";

let X = vars "x y";

let rat = "
     (#)0 -> #;
     # + x -> x;
     (x)0 + (y)0 -> (x+y)0;
     (x)0 + (y)1 -> (x+y)1;
     (x)0 + (y)j -> (x+y)j;
     (x)1 + (y)1 -> (x+y+(#)1)j;
     (x)j + (y)j -> (x+y+(#)j)1;
     (x)1 + (y)j -> (x+y)0;
     opp(#) -> # ;
     opp((x)0) -> (opp(x))0 ;
     opp((x)1) -> (opp(x))j ;
     opp((x)j) -> (opp(x))1 ;
     x - y -> x+opp(y) ;
     # * x -> #;
     (x)0 * y -> (x*y)0;
     (x)1 * y -> (x*y)0 + y;
     (x)j * y -> (x*y)0 - y;
     abs(x) -> test_abs_pos(x,x);
  test_abs_pos(#,x) -> x;
  test_abs_pos((x)0,y) -> test_abs_pos(x,y);
  test_abs_pos((x)1,y) -> test_abs_pos(x,y);
  test_abs_pos((x)j,y) -> test_abs_neg(x,y);
  test_abs_neg(#,x) -> opp(x);
  test_abs_neg((x)0,y) -> test_abs_neg(x,y);
  test_abs_neg((x)1,y) -> test_abs_pos(x,y);
  test_abs_neg((x)j,y) -> test_abs_neg(x,y);
  signe(#) -> #;
  signe((x)0) -> signe(x);
  signe((x)1) -> test_signe_pos(x);
  signe((x)j) -> test_signe_neg(x);
  test_signe_pos(#) -> (#)1;
  test_signe_pos((x)0) -> test_signe_pos(x);
  test_signe_pos((x)1) -> test_signe_pos(x);
  test_signe_pos((x)j) -> test_signe_neg(x);
  test_signe_neg(#) -> (#)j;
  test_signe_neg((x)0) -> test_signe_neg(x);
  test_signe_neg((x)1) -> test_signe_pos(x);
  test_signe_neg((x)j) -> test_signe_neg(x);
  min(x,y) -> test_min_pos(abs(y)-abs(x),x,y);
  min'(x,y) -> test_min_pos(abs((y)1)-abs((x)1),x,y);
  min''(x,y) -> test_min_pos(abs((y)j)-abs((x)j),x,y);
  test_min_pos(#,x,y) -> x;
  test_min_pos((x)0,y,z) -> test_min_pos(x,y,z);
  test_min_pos((x)1,y,z) -> test_min_pos(x,y,z);
  test_min_pos((x)j,y,z) -> test_min_neg(x,y,z);
  test_min_neg(#,x,y) -> y;
  test_min_neg((x)0,y,z) -> test_min_neg(x,y,z);
  test_min_neg((x)1,y,z) -> test_min_pos(x,y,z);
  test_min_neg((x)j,y,z) -> test_min_neg(x,y,z);
  f(#,x) -> #;
  f(x,#) -> signe(x);
  f((x)0,(y)0) -> f(x,y);
  f((x)0,(y)1) -> (f(x,(y)1))0;
  f((x)0,(y)j) -> (f(x,(y)j))0;
  f((x)1,(y)0) -> f((x)1,y);
  f((x)1,(y)1) ->
    (f(x - min'(x,y), (y)1))0 + f(min((x)1,(y)1), x - y);
  f((x)1,(y)j) -> 
    (f(x + min''(opp(x),y), (y)j))0 + f(min((x)1,(opp(y))1), x + y);
  f((x)j,(y)0) -> f((x)j,y);
  f((x)j,(y)1) ->
    (f(x + min'(opp(x),y), (y)1))0 + f(min((x)j,(opp(y))j), x + y);
  f((x)j,(y)j) ->
    (f(x - min''(x,y), (y)j))0 + f(min((x)j,(y)j), x - y);
  rat(x,y) -> irred(signe(y)*f(x,y),signe(y)*f(y,x));
  irred(x,y) +_Q irred(u,v) -> irred((x*v) + (u*y),y*v);
  irred(x,y) *_Q irred(u,v) -> rat(x*u,y*v);
";


