
operators

% constructors

  b : constant
  0,1 : postfix unary

% operators

  +, * : AC

% variables

  x,y : variable

axioms
  (b)0 = b ;

  x + b = x ;
  (x)0 + (y)0 = (x+y)0 ;
  (x)0 + (y)1 = (x+y)1 ;
  (x)1 + (y)1 = (x+y+(b)1)0 ;
  
  x * b = b ;
  x * (y)0 = (x*y)0 ;
  x * (y)1 = ((x*y)0) + x ;

order
lexico(
  poly(
[b] = 2 ;
[0](x) = x ;
[1](x) = x + 1 ;
[+](x,y) = x + y - 1;
[*](x,y) = x.y);
  poly(
[b] = 2 ;
[0](x) = x + 1 ;
[1](x) = x + 1 ;
[+](x,y) = x + y ;
[*](x,y) = x.y);
interactive)

problems

% 89 = b1011001
% 77 = b1001101
% 89 * 77, ca doit donner 6853= b1101011000101

  reduce ((((((((b)1)0)1)1)0)0)1) * ((((((((b)1)0)0)1)1)0)1) ;

% pb de Christophe Raffalli : a-t-on 1001 * 1000 = 1000*1001
% 1000 = b1111101000
% 1001 = b1111101001

  (((((((((((b)1)1)1)1)1)0)1)0)0)0) * 
  (((((((((((b)1)1)1)1)1)0)1)0)0)1) =
  (((((((((((b)1)1)1)1)1)0)1)0)0)1) * 
  (((((((((((b)1)1)1)1)1)0)1)0)0)0) ;

end
 
