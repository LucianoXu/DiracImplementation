%***************************************************************************
%
% A presentation of natural numbers
%
%
%***************************************************************************

operators
 
% booleens
  T,F : constant

% entiers unaires

  0 : constant
  s : unary

  1,2,3,4,5,6,7,8,9 : constant

  eq : commutative

  +,. : AC
  ^ : binary
  x,y,z,t : variable

axioms

  0 eq 0 = T;
  0 eq s(x) = F;
  s(x) eq s(y) = x eq y;

  1 = s(0);
  2 = s(1);
  3 = s(2);
  4 = s(3);
  5 = s(4);
  6 = s(5);
  7 = s(6);
  8 = s(7);
  9 = s(8);

  x + 0 = x;
  x + s(y) = s(x+y);

  x.0 = 0;
  x.s(y) = (x.y)+x;

  x^0 = 1;
  x^1 = x;
  1^x = 1;

  (x^y).(x^z) = x^(y+z);
  (x^y)^z = x^(y.z);

order 
  rpo( 9>8>7>6>5>4>3>2>1>s>0,
      . > + > s > 0;
  ^ lrlex)
  % interactive    
      
problems

  eq(x,y) = eq(y,x);
     
end

